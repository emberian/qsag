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

use crate::inventory::HdError;
use qsag_asm::wipe::{SecretBuffer, SecretBytes, SecretWipe, wipe};

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
/// Default maximum derivation depth $D_{\max} = 8$.
/// Each non-hardened child step adds an independent public $\text{CBD}_2$ vector
/// ($\|\Delta s_i\|_\infty \le 2$) to $(s_1, s_2)$, so after depth $D$ from a $\text{CBD}_2$
/// root the secret's worst-case $\ell_\infty$ norm grows to $2(D + 1)$ (`18` at $D = 8$).
/// Keeping $D_{\max} \le 8$ by default (and hard-capping `max_depth <= 16`) prevents unbounded
/// norm accumulation if callers compose derived shares with fixed-$\beta$ lattice protocols.
pub const DEFAULT_MAX_DERIVATION_DEPTH: u16 = 8;
/// Hard upper cap on `max_depth` accepted during linear-module provisioning (`||s||_inf <= 34`
/// for non-hardened $\text{CBD}_2$ chains from a single $\text{CBD}_2$ secret).
pub const MAX_NON_HARDENED_DERIVATION_DEPTH: u16 = 16;

/// Worst-case $\ell_\infty$ coefficient bound $2 \cdot (d + 1)$ after `depth` non-hardened
/// $\text{CBD}_2$ derivation steps from a single $\text{CBD}_2$ root secret.
#[inline]
pub const fn max_cbd2_linf_norm_after_depth(depth: u16) -> u32 {
    (depth as u32 + 1) * 2
}

/// Barrett reduction for every u64 input. With mu=floor(2^64/q), the
/// quotient estimate is at most one below floor(x/q), so r is below 2q.
/// The correction mask is kept opaque to the optimizer; audit the final image.
#[inline]
pub fn ct_reduce_mod_q_u64(x: u64) -> u32 {
    const MU: u128 = (1u128 << 64) / MODULE_Q as u128;
    let quotient = ((x as u128 * MU) >> 64) as u64;
    let r = x - quotient * MODULE_Q as u64;
    let mask = core::hint::black_box(!qsag_accel::ct::ct_lt_mask_u64(r, MODULE_Q as u64));
    (r.wrapping_sub((MODULE_Q as u64) & mask)) as u32
}

#[inline]
const fn const_reduce_mod_q_u64(x: u64) -> u32 {
    const MU: u128 = (1u128 << 64) / MODULE_Q as u128;
    let quotient = ((x as u128 * MU) >> 64) as u64;
    let r = x - quotient * MODULE_Q as u64;
    let over = !ct_lt_u64(r, MODULE_Q as u64);
    ct_select_u64(over, r.wrapping_sub(MODULE_Q as u64), r) as u32
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
    let a_c = const_reduce_mod_q_u64(a as u64) as u64;
    let b_c = const_reduce_mod_q_u64(b as u64) as u64;
    let s = a_c + b_c;
    let over = !ct_lt_u64(s, MODULE_Q as u64);
    ct_select_u64(over, s.wrapping_sub(MODULE_Q as u64), s) as u32
}

#[inline]
pub const fn mod_q_sub(a: u32, b: u32) -> u32 {
    let a_c = const_reduce_mod_q_u64(a as u64) as u64;
    let b_c = const_reduce_mod_q_u64(b as u64) as u64;
    let lt = ct_lt_u64(a_c, b_c);
    let diff = a_c.wrapping_sub(b_c);
    ct_select_u64(lt, diff.wrapping_add(MODULE_Q as u64), diff) as u32
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
#[derive(Clone, Eq)]
pub struct RingPoly {
    pub coeffs: [u32; MODULE_N],
}

impl PartialEq for RingPoly {
    fn eq(&self, other: &Self) -> bool {
        let mut diff = 0u32;
        for (a, b) in self.coeffs.iter().zip(other.coeffs.iter()) {
            diff |= a ^ b;
        }
        core::hint::black_box(diff) == 0
    }
}

impl SecretWipe for RingPoly {
    fn secret_wipe(&mut self) {
        wipe(&mut self.coeffs);
    }
}

impl Drop for RingPoly {
    fn drop(&mut self) {
        self.secret_wipe();
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
        let mut out = Self::zero();
        for (i, value) in out.coeffs.iter_mut().enumerate() {
            *value = mod_q_add(self.coeffs[i], rhs.coeffs[i]);
        }
        out
    }

    pub fn sub(&self, rhs: &Self) -> Self {
        let mut out = Self::zero();
        for (i, value) in out.coeffs.iter_mut().enumerate() {
            *value = mod_q_sub(self.coeffs[i], rhs.coeffs[i]);
        }
        out
    }

    pub fn scale(&self, scalar: u32) -> Self {
        let s = ct_reduce_mod_q_u64(scalar as u64);
        let mut out = Self::zero();
        for (i, value) in out.coeffs.iter_mut().enumerate() {
            *value = mod_q_mul(self.coeffs[i], s);
        }
        out
    }

    /// Fixed-schedule NTT multiplication modulo X^256+1.
    pub fn mul_negacyclic(&self, rhs: &Self) -> Self {
        let left = forward(self);
        let right = forward(rhs);
        let mut product = Self::zero();
        qsag_asm::mldsa_pointwise_mul(&mut product.coeffs, &left.coeffs, &right.coeffs);
        inverse(product)
    }

    /// Exact integer squared Euclidean norm $\sum_{m=0}^{255} c_m^2$ of centered representatives
    /// in $[-(q-1)/2, (q-1)/2]$ (`0` floating-point instructions!). Non-canonical coefficients
    /// are reduced modulo `MODULE_Q` in constant time before centering so public callers can
    /// never trigger subtraction underflow.
    pub fn centered_l2_norm_sq(&self) -> u64 {
        let half_q = (MODULE_Q / 2) as u64;
        let mut sum_sq = 0u64;
        for &c in &self.coeffs {
            let c64 = ct_reduce_mod_q_u64(c as u64) as u64;
            let gt_half = ct_lt_u64(half_q, c64);
            let abs_val = ct_select_u64(gt_half, (MODULE_Q as u64).wrapping_sub(c64), c64);
            sum_sq = sum_sq.saturating_add(abs_val * abs_val);
        }
        sum_sq
    }

    /// Sample a short centered-binomial polynomial $\text{CBD}_2$ (`[-2, 2]`) in 100% constant time
    /// via bit-popcount difference (`0` floats, `0` divisions, `0` rejection branches!).
    pub fn sample_cbd2_ct(domain: &[u8], seed: &[u8], tag_idx: u32) -> Self {
        let idx_be = tag_idx.to_be_bytes();
        let mut buf = SecretBuffer([0u8; 128]);
        cshake256_framed_xof(domain, &[seed, &idx_be], &mut buf[..]);
        let mut out = Self::zero();
        for (i, &byte) in buf.iter().enumerate() {
            // Two coefficients per byte (`4` bits each: `a0 + a1 - b0 - b1` in `[-2, 2]`).
            let lo = byte & 0x0F;
            let hi = byte >> 4;
            let pos_lo = ((lo & 1) + ((lo >> 1) & 1)) as u32;
            let neg_lo = (((lo >> 2) & 1) + ((lo >> 3) & 1)) as u32;
            let pos_hi = ((hi & 1) + ((hi >> 1) & 1)) as u32;
            let neg_hi = (((hi >> 2) & 1) + ((hi >> 3) & 1)) as u32;
            out.coeffs[2 * i] = mod_q_sub(pos_lo, neg_lo);
            out.coeffs[2 * i + 1] = mod_q_sub(pos_hi, neg_hi);
        }
        out
    }

    /// Fixed-work 192-bit reduction. Per coefficient TV distance is below q/2^192.
    /// There is no secret-dependent retry loop or division in the reduction.
    pub fn sample_uniform_mod_q(domain: &[u8], seed: &[u8], tag_idx: u32) -> Self {
        let mut buf = SecretBuffer([0u8; MODULE_N * 24]);
        cshake256_framed_xof(domain, &[seed, &tag_idx.to_be_bytes()], &mut buf[..]);
        let mut out = Self::zero();
        for (coeff, wide) in out.coeffs.iter_mut().zip(buf.as_chunks::<24>().0) {
            *coeff = reduce_wide_mod_q(wide);
        }
        out
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(MODULE_N * 4);
        for &c in &self.coeffs {
            out.extend_from_slice(&c.to_le_bytes());
        }
        out
    }
}

/// Secret `RingPoly` with no public accessor and `<REDACTED>` in `Debug`; the
/// inner polynomial erases itself on drop.
pub struct SecretRingPoly(RingPoly);

impl SecretRingPoly {
    pub const fn new(poly: RingPoly) -> Self {
        Self(poly)
    }

    /// Crate-internal: the coefficients never leave the protocol modules.
    /// ```compile_fail
    /// fn leak(secret: &qsag_hd::SecretRingPoly) -> qsag_hd::RingPoly {
    ///     secret.expose().clone()
    /// }
    /// ```
    pub(crate) const fn expose(&self) -> &RingPoly {
        &self.0
    }
}

impl fmt::Debug for SecretRingPoly {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("SecretRingPoly(<REDACTED>)")
    }
}

impl SecretWipe for SecretRingPoly {
    fn secret_wipe(&mut self) {
        self.0.secret_wipe();
    }
}

/// Reduction of a big-endian integer of any public length, one fixed Horner
/// step per 32-bit word (per byte for a leading remainder). Each intermediate
/// fits in u64 because the preceding remainder is below q.
fn reduce_wide_mod_q(bytes: &[u8]) -> u32 {
    let (head, words) = bytes.as_rchunks::<4>();
    let mut r = 0u32;
    for &byte in head {
        r = ct_reduce_mod_q_u64((r as u64) * 256 + u64::from(byte));
    }
    for word in words {
        r = ct_reduce_mod_q_u64(((r as u64) << 32) | u64::from(u32::from_be_bytes(*word)));
    }
    r
}

#[cfg(test)]
fn sample_scalar_uniform_mod_q(domain: &[u8], seed: &[u8], tag_idx: u32) -> u32 {
    let mut buf = [0u8; 24];
    cshake256_framed_xof(domain, &[seed, &tag_idx.to_be_bytes()], &mut buf);
    let value = reduce_wide_mod_q(&buf);
    wipe(&mut buf);
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

///Threshold share kind supported by `PiHdLinearModule`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ShareScheme {
    /// Degree `t - 1` Shamir sharing at validated nonzero distinct evaluation point `eval_point`.
    Shamir { threshold: u16, eval_point: u32 },
    /// Sum sharing with an exact full-committee opening roster and unit weights.
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
///
/// The secret coordinates, MAC shares and MAC key shares have no public accessor; they
/// are read only by the rekey and committed-evaluation protocol steps.
/// ```compile_fail
/// fn leak(share: &qsag_hd::LinearModulePartyShare) -> u32 { share.spdz_alpha_share() }
/// ```
/// ```compile_fail
/// fn leak(share: &qsag_hd::LinearModulePartyShare) -> qsag_hd::RingPoly {
///     share.s_share_coord(0).clone()
/// }
/// ```
/// ```compile_fail
/// fn leak(share: &qsag_hd::LinearModulePartyShare) -> qsag_hd::RingPoly {
///     share.spdz_mac_s1().clone()
/// }
/// ```
/// The lineage metadata is read-only outside the crate, so a holder cannot widen its
/// own derivation budget or rebind the share to another public key.
/// ```compile_fail
/// fn widen(share: &mut qsag_hd::LinearModulePartyShare) { share.max_depth = u16::MAX; }
/// ```
/// ```compile_fail
/// fn rewind(share: &mut qsag_hd::LinearModulePartyShare) { share.depth_used = 0; }
/// ```
/// ```compile_fail
/// fn rebind(share: &mut qsag_hd::LinearModulePartyShare) { share.seed_a = [0; 32]; }
/// ```
/// Positive control: the public metadata stays readable.
/// ```
/// fn lineage(share: &qsag_hd::LinearModulePartyShare) -> (u16, u16, u16, [u8; 32]) {
///     let _ = (share.scheme(), share.t_vec());
///     (share.party_id(), share.depth_used(), share.max_depth(), *share.seed_a())
/// }
/// ```
pub struct LinearModulePartyShare {
    pub(crate) party_id: u16,
    pub(crate) scheme: ShareScheme,
    additive_source_threshold: Option<u16>,
    pub(crate) seed_a: [u8; 32],
    pub(crate) t_vec: [RingPoly; MODULE_K],
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
    poison_journal: Option<Arc<dyn crate::poison::HdPoisonJournal>>,
    testing_poison_journal: bool,
    poisoned: Arc<AtomicBool>,
    evaluation_queries: Arc<AtomicUsize>,
    pub(crate) depth_used: u16,
    pub(crate) max_depth: u16,
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
    /// Convert this share to a sum sharing over the complete committee. Every
    /// custodian must perform the same conversion before evaluation. Privacy is
    /// inherited from the original sharing; this does not strengthen its corruption
    /// threshold. For a Shamir n-of-n input the output is an n-of-n additive sharing.
    pub fn into_additive(mut self) -> Result<Self, HdError> {
        let ShareScheme::Shamir {
            threshold,
            eval_point,
        } = self.scheme
        else {
            return Ok(self);
        };
        if self.committee.is_empty() || self.committee.len() > crate::MAX_CUSTODIANS {
            return Err(HdError::InvalidThresholdParameters);
        }
        let xs: Vec<_> = self.committee.iter().map(|entry| entry.1).collect();
        validate_shamir_eval_points(&xs)?;
        if !self.committee.contains(&(self.party_id, eval_point)) {
            return Err(HdError::InvalidThresholdParameters);
        }
        let weight = interpolation_weight(&xs, eval_point);
        for poly in &mut self.s_shares {
            poly.0 = poly.expose().scale(weight);
        }
        for lane in &mut self.spdz_macs {
            for poly in lane {
                poly.0 = poly.expose().scale(weight);
            }
        }
        for alpha in &mut self.spdz_alpha_shares {
            *alpha = mod_q_mul(*alpha, weight);
        }
        self.additive_source_threshold = Some(threshold);
        self.scheme = ShareScheme::Additive {
            num_parties: self.committee.len() as u16,
        };
        Ok(self)
    }

    /// Explicit opt-in for isolated tests without persistent custody. Absent from
    /// builds without `cfg(test)` or the `testing-ephemeral` feature (regression on
    /// [`DEALER_FREE_PUBLIC_API`]).
    #[cfg(any(test, feature = "testing-ephemeral"))]
    pub fn in_memory_poison_journal_for_testing(mut self) -> Self {
        self.testing_poison_journal = true;
        self
    }
    fn require_poison_journal(&self) -> Result<(), HdError> {
        if self.testing_poison_journal {
            return Ok(());
        }
        if self.poison_journal.is_some() && !self.is_permanently_poisoned() {
            return Ok(());
        }
        Err(HdError::MacCheckFailed)
    }
    pub fn attach_poison_journal(
        &mut self,
        journal: Arc<dyn crate::poison::HdPoisonJournal>,
    ) -> Result<(), HdError> {
        if journal.family_id() != self.family_id
            || journal.is_permanently_poisoned().unwrap_or(true)
        {
            self.poison();
            return Err(HdError::MacCheckFailed);
        }
        if self.poison_journal.is_some() || self.poisoned.load(Ordering::Acquire) {
            return Err(HdError::MacCheckFailed);
        }
        self.poison_journal = Some(journal);
        Ok(())
    }
    /// True iff this family is permanently quarantined: this handle (or a sibling
    /// sharing its latch) failed, or the durable journal records a quarantine or is
    /// damaged. The result is latched. A disclosure in flight is not a quarantine.
    pub fn is_permanently_poisoned(&self) -> bool {
        if self.poisoned.load(Ordering::Acquire) {
            return true;
        }
        if let Some(journal) = &self.poison_journal
            && journal.is_permanently_poisoned().unwrap_or(true)
        {
            self.poisoned.store(true, Ordering::Release);
            return true;
        }
        false
    }
    /// True while this share must not start an operation: it is permanently
    /// quarantined, or a disclosure on its family journal is in flight. Only the
    /// first is latched; the second clears when that disclosure completes.
    pub fn is_poisoned(&self) -> bool {
        self.is_permanently_poisoned()
            || self
                .poison_journal
                .as_ref()
                .is_some_and(|journal| journal.is_poisoned().unwrap_or(true))
    }
    fn poison(&mut self) {
        self.poisoned.store(true, Ordering::Release);
        if let Some(journal) = &self.poison_journal {
            let _ = journal.poison();
        }
        self.erase();
    }
    fn erase(&mut self) {
        wipe(&mut self.spdz_alpha_shares);
        wipe(&mut self.s_shares);
        wipe(&mut self.spdz_macs);
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
) -> ([RingPoly; MODULE_SECRET_L], SecretBytes<32>) {
    let idx_be = child_index.to_be_bytes();
    let tweak_seed = SecretBytes::<32>::new(cshake256_framed_32(
        b"QSAG.HD.LMOD.TWEAK_SEED.V1",
        &[chain_code, pk_digest, &idx_be],
    ));
    let next_chain_code = SecretBytes::<32>::new(cshake256_framed_32(
        b"QSAG.HD.LMOD.NEXT_CC.V1",
        &[chain_code, pk_digest, &idx_be],
    ));
    let tweaks = core::array::from_fn(|j| {
        RingPoly::sample_cbd2_ct(b"QSAG.HD.LMOD.R_POLY.V2", &tweak_seed[..], j as u32)
    });
    (tweaks, next_chain_code)
}

impl LinearModuleXPub {
    /// True iff `seed_a` matches the expanded matrix and every `t_vec` coefficient lies in `[0, MODULE_Q)`.
    pub fn is_canonical(&self) -> bool {
        self.seed_a == self.matrix.seed
            && self
                .t_vec
                .iter()
                .all(|p| p.coeffs.iter().all(|&c| c < MODULE_Q))
    }

    /// Derive non-hardened watch-only child `XPub` in **`0` online MPC rounds**:
    /// $\mathbf{t}^{(i)} = \mathbf{t} + \mathbf{A}\Delta s_1 + \Delta s_2 \bmod q$, enforcing $d + 1 \le D_{\max}$.
    pub fn derive_child(&self, child_index: u32) -> Result<Self, HdError> {
        if child_index & (1 << 31) != 0 {
            return Err(HdError::HardenedDerivationRequired);
        }
        if !self.is_canonical() {
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
            chain_code: Some(*next_cc),
            matrix: Arc::clone(&self.matrix),
            depth_used: self.depth_used + 1,
            max_depth: self.max_depth,
        })
    }

    pub fn to_address(&self, hrp: &str) -> Result<QsagAddress, HdError> {
        if !self.is_canonical() {
            return Err(HdError::InvalidThresholdParameters);
        }
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

    pub const fn party_id(&self) -> u16 {
        self.party_id
    }

    pub const fn scheme(&self) -> ShareScheme {
        self.scheme
    }

    pub const fn seed_a(&self) -> &[u8; 32] {
        &self.seed_a
    }

    /// Public relation image `t = A s1 + s2` of the shared secret.
    pub const fn t_vec(&self) -> &[RingPoly; MODULE_K] {
        &self.t_vec
    }

    pub const fn depth_used(&self) -> u16 {
        self.depth_used
    }

    pub const fn max_depth(&self) -> u16 {
        self.max_depth
    }
}

/// Validate that all `0..n` Shamir evaluation points are nonzero mod `MODULE_Q` and pairwise distinct!
/// Directly prevents the `eval_points[m] == 0` cleartext secret disclosure bug.
pub fn validate_shamir_eval_points(eval_points: &[u32]) -> Result<(), HdError> {
    for (i, &xi_raw) in eval_points.iter().enumerate() {
        let xi = ct_reduce_mod_q_u64(xi_raw as u64);
        if xi == 0 || xi_raw >= MODULE_Q {
            return Err(HdError::DuplicateOrZeroEvalPoint);
        }
        for &xj_raw in &eval_points[i + 1..] {
            if xi == (ct_reduce_mod_q_u64(xj_raw as u64)) {
                return Err(HdError::DuplicateOrZeroEvalPoint);
            }
        }
    }
    Ok(())
}

#[cfg(test)]
fn eval_poly(coeffs: &[RingPoly], x: u32) -> RingPoly {
    coeffs
        .iter()
        .rev()
        .fold(RingPoly::zero(), |acc, c| acc.scale(x).add(c))
}

/// Test-only trusted-dealer fixture. The dealer knows all secrets; production
/// roots come from the dealerless ceremony in `dealerless.rs`.
#[cfg(test)]
pub(crate) fn setup_shamir_linear_module(
    master_entropy: [u8; 32],
    threshold: u16,
    eval_points: &[u32],
    max_depth: u16,
) -> Result<(LinearModuleXPub, Vec<LinearModulePartyShare>), HdError> {
    if threshold == 0
        || usize::from(threshold) > eval_points.len()
        || eval_points.len() > usize::from(u16::MAX)
        || max_depth == 0
        || max_depth > MAX_NON_HARDENED_DERIVATION_DEPTH
    {
        return Err(HdError::InvalidThresholdParameters);
    }
    validate_shamir_eval_points(eval_points)?;
    let mut ent = master_entropy;
    let seed_a = cshake256_framed_32(b"QSAG.HD.LMOD.SEED_A.V2", &[&ent]);
    let chain_code = cshake256_framed_32(b"QSAG.HD.LMOD.ROOT_CC.V2", &[&ent]);
    let s_secret: [RingPoly; MODULE_SECRET_L] = core::array::from_fn(|j| {
        RingPoly::sample_cbd2_ct(b"QSAG.HD.LMOD.ROOT_S.V2", &ent, j as u32)
    });
    let matrix = Arc::new(ExpandedHdMatrix::new(seed_a));
    let t_vec = matrix.relation(&s_secret);
    let family_id = hash_t_vec(&seed_a, &t_vec);
    let degree = usize::from(threshold);
    let poly_coeffs: [Vec<RingPoly>; MODULE_SECRET_L] = core::array::from_fn(|j| {
        (0..degree)
            .map(|d| {
                if d == 0 {
                    s_secret[j].clone()
                } else {
                    RingPoly::sample_uniform_mod_q(
                        b"QSAG.HD.LMOD.SHAMIR.V2",
                        &ent,
                        ((j as u32) << 16) | d as u32,
                    )
                }
            })
            .collect()
    });
    let mut alpha_coeffs: [Vec<u32>; MODULE_MAC_LANES] = core::array::from_fn(|lane| {
        (0..degree)
            .map(|d| {
                sample_scalar_uniform_mod_q(
                    b"QSAG.HD.LMOD.ALPHA.V2",
                    &ent,
                    ((lane as u32) << 16) | d as u32,
                )
            })
            .collect()
    });
    let mac_coeffs: [[Vec<RingPoly>; MODULE_SECRET_L]; MODULE_MAC_LANES] =
        core::array::from_fn(|lane| {
            core::array::from_fn(|j| {
                (0..degree)
                    .map(|d| {
                        if d == 0 {
                            s_secret[j].scale(alpha_coeffs[lane][0])
                        } else {
                            RingPoly::sample_uniform_mod_q(
                                b"QSAG.HD.LMOD.MAC.V2",
                                &ent,
                                ((lane as u32) << 24) | ((j as u32) << 16) | d as u32,
                            )
                        }
                    })
                    .collect()
            })
        });
    let shares = eval_points
        .iter()
        .enumerate()
        .map(|(p, &x)| {
            LinearModulePartyShare {
                party_id: p as u16,
                scheme: ShareScheme::Shamir {
                    threshold,
                    eval_point: x,
                },
                additive_source_threshold: None,
                seed_a,
                t_vec: t_vec.clone(),
                chain_code: RedactedSecret::new(chain_code),
                chain_code_key: RedactedSecret::new(cshake256_framed_32(
                    b"QSAG.HD.CC.KEY.V1",
                    &[&ent],
                )),
                hardened: false,
                derivation_index: 0,
                s_shares: core::array::from_fn(|j| {
                    SecretRingPoly::new(eval_poly(&poly_coeffs[j], x))
                }),
                spdz_macs: core::array::from_fn(|lane| {
                    core::array::from_fn(|j| {
                        SecretRingPoly::new(eval_poly(&mac_coeffs[lane][j], x))
                    })
                }),
                spdz_alpha_shares: core::array::from_fn(|lane| {
                    alpha_coeffs[lane]
                        .iter()
                        .rev()
                        .fold(0, |acc, &c| mod_q_add(mod_q_mul(acc, x), c))
                }),
                matrix: Arc::clone(&matrix),
                family_id,
                #[cfg(feature = "std")]
                budget: None,
                committee: eval_points
                    .iter()
                    .enumerate()
                    .map(|(i, &x)| (i as u16, x))
                    .collect(),
                poison_journal: None,
                testing_poison_journal: false,
                poisoned: Arc::new(AtomicBool::new(false)),
                evaluation_queries: Arc::new(AtomicUsize::new(0)),
                depth_used: 0,
                max_depth,
            }
            .in_memory_poison_journal_for_testing()
        })
        .collect();
    for coeffs in &mut alpha_coeffs {
        wipe(coeffs);
    }
    wipe(&mut ent);
    Ok((
        LinearModuleXPub {
            seed_a,
            t_vec,
            chain_code: Some(chain_code),
            matrix,
            depth_used: 0,
            max_depth,
        },
        shares,
    ))
}

/// Lagrange coefficient of the point `own_x` for evaluating at `target` a
/// polynomial of degree below `xs.len()` from its values at the distinct points `xs`.
fn lagrange_weight(xs: &[u32], own_x: u32, target: u32) -> u32 {
    let mut numerator = 1;
    let mut denominator = 1;
    for &x in xs {
        if x != own_x {
            numerator = mod_q_mul(numerator, mod_q_sub(target, x));
            denominator = mod_q_mul(denominator, mod_q_sub(own_x, x));
        }
    }
    mod_q_mul(numerator, mod_q_inv_or_zero(denominator))
}

/// Weight of the share at `own_x` in the reconstruction of the secret at zero.
fn interpolation_weight(xs: &[u32], own_x: u32) -> u32 {
    lagrange_weight(xs, own_x, 0)
}

#[cfg(test)]
fn quorum_weights(
    quorum: &[LinearModulePartyShare],
    expected: &LinearModuleXPub,
) -> Result<Vec<u32>, HdError> {
    if expected.seed_a != expected.matrix.seed {
        return Err(HdError::InvalidThresholdParameters);
    }
    let first = quorum.first().ok_or(HdError::InvalidThresholdParameters)?;
    let threshold = match first.scheme {
        ShareScheme::Shamir { threshold, .. } => threshold,
        ShareScheme::Additive { num_parties } => num_parties,
    };
    if threshold == 0 || quorum.len() < usize::from(threshold) {
        return Err(HdError::InvalidThresholdParameters);
    }
    let additive = matches!(first.scheme, ShareScheme::Additive { .. });
    if additive && (quorum.len() != usize::from(threshold) || quorum.len() != first.committee.len())
    {
        return Err(HdError::InvalidThresholdParameters);
    }
    let mut xs = Vec::with_capacity(quorum.len());
    for (i, sh) in quorum.iter().enumerate() {
        if sh.is_poisoned()
            || (sh.hardened && expected.chain_code.is_some())
            || sh.seed_a != expected.seed_a
            || sh.t_vec != expected.t_vec
            || sh.depth_used != expected.depth_used
            || sh.max_depth != expected.max_depth
            || expected
                .chain_code
                .is_some_and(|cc| !qsag_accel::ct::ct_eq_bytes(sh.chain_code.expose(), &cc))
            || quorum[..i]
                .iter()
                .any(|prior| prior.party_id == sh.party_id)
        {
            return Err(HdError::InvalidThresholdParameters);
        }
        match sh.scheme {
            ShareScheme::Shamir {
                threshold: t,
                eval_point: x,
            } if !additive && t == threshold => xs.push(x),
            ShareScheme::Additive { num_parties }
                if additive
                    && num_parties == threshold
                    && sh.committee == first.committee
                    && first.committee.iter().any(|entry| entry.0 == sh.party_id) => {}
            _ => return Err(HdError::InvalidThresholdParameters),
        }
    }
    if additive {
        return Ok(alloc::vec![1; quorum.len()]);
    }
    validate_shamir_eval_points(&xs)?;
    Ok(xs.iter().map(|&x| interpolation_weight(&xs, x)).collect())
}

/// Test-only oracle: reconstructs complete secrets and authentication keys and
/// checks all seven MAC lanes and the key relation. Absent from every non-test build.
#[cfg(test)]
pub(crate) fn reconstruct_for_recovery_or_test(
    quorum: &[LinearModulePartyShare],
    expected_xpub: &LinearModuleXPub,
) -> Result<[RingPoly; MODULE_SECRET_L], HdError> {
    let weights = quorum_weights(quorum, expected_xpub)?;
    let secret = core::array::from_fn(|j| {
        quorum
            .iter()
            .zip(&weights)
            .fold(RingPoly::zero(), |acc, (sh, &w)| {
                acc.add(&sh.s_shares[j].expose().scale(w))
            })
    });
    let mut alpha = [0; MODULE_MAC_LANES];
    let mut difference = 0u32;
    for (lane, key) in alpha.iter_mut().enumerate() {
        *key = quorum.iter().zip(&weights).fold(0, |acc, (sh, &w)| {
            mod_q_add(acc, mod_q_mul(sh.spdz_alpha_shares[lane], w))
        });
        for (j, value) in secret.iter().enumerate() {
            let mac = quorum
                .iter()
                .zip(&weights)
                .fold(RingPoly::zero(), |acc, (sh, &w)| {
                    acc.add(&sh.spdz_macs[lane][j].expose().scale(w))
                });
            let expected = value.scale(*key);
            for (&a, &b) in mac.coeffs.iter().zip(&expected.coeffs) {
                difference |= a ^ b;
            }
        }
    }
    wipe(&mut alpha);
    if difference != 0 {
        return Err(HdError::MacCheckFailed);
    }
    if expected_xpub.matrix.relation(&secret) != expected_xpub.t_vec {
        return Err(HdError::InvalidThresholdParameters);
    }
    Ok(secret)
}

/// Test-only alias of the reconstruction oracle.
#[cfg(test)]
pub(crate) fn reconstruct_shamir_and_verify_key_relation(
    quorum: &[LinearModulePartyShare],
    expected_xpub: &LinearModuleXPub,
) -> Result<[RingPoly; MODULE_SECRET_L], HdError> {
    reconstruct_for_recovery_or_test(quorum, expected_xpub)
}

#[path = "threshold_eval.rs"]
mod threshold_eval;
pub use threshold_eval::*;

#[path = "dealerless.rs"]
mod dealerless;
pub use dealerless::*;

#[cfg(test)]
mod ntt_tests {
    use super::*;
    #[test]
    fn ntt_matches_schoolbook() {
        for seed in [0, 1, 29, 255] {
            let a = RingPoly::sample_uniform_mod_q(b"test", &[seed; 32], 0);
            let b = RingPoly::sample_uniform_mod_q(b"test", &[seed; 32], 1);
            let mut expected = RingPoly::zero();
            for (i, &left) in a.coeffs.iter().enumerate() {
                for (j, &right) in b.coeffs.iter().enumerate() {
                    let product = mod_q_mul(left, right);
                    let index = (i + j) % MODULE_N;
                    expected.coeffs[index] = if i + j < MODULE_N {
                        mod_q_add(expected.coeffs[index], product)
                    } else {
                        mod_q_sub(expected.coeffs[index], product)
                    };
                }
            }
            assert_eq!(a.mul_negacyclic(&b), expected);
        }
    }

    #[test]
    fn multiplication_reduces_noncanonical_public_coefficients() {
        let a = RingPoly::sample_uniform_mod_q(b"test", &[7; 32], 0);
        let b = RingPoly::sample_uniform_mod_q(b"test", &[7; 32], 1);
        let mut lifted = a.clone();
        for (i, c) in lifted.coeffs.iter_mut().enumerate() {
            *c += MODULE_Q * (i as u32 % 500);
        }
        lifted.coeffs[255] = u32::MAX - (u32::MAX - a.coeffs[255]) % MODULE_Q;
        assert_eq!(lifted.mul_negacyclic(&b), a.mul_negacyclic(&b));
        assert_eq!(b.mul_negacyclic(&lifted), a.mul_negacyclic(&b));
    }

    #[test]
    fn noncanonical_public_coefficients_are_reduced_in_arithmetic_and_refused_in_keys() {
        let q = MODULE_Q as u64;
        for (a, b) in [
            (MODULE_Q, 0),
            (0, MODULE_Q),
            (MODULE_Q + 5, MODULE_Q - 1),
            (2 * MODULE_Q + 1, 3 * MODULE_Q + 7),
            (u32::MAX, 1),
            (1, u32::MAX),
            (u32::MAX, u32::MAX),
        ] {
            let (ar, br) = (a as u64 % q, b as u64 % q);
            assert_eq!(mod_q_add(a, b) as u64, (ar + br) % q);
            assert_eq!(mod_q_sub(a, b) as u64, (ar + q - br) % q);
        }
        // The centered norm of a lifted polynomial is the norm of its canonical form;
        // it used to underflow `q - c` (a debug panic, a wrapped square in release).
        let canonical = RingPoly::sample_uniform_mod_q(b"test", &[9; 32], 0);
        let mut lifted = canonical.clone();
        for (i, c) in lifted.coeffs.iter_mut().enumerate() {
            *c += MODULE_Q * (1 + i as u32 % 500);
        }
        lifted.coeffs[0] = u32::MAX - (u32::MAX - canonical.coeffs[0]) % MODULE_Q;
        assert_eq!(
            lifted.centered_l2_norm_sq(),
            canonical.centered_l2_norm_sq()
        );
        // A public key with a coefficient outside `[0, q)` is not hashed into a child
        // or an address.
        let (pk, _) = setup_shamir_linear_module([4; 32], 2, &[1, 2, 3], 4).unwrap();
        assert!(pk.is_canonical());
        assert!(pk.derive_child(1).is_ok());
        assert!(pk.to_address("qsp").is_ok());
        for value in [MODULE_Q, MODULE_Q + pk.t_vec[2].coeffs[7], u32::MAX] {
            let mut bad = pk.clone();
            bad.t_vec[2].coeffs[7] = value;
            assert!(!bad.is_canonical());
            assert_eq!(
                bad.derive_child(1).err(),
                Some(HdError::InvalidThresholdParameters)
            );
            assert_eq!(
                bad.to_address("qsp").err(),
                Some(HdError::InvalidThresholdParameters)
            );
        }
    }
}

#[cfg(test)]
mod mac_tests {
    use super::*;
    #[test]
    fn every_coordinate_and_mac_lane_is_checked() {
        for coord in 0..MODULE_SECRET_L {
            let (pk, mut shares) = setup_shamir_linear_module([9; 32], 2, &[1, 2, 3], 4).unwrap();
            let last = shares.remove(2);
            let mut quorum = [shares.remove(0), last];
            quorum[0].s_shares[coord].0.coeffs[127] =
                mod_q_add(quorum[0].s_shares[coord].0.coeffs[127], 1);
            assert_eq!(
                reconstruct_shamir_and_verify_key_relation(&quorum, &pk),
                Err(HdError::MacCheckFailed)
            );
        }
        for lane in 0..MODULE_MAC_LANES {
            let (pk, mut shares) = setup_shamir_linear_module([9; 32], 2, &[1, 2, 3], 4).unwrap();
            let last = shares.remove(2);
            let mut quorum = [shares.remove(0), last];
            quorum[0].spdz_macs[lane][7].0.coeffs[255] =
                mod_q_add(quorum[0].spdz_macs[lane][7].0.coeffs[255], 1);
            assert_eq!(
                reconstruct_shamir_and_verify_key_relation(&quorum, &pk),
                Err(HdError::MacCheckFailed)
            );
        }
    }
}

/// Immutable public matrix cached in the FIPS 204 NTT domain.
#[derive(Debug, PartialEq, Eq)]
pub struct ExpandedHdMatrix {
    seed: [u8; 32],
    ntt: [[RingPoly; MODULE_L]; MODULE_K],
}
/// FIPS 204 forward NTT through the audited `qsag-asm` kernel, which is
/// constant time and requires canonical residues; inputs are reduced first
/// because `RingPoly::coeffs` is a public field.
fn forward(poly: &RingPoly) -> RingPoly {
    let mut out = poly.clone();
    for c in &mut out.coeffs {
        *c = ct_reduce_mod_q_u64(u64::from(*c));
    }
    qsag_asm::mldsa_ntt(&mut out.coeffs);
    out
}
fn inverse(mut poly: RingPoly) -> RingPoly {
    qsag_asm::mldsa_inv_ntt(&mut poly.coeffs);
    poly
}
impl ExpandedHdMatrix {
    pub fn new(seed: [u8; 32]) -> Self {
        let matrix = expand_matrix_a(&seed);
        Self {
            seed,
            ntt: core::array::from_fn(|r| core::array::from_fn(|c| forward(&matrix[r][c]))),
        }
    }
    pub fn multiply(&self, secret: &[RingPoly; MODULE_L]) -> [RingPoly; MODULE_K] {
        let transformed: [RingPoly; MODULE_L] = core::array::from_fn(|c| forward(&secret[c]));
        core::array::from_fn(|r| {
            let mut acc = RingPoly::zero();
            for (a, b) in self.ntt[r].iter().zip(&transformed) {
                for (c, (&x, &y)) in acc.coeffs.iter_mut().zip(a.coeffs.iter().zip(&b.coeffs)) {
                    *c = mod_q_add(*c, mod_q_mul(x, y));
                }
            }
            inverse(acc)
        })
    }
    fn relation(&self, secret: &[RingPoly; MODULE_SECRET_L]) -> [RingPoly; MODULE_K] {
        let product = self.multiply(&core::array::from_fn(|j| secret[j].clone()));
        core::array::from_fn(|r| product[r].add(&secret[MODULE_L + r]))
    }
}

fn pack_coefficients(values: &[u32], out: &mut [u8]) {
    let mut buffer = 0u64;
    let mut bits = 0;
    let mut cursor = 0;
    for &value in values {
        buffer |= u64::from(value & 0x7f_ffff) << bits;
        bits += 23;
        while bits >= 8 {
            out[cursor] = buffer as u8;
            cursor += 1;
            buffer >>= 8;
            bits -= 8;
        }
    }
    if bits != 0 {
        out[cursor] = buffer as u8;
    }
}
/// Canonical decoding of exactly `values.len()` packed 23-bit residues:
/// `None` for a wrong length, a residue `>= q` or nonzero padding bits.
fn unpack_canonical_coefficients(bytes: &[u8], values: &mut [u32]) -> Option<()> {
    let bits = values.len().checked_mul(23)?;
    if bytes.len() != bits.div_ceil(8) {
        return None;
    }
    unpack_coefficients(bytes, values);
    let padded = bits % 8 != 0 && bytes.last().is_some_and(|last| last >> (bits % 8) != 0);
    (!padded && values.iter().all(|&value| value < MODULE_Q)).then_some(())
}
fn unpack_coefficients(bytes: &[u8], values: &mut [u32]) {
    let mut buffer = 0u64;
    let mut bits = 0;
    let mut cursor = 0;
    for value in values {
        while bits < 23 {
            buffer |= u64::from(bytes[cursor]) << bits;
            cursor += 1;
            bits += 8;
        }
        *value = buffer as u32 & 0x7f_ffff;
        buffer >>= 23;
        bits -= 23;
    }
}

impl RingPoly {
    /// Version 1 external coefficient codec: exactly 736 bytes, little-endian 23-bit residues.
    /// Transcript hashing deliberately retains its original four-byte encoding.
    pub fn encode_packed_v1(&self) -> Result<[u8; 736], HdError> {
        if self.coeffs.iter().any(|&c| c >= MODULE_Q) {
            return Err(HdError::InvalidThresholdParameters);
        }
        let mut out = [0; 736];
        pack_coefficients(&self.coeffs, &mut out);
        Ok(out)
    }
    pub fn decode_packed_v1(bytes: &[u8]) -> Result<Self, HdError> {
        let mut out = Self::zero();
        unpack_canonical_coefficients(bytes, &mut out.coeffs)
            .ok_or(HdError::InvalidThresholdParameters)?;
        Ok(out)
    }
}

/// Test-only trusted-dealer hardened fixture.
#[cfg(test)]
pub(crate) fn setup_hardened_shamir_linear_module(
    entropy: [u8; 32],
    threshold: u16,
    eval_points: &[u32],
    max_depth: u16,
) -> Result<(LinearModuleXPub, Vec<LinearModulePartyShare>), HdError> {
    let (mut pk, mut shares) =
        setup_shamir_linear_module(entropy, threshold, eval_points, max_depth)?;
    pk.chain_code = None;
    for share in &mut shares {
        share.hardened = true;
    }
    Ok((pk, shares))
}

/// Test-only trusted-dealer rekey fixture retained for the historical regressions.
/// Production rekey is `LinearModulePartyShare::derive_child_share`.
#[cfg(test)]
pub(crate) fn trusted_dealer_rekey_child(
    parents: &mut [LinearModulePartyShare],
    expected: &LinearModuleXPub,
    child_index: u32,
    mut fresh_entropy: [u8; 32],
    hardened: bool,
) -> Result<(LinearModuleXPub, Vec<LinearModulePartyShare>), HdError> {
    let entropy = RedactedSecret::new(fresh_entropy);
    wipe(&mut fresh_entropy);
    let parent_secret = match reconstruct_for_recovery_or_test(parents, expected) {
        Ok(s) => s,
        Err(e) => {
            for p in parents {
                p.poison();
            }
            return Err(e);
        }
    };
    let first = &parents[0];
    if parents.len() != first.committee.len()
        || parents.iter().zip(&first.committee).any(|(p, &(id, x))| {
            p.party_id != id
                || match p.scheme {
                    ShareScheme::Shamir { eval_point, .. } => eval_point != x,
                    ShareScheme::Additive { num_parties } => {
                        usize::from(num_parties) != parents.len()
                    }
                }
        })
    {
        return Err(HdError::InvalidThresholdParameters);
    }
    if expected.depth_used >= expected.max_depth {
        return Err(HdError::DerivationBudgetExceeded {
            current: expected.depth_used,
            max: expected.max_depth,
        });
    }
    if expected.chain_code.is_none() && !hardened {
        return Err(HdError::HardenedDerivationRequired);
    }
    let digest = hash_t_vec(&expected.seed_a, &expected.t_vec);
    let seed = RedactedSecret::new(cshake256_framed_32(
        b"QSAG.HD.REKEY.V1",
        &[
            entropy.expose(),
            &digest,
            &child_index.to_be_bytes(),
            &expected.depth_used.to_be_bytes(),
        ],
    ));
    // Hardened secret derivation is deterministic in the parent/path. Rekey entropy
    // changes authentication/sharing only. The secret binding also permits a public
    // non-hardened parent to derive a genuinely hardened child.
    let secret_binding = RedactedSecret::new(hash_t_vec(
        &expected.seed_a,
        &core::array::from_fn(|j| parent_secret[j].clone()),
    ));
    let private_cc = RedactedSecret::new(cshake256_framed_32(
        b"QSAG.HD.HARDENED_CC.V1",
        &[first.chain_code.expose(), secret_binding.expose(), &digest],
    ));
    let cc = if hardened {
        private_cc.expose()
    } else {
        first.chain_code.expose()
    };
    let (tweak, next_cc) = expand_linear_tweak(cc, &digest, child_index);
    let target: [RingPoly; MODULE_SECRET_L] =
        core::array::from_fn(|j| parent_secret[j].add(&tweak[j]));
    let xs: Vec<_> = first.committee.iter().map(|entry| entry.1).collect();
    let threshold = match first.scheme {
        ShareScheme::Shamir { threshold, .. } => threshold,
        ShareScheme::Additive { num_parties } => num_parties,
    };
    let (random_pk, mut children) =
        setup_shamir_linear_module(*seed.expose(), threshold, &xs, expected.max_depth)?;
    let random_secret = reconstruct_for_recovery_or_test(&children, &random_pk)?;
    let delta: [RingPoly; MODULE_SECRET_L] =
        core::array::from_fn(|j| target[j].sub(&random_secret[j]));
    let pk = LinearModuleXPub {
        seed_a: expected.seed_a,
        t_vec: first.matrix.relation(&target),
        chain_code: if hardened { None } else { Some(*next_cc) },
        matrix: Arc::clone(&first.matrix),
        depth_used: expected.depth_used + 1,
        max_depth: expected.max_depth,
    };
    for (child, parent) in children.iter_mut().zip(parents.iter()) {
        for (j, shift) in delta.iter().enumerate() {
            child.s_shares[j] = SecretRingPoly::new(child.s_shares[j].expose().add(shift));
            for lane in 0..MODULE_MAC_LANES {
                child.spdz_macs[lane][j] = SecretRingPoly::new(
                    child.spdz_macs[lane][j]
                        .expose()
                        .add(&shift.scale(child.spdz_alpha_shares[lane])),
                );
            }
        }
        child.seed_a = pk.seed_a;
        child.t_vec = pk.t_vec.clone();
        child.chain_code = RedactedSecret::new(*next_cc);
        child.chain_code_key = RedactedSecret::new(*parent.chain_code_key.expose());
        child.hardened = hardened;
        child.derivation_index = child_index;
        child.depth_used = pk.depth_used;
        child.matrix = Arc::clone(&parent.matrix);
        child.family_id = parent.family_id;
        child.poison_journal = parent.poison_journal.clone();
        child.testing_poison_journal = parent.testing_poison_journal;
        child.poisoned = Arc::clone(&parent.poisoned);
        child.evaluation_queries = Arc::clone(&parent.evaluation_queries);
        #[cfg(feature = "std")]
        {
            child.budget = parent.budget.clone();
        }
    }
    if matches!(first.scheme, ShareScheme::Additive { .. }) {
        children = children
            .into_iter()
            .map(LinearModulePartyShare::into_additive)
            .collect::<Result<_, _>>()?;
    }
    let checked = reconstruct_for_recovery_or_test(&children, &pk)?;
    if checked != target {
        return Err(HdError::MacCheckFailed);
    }
    Ok((pk, children))
}

#[cfg(test)]
mod regression_tests {
    use super::*;
    #[test]
    fn additive_reconstruction_and_rekey_require_the_entire_committee() {
        let (pk, shamir) = setup_shamir_linear_module([73; 32], 3, &[1, 7, 31], 4).unwrap();
        let expected = reconstruct_for_recovery_or_test(&shamir, &pk).unwrap();
        let mut additive: Vec<_> = shamir
            .into_iter()
            .map(|s| s.into_additive().unwrap())
            .collect();
        assert_eq!(
            reconstruct_for_recovery_or_test(&additive, &pk).unwrap(),
            expected
        );
        assert!(reconstruct_for_recovery_or_test(&additive[..2], &pk).is_err());
        let (child_pk, child) =
            trusted_dealer_rekey_child(&mut additive, &pk, 7, [38; 32], false).unwrap();
        assert_eq!(child_pk, pk.derive_child(7).unwrap());
        assert!(
            child
                .iter()
                .all(|s| matches!(s.scheme, ShareScheme::Additive { num_parties: 3 }))
        );
        assert!(reconstruct_for_recovery_or_test(&child, &child_pk).is_ok());
        assert!(reconstruct_for_recovery_or_test(&child[..2], &child_pk).is_err());
    }

    #[test]
    fn reducer_cache_hash_and_codec_preserve_mappings() {
        for seed in [0, 1, 19, 255] {
            let mut bytes = [seed; 6144];
            cshake256_framed_xof(b"reduction-test", &[&[seed]], &mut bytes);
            for chunk in bytes.as_chunks::<24>().0 {
                let mut old = 0;
                for &byte in chunk {
                    for bit in (0..8).rev() {
                        old = mod_q_add(old, old);
                        old = mod_q_add(old, u32::from((byte >> bit) & 1));
                    }
                }
                assert_eq!(reduce_wide_mod_q(chunk), old);
            }
            // Lengths that are not a whole number of words keep the same map.
            for len in [0usize, 1, 3, 5, 23, 25] {
                let old = bytes[..len].iter().fold(0, |acc, &byte| {
                    ct_reduce_mod_q_u64(u64::from(acc) * 256 + u64::from(byte))
                });
                assert_eq!(reduce_wide_mod_q(&bytes[..len]), old);
            }
        }
        let matrix = expand_matrix_a(&[1; 32]);
        let cached = ExpandedHdMatrix::new([1; 32]);
        let secret =
            core::array::from_fn(|j| RingPoly::sample_uniform_mod_q(b"test", &[2; 32], j as u32));
        let old: [RingPoly; MODULE_K] = core::array::from_fn(|r| {
            matrix[r]
                .iter()
                .zip(&secret)
                .fold(RingPoly::zero(), |sum, (a, b)| {
                    sum.add(&a.mul_negacyclic(b))
                })
        });
        assert_eq!(cached.multiply(&secret), old);
        let old_bytes: Vec<_> = old.iter().map(RingPoly::to_bytes).collect();
        assert_eq!(
            hash_t_vec(&[1; 32], &old),
            cshake256_framed_32(
                b"QSAG.HD.LMOD.PK_HASH.V1",
                &[
                    &[1; 32],
                    &old_bytes[0],
                    &old_bytes[1],
                    &old_bytes[2],
                    &old_bytes[3]
                ]
            )
        );
        let poly = RingPoly {
            coeffs: core::array::from_fn(|i| if i % 2 == 0 { MODULE_Q - 1 } else { 0 }),
        };
        let packed = poly.encode_packed_v1().unwrap();
        assert_eq!(RingPoly::decode_packed_v1(&packed).unwrap(), poly);
        assert!(RingPoly::decode_packed_v1(&packed[..735]).is_err());
        assert!(RingPoly::decode_packed_v1(&[255; 736]).is_err());
    }
    #[test]
    fn hardened_descriptor_blocks_public_parent_recovery_and_bad_parent_rekey() {
        let (pk, mut parents) =
            setup_hardened_shamir_linear_module([5; 32], 2, &[1, 2, 3], 5).unwrap();
        assert!(pk.chain_code.is_none());
        assert_eq!(pk.derive_child(9), Err(HdError::HardenedDerivationRequired));
        let (child_pk, child) =
            trusted_dealer_rekey_child(&mut parents, &pk, 9, [91; 32], true).unwrap();
        assert!(child_pk.chain_code.is_none());
        let (repeat_pk, repeat) =
            trusted_dealer_rekey_child(&mut parents, &pk, 9, [93; 32], true).unwrap();
        assert_eq!(repeat_pk, child_pk);
        assert_ne!(repeat[0].spdz_alpha_shares, child[0].spdz_alpha_shares);
        let exposed_child = reconstruct_for_recovery_or_test(&child, &child_pk).unwrap();
        let parent = reconstruct_for_recovery_or_test(&parents, &pk).unwrap();
        // The report's attack using a public/placeholder chain code no longer recovers the parent.
        let (guessed_tweak, _) =
            expand_linear_tweak(&[0; 32], &hash_t_vec(&pk.seed_a, &pk.t_vec), 9);
        let guessed_parent: [RingPoly; MODULE_SECRET_L] =
            core::array::from_fn(|j| exposed_child[j].sub(&guessed_tweak[j]));
        assert_ne!(guessed_parent, parent);
        parents[0].spdz_macs[6][7].0.coeffs[255] =
            mod_q_add(parents[0].spdz_macs[6][7].0.coeffs[255], 1);
        assert!(matches!(
            trusted_dealer_rekey_child(&mut parents, &pk, 10, [92; 32], true),
            Err(HdError::MacCheckFailed)
        ));
    }
    #[test]
    fn query_basis_attack_stops_before_228_queries() {
        let (_, shares) = setup_shamir_linear_module([5; 32], 2, &[1, 2, 3], 5).unwrap();
        for _ in 0..128 {
            shares[0].burn_query().unwrap();
        }
        assert_eq!(
            shares[0].burn_query(),
            Err(HdError::EvaluationBudgetExceeded)
        );
    }

    #[test]
    fn derivation_depth_cap_bounds_cbd2_norm_growth() {
        assert_eq!(DEFAULT_MAX_DERIVATION_DEPTH, 8);
        assert_eq!(MAX_NON_HARDENED_DERIVATION_DEPTH, 16);
        assert_eq!(
            max_cbd2_linf_norm_after_depth(DEFAULT_MAX_DERIVATION_DEPTH),
            18
        );
        assert_eq!(
            max_cbd2_linf_norm_after_depth(MAX_NON_HARDENED_DERIVATION_DEPTH),
            34
        );
        assert!(
            setup_shamir_linear_module([7; 32], 2, &[1, 2, 3], DEFAULT_MAX_DERIVATION_DEPTH)
                .is_ok()
        );
        assert!(
            setup_shamir_linear_module([7; 32], 2, &[1, 2, 3], MAX_NON_HARDENED_DERIVATION_DEPTH)
                .is_ok()
        );
        assert_eq!(
            setup_shamir_linear_module(
                [7; 32],
                2,
                &[1, 2, 3],
                MAX_NON_HARDENED_DERIVATION_DEPTH + 1,
            )
            .err(),
            Some(HdError::InvalidThresholdParameters)
        );
    }
}

#[cfg(test)]
mod reduction_tests {
    use super::*;

    #[test]
    fn barrett_boundaries_and_full_width_random_inputs() {
        let q = MODULE_Q as u64;
        // Exhaust every residue at both ends of the u64 domain.
        for r in 0..q {
            for x in [r, q + r, u64::MAX - r] {
                assert_eq!(ct_reduce_mod_q_u64(x) as u64, x % q);
            }
        }
        for k in [0, 1, 2, u32::MAX as u64, u64::MAX / q] {
            let x = k * q;
            for v in [x.saturating_sub(1), x, x.saturating_add(1)] {
                assert_eq!(ct_reduce_mod_q_u64(v) as u64, v % q);
            }
        }
        let mut x = u128::MAX;
        for _ in 0..100_000 {
            assert_eq!(ct_reduce_mod_q_u128(x) as u128, x % q as u128);
            assert_eq!(ct_reduce_mod_q_u64(x as u64) as u64, (x as u64) % q);
            x = x
                .wrapping_mul(0xda942042e4dd58b5)
                .wrapping_add(0x9e3779b97f4a7c15);
        }
    }
}
