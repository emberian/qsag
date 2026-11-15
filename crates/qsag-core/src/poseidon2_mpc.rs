//! Dishonest-majority $t$-of-$n$ Shamir SPDZ `Poseidon2` MPC engine (`poseidon2_mpc.rs`) for
//! stateful `JortsPoseidon2` and stateless `Corduroy` / `Baggy` over `Poseidon2Suite`,
//! with authenticated arithmetic and checked output release.
//!
//! ### Security Architecture & Hardening Invariants
//! 1. **Zero Secret Reconstruction (`0` Omniscient RAM):** Key shares (`SK.seed`, `SK.prf`) arrive
//!    from `dkg.rs` as 256 Boolean-verified `Goldilocks` bit shares, are packed locally into 32
//!    canonical `[0, 255]` byte shares, and authenticated directly via dealerless
//!    [`spdz_authenticate_goldilocks_batch_ext2`] under a unified `GoldilocksExt2` SPDZ MAC key
//!    $\alpha \in \mathbb{F}_{p^2}$ (`|F_{p^2}| \approx 2^{128}`).
//! 2. **Exact 56-Bit Linear Sponge Packing:** Because `bytes_to_limbs56` packs 7 big-endian bytes
//!    into `< 2^{56} < p` without cross-byte carry or modular wraparound, injecting 32 secret
//!    byte shares `[0, 255]` into any `th_preimage` template is an exact $\mathbb{F}_p$-linear
//!    combination over `Goldilocks` (`0` input A2B circuits!).
//! 3. **1-Round Binomial $x^7$ S-Box (`118` Tuples / `poseidon2_perm12`):** Each S-box consumes one
//!    [`AuthenticatedPower7Share`] `([r], [r^2], ..., [r^7])`, opens $y = x + r$ (`degree < t`),
//!    queues `([x + r], [x_mac + r_mac], y)` for mandatory pre-cut SPDZ `MacCheck`, and evaluates
//!    $(y - r)^7$ linearly on shares and `GoldilocksExt2` MACs in 1 round.
//! 4. **Exact Canonical `< p` Arithmetic-to-Binary (`A2B`) for Unrevealed Chain Steps:** Unrevealed
//!    intermediate WOTS+C / FORS hashes convert `st[0..4]` into 32 canonical big-endian byte shares
//!    without opening `st[0..4]`: each lane masks $z = (x - r) \bmod p$ with a verified `< p`
//!    [`CanonicalBitMask64Share`], runs dual 64-bit public+secret ripple adders on $z + r$ and
//!    $(z + 2^{32} - 1) + r$, and selects exact canonical bits via the $2^{64}$ carry flag (`0`
//!    modulo-$p$ wraparound bugs across `0, 1, 2^{32} - 1, 2^{32}, p - 1`).
//! 5. **Strict Two-Stage Pre-Cut SPDZ `MacCheck` + Immediate Vault Poisoning:** Every cut-boundary
//!    opening (`r_rand`, FORS revealed leaf/tree leaves, WOTS+C chain endpoints, subtree public
//!    keys) verifies all queued intermediate wires AND the cut wires themselves via committed
//!    zero-masked [`commit_and_open_spdz_goldilocks_batch_quorum`] **strictly before** revealing
//!    the cut digest; any failure immediately calls `poison_and_wipe()` on all vaults and key shares.
//! 6. **Committee-wide latch gate on stateful signing:** a one-time leaf must be bound to one
//!    message across the whole committee, not only inside the `m >= t` members that happen to
//!    sign. The stateful entry points therefore accept local latches alone only when all `n`
//!    members attend, and otherwise require an [`EpochLatchCertificate`]: evidence that `q`
//!    members with `2q > n + (t - 1)` reserved this `(key, epoch, message digest)`. The signer
//!    re-checks the inequality and the binding, and refuses before any latch moves and before any
//!    share is touched. Availability follows the latch quorum, not `t`: a `(2, 3)` committee needs
//!    all three latches for every signature (see [`crate::dkg::QuorumEpochLatchCluster`]).
//! 7. **No caller-chosen randomiser:** the stateless signers derive `R` under MPC from `SK.prf`,
//!    a fixed domain frame and the message digest, so `R` (and with it the FORS instance) is the
//!    same in every session for a given `(key, message)`.

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use crate::dkg::{
    EpochLatchAuthorityPublic, EpochLatchCertificate, EpochLatchError as QuorumLatchError,
    ShamirPoseidonSeedShare, epoch_latch_binding, latch_quorum_intersects_honestly,
};
use crate::field::goldilocks::{Goldilocks, GoldilocksExt2};
use crate::keccak_mpc::DkgCachedSubtrees;
use crate::preprocessing::{
    OtMesh, PartyPrivateRng, PreprocessError, PreprocessedPoseidonPartyVault,
    commit_and_open_spdz_goldilocks_batch_quorum, open_and_check_degree_goldilocks,
    run_dealerless_pi_pow7_with_alpha, spdz_authenticate_goldilocks_batch_ext2,
    spdz_setup_alpha_goldilocks, validate_all_eval_points_goldilocks,
};
use crate::sponge::keccak::cshake256_32;
use crate::sponge::poseidon2::{
    POSEIDON2_CONST_IV, POSEIDON2_HALF_EXTERNAL_ROUNDS, POSEIDON2_INIT_STATE,
    POSEIDON2_INTERNAL_ROUNDS, bytes_to_limbs56, poseidon2_const_at, poseidon2_hash32,
    poseidon2_pad, poseidon2_perm12,
};
use crate::tsw_baggy::{
    AdrsKind, EpochLatchError, ForsTreeOpening, HashAdrs, LayerXmssSig, Poseidon2Suite,
    PqHashParams, PqHashSig, PqPublicKey, StatefulEpochLatch, TAG_PRF, TAG_TH_F,
    build_merkle_from_leaves_topdown, build_prf_msg_template, build_single_secret32_template,
    build_stateful_det_opt_domain, build_stateless_det_opt_domain,
    derive_stateless_leaf_and_fors_indices, grind_tsw_internal_counter, grind_tsw_leaf_counter,
    th_pre_hash, th_tweak_tl, verify_pq_hash_sig,
};
use crate::wipe::{
    SecretBuffer, SecretWipe, ct_eq_bytes32, secret_vec_push, secret_vec_reserve, wipe_bytes32,
    wipe_ext2, wipe_goldilocks,
};

/// Number of $x^7$ S-boxes in one Width-12 `poseidon2_perm12` (`4 * 12 + 22 * 1 + 4 * 12 = 118`).
pub const POSEIDON2_SBOXES_PER_PERM: usize = 118;

/// Number of Beaver triples consumed by one 64-bit canonical `< p` A2B lane conversion
/// (`63` for `z + r` + `63` for `(z + 2^32 - 1) + r` + `64` for carry mux = `190`).
pub const POSEIDON2_BEAVER_PER_A2B_LANE: usize = 190;

/// Number of Beaver triples consumed by one 4-lane (`256`-bit) sponge output A2B conversion (`760`).
pub const POSEIDON2_BEAVER_PER_A2B_HASH32: usize = 4 * POSEIDON2_BEAVER_PER_A2B_LANE;

const GOLDILOCKS_EPSILON: u64 = (1u64 << 32) - 1; // 2^64 - p = 2^32 - 1

/// Errors returned by the dishonest-majority `Poseidon2` SPDZ engine.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Poseidon2MpcError {
    InvalidParams,
    InvalidQuorum {
        t: usize,
        n: usize,
    },
    KeySharePoisoned {
        party_id: usize,
    },
    PublicSeedMismatch,
    Preprocess(PreprocessError),
    EpochLatch(EpochLatchError),
    TswGrindExhausted,
    PolicyRejected,
    SignatureSelfCheckFailed,
    /// A supplied top-subtree leaf cache does not belong to this `(params, pk)`: wrong layer, wrong
    /// public key, wrong leaf count, or leaves that do not hash to `pk_root`.
    CachedSubtreeMismatch,
    /// A stateful signature was requested from `signers < committee` members without a latch
    /// certificate. Local latches bind an epoch to a message only among the members present, so
    /// a different signing set could open the same one-time leaf for another message.
    LatchCertificateRequired {
        signers: usize,
        committee: usize,
    },
    /// The presented latch certificate does not authorise this `(committee, key, epoch, message)`.
    LatchCertificateRejected(QuorumLatchError),
    /// Signing was requested before the key shares were enrolled with a verified `(params, pk)` profile.
    KeyNotEnrolled,
    /// Key shares disagree on, or were invoked with a different, `(params, pk)` profile than enrolled.
    KeyProfileMismatch,
}

impl From<PreprocessError> for Poseidon2MpcError {
    fn from(e: PreprocessError) -> Self {
        Self::Preprocess(e)
    }
}

impl From<EpochLatchError> for Poseidon2MpcError {
    fn from(e: EpochLatchError) -> Self {
        Self::EpochLatch(e)
    }
}

/// SPDZ-authenticated `Goldilocks` wire share `([val]_p, [mac]_p)` held by a single party.
#[derive(Clone, Copy)]
struct AuthGlWire {
    val: Goldilocks,
    mac: GoldilocksExt2,
}

impl AuthGlWire {
    const ZERO: Self = Self {
        val: Goldilocks::ZERO,
        mac: GoldilocksExt2::ZERO,
    };

    #[inline]
    fn public_const(c: Goldilocks, alpha_share: GoldilocksExt2) -> Self {
        Self {
            val: c,
            mac: alpha_share.mul_base(c),
        }
    }

    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self {
            val: self.val + rhs.val,
            mac: self.mac + rhs.mac,
        }
    }

    #[inline]
    fn sub(self, rhs: Self) -> Self {
        Self {
            val: self.val - rhs.val,
            mac: self.mac - rhs.mac,
        }
    }

    #[inline]
    fn scale(self, c: Goldilocks) -> Self {
        Self {
            val: self.val * c,
            mac: self.mac.mul_base(c),
        }
    }

    #[inline]
    fn neg(self) -> Self {
        Self {
            val: self.val.const_neg(),
            mac: GoldilocksExt2::ZERO - self.mac,
        }
    }
}

impl SecretWipe for AuthGlWire {
    #[inline]
    fn secret_wipe(&mut self) {
        self.val.secret_wipe();
        self.mac.secret_wipe();
    }
}

/// Single party's non-clonable SPDZ-authenticated `Poseidon2` secret key share (`SK.seed`, `SK.prf`).
///
/// Redacts all field/MAC shares in `fmt::Debug` and volatile-wipes all secret storage on `Drop`
/// or `poison_and_wipe()`.
pub struct Poseidon2SpdzAuthenticatedKeyShare {
    pub party_id: usize,
    /// Number of members `n` the key was shared among; fixed when the share is authenticated.
    pub committee_size: usize,
    pub eval_point: Goldilocks,
    pub pk_seed: [u8; 32],
    pub mac_alpha_share: GoldilocksExt2,
    pub(crate) sk_seed_bytes: [Goldilocks; 32],
    pub(crate) sk_seed_macs: [GoldilocksExt2; 32],
    pub(crate) sk_prf_bytes: [Goldilocks; 32],
    pub(crate) sk_prf_macs: [GoldilocksExt2; 32],
    pub(crate) enrolled_profile: Option<(PqHashParams, PqPublicKey)>,
    pub(crate) enrolled_hem_profile: Option<(HemJortsPublicKey, HemDigest4)>,
    pub(crate) enrolled_latch_authority: Option<EpochLatchAuthorityPublic>,
    pub poisoned: bool,
}

impl fmt::Debug for Poseidon2SpdzAuthenticatedKeyShare {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Poseidon2SpdzAuthenticatedKeyShare")
            .field("party_id", &self.party_id)
            .field("poisoned", &self.poisoned)
            .finish_non_exhaustive()
    }
}

impl Poseidon2SpdzAuthenticatedKeyShare {
    /// Enrolled `(PqHashParams, PqPublicKey)` profile pinned to this key share, if any.
    #[inline]
    pub fn enrolled_profile(&self) -> Option<&(PqHashParams, PqPublicKey)> {
        self.enrolled_profile.as_ref()
    }

    /// Pin `(params, pk)` to this key share once. Re-enrolling the exact same `(params, pk)` is
    /// idempotent; any different `params` or `pk` returns [`Poseidon2MpcError::KeyProfileMismatch`].
    pub fn enroll_key_profile(
        &mut self,
        params: PqHashParams,
        pk: PqPublicKey,
    ) -> Result<(), Poseidon2MpcError> {
        if !params.is_well_formed() {
            return Err(Poseidon2MpcError::InvalidParams);
        }
        if !ct_eq_bytes32(&pk.pk_seed, &self.pk_seed) {
            return Err(Poseidon2MpcError::PublicSeedMismatch);
        }
        match &self.enrolled_profile {
            None => {
                self.enrolled_profile = Some((params, pk));
                Ok(())
            }
            Some((ep, epk)) => {
                if *ep == params
                    && ct_eq_bytes32(&epk.pk_seed, &pk.pk_seed)
                    && ct_eq_bytes32(&epk.pk_root, &pk.pk_root)
                {
                    Ok(())
                } else {
                    Err(Poseidon2MpcError::KeyProfileMismatch)
                }
            }
        }
    }

    /// Enrolled `Hem`-aggregatable `(HemJortsPublicKey, prf_check)` profile pinned to this share.
    #[inline]
    pub fn enrolled_hem_profile(&self) -> Option<&(HemJortsPublicKey, HemDigest4)> {
        self.enrolled_hem_profile.as_ref()
    }

    /// Pin a `Hem`-aggregatable `(HemJortsPublicKey, prf_check)` profile to this key share once.
    /// Re-enrolling the exact same `(pk, prf_check)` is idempotent; any mismatch returns
    /// [`Poseidon2MpcError::KeyProfileMismatch`].
    pub fn enroll_hem_key_profile(
        &mut self,
        pk: HemJortsPublicKey,
        prf_check: HemDigest4,
    ) -> Result<(), Poseidon2MpcError> {
        if pk.pk_seed != hem_pk_seed_from_bytes32(&self.pk_seed) {
            return Err(Poseidon2MpcError::PublicSeedMismatch);
        }
        match &self.enrolled_hem_profile {
            None => {
                self.enrolled_hem_profile = Some((pk, prf_check));
                Ok(())
            }
            Some((epk, eprf)) => {
                if *epk == pk && *eprf == prf_check {
                    Ok(())
                } else {
                    Err(Poseidon2MpcError::KeyProfileMismatch)
                }
            }
        }
    }

    /// Enrolled committee latch MAC authority pinned to this key share, if any.
    #[inline]
    pub fn enrolled_latch_authority(&self) -> Option<&EpochLatchAuthorityPublic> {
        self.enrolled_latch_authority.as_ref()
    }

    /// Pin a committee [`EpochLatchAuthorityPublic`] to this key share once. Re-enrolling the
    /// exact same authority is idempotent; any different authority or committee size returns
    /// `LatchCertificateRejected(CertificateCommitteeMismatch)`.
    pub fn enroll_latch_authority(
        &mut self,
        authority: EpochLatchAuthorityPublic,
    ) -> Result<(), Poseidon2MpcError> {
        if authority.committee_size() != self.committee_size {
            return Err(Poseidon2MpcError::LatchCertificateRejected(
                QuorumLatchError::CertificateCommitteeMismatch,
            ));
        }
        match &self.enrolled_latch_authority {
            None => {
                self.enrolled_latch_authority = Some(authority);
                Ok(())
            }
            Some(existing) if *existing == authority => Ok(()),
            Some(_) => Err(Poseidon2MpcError::LatchCertificateRejected(
                QuorumLatchError::CertificateCommitteeMismatch,
            )),
        }
    }

    /// Permanently burn this key share and volatile-wipe its secret byte shares and MACs.
    pub fn poison_and_wipe(&mut self) {
        self.poisoned = true;
        wipe_goldilocks(&mut self.sk_seed_bytes);
        wipe_ext2(&mut self.sk_seed_macs);
        wipe_goldilocks(&mut self.sk_prf_bytes);
        wipe_ext2(&mut self.sk_prf_macs);
        wipe_ext2(core::slice::from_mut(&mut self.mac_alpha_share));
    }
}

impl Drop for Poseidon2SpdzAuthenticatedKeyShare {
    fn drop(&mut self) {
        self.poison_and_wipe();
        wipe_bytes32(&mut self.pk_seed);
    }
}

/// Queued intermediate SPDZ wire openings (`y = x + r`, Beaver `d, e`, A2B `z = x - r`) that MUST
/// pass committed zero-masked `GoldilocksExt2` `MacCheck` **strictly before** any cut-boundary
/// digest is opened.
struct SpdzGoldilocksPendingChecks {
    quorum_size: usize,
    shares_per_party: Vec<Vec<Goldilocks>>,
    macs_per_party: Vec<Vec<GoldilocksExt2>>,
}

impl SpdzGoldilocksPendingChecks {
    fn new(quorum_size: usize) -> Self {
        Self {
            quorum_size,
            shares_per_party: vec![Vec::new(); quorum_size],
            macs_per_party: vec![Vec::new(); quorum_size],
        }
    }

    #[inline]
    fn record_batch(&mut self, wires_per_party: &[Vec<AuthGlWire>]) {
        debug_assert_eq!(wires_per_party.len(), self.quorum_size);
        let q = self.quorum_size;
        for ((shares, macs), wires) in self.shares_per_party[..q]
            .iter_mut()
            .zip(self.macs_per_party[..q].iter_mut())
            .zip(wires_per_party[..q].iter())
        {
            secret_vec_reserve(shares, wires.len());
            secret_vec_reserve(macs, wires.len());
            for w in wires {
                secret_vec_push(shares, w.val);
                secret_vec_push(macs, w.mac);
            }
        }
    }

    fn clear_and_wipe(&mut self) {
        for p in 0..self.quorum_size {
            wipe_goldilocks(&mut self.shares_per_party[p]);
            wipe_ext2(&mut self.macs_per_party[p]);
            self.shares_per_party[p].clear();
            self.macs_per_party[p].clear();
        }
    }
}

impl Drop for SpdzGoldilocksPendingChecks {
    fn drop(&mut self) {
        self.clear_and_wipe();
    }
}

fn poison_all_on_abort(
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
) {
    for ks in key_shares.iter_mut() {
        ks.poison_and_wipe();
    }
    for v in vaults.iter_mut() {
        v.poison_and_wipe();
    }
}

/// Authenticate distributed `ShamirPoseidonSeedShare`s (`SK.seed`, `SK.prf`, `pk_seed`) and
/// simultaneously generate correlated `PreprocessedPoseidonPartyVault`s under a single unified
/// dealerless `GoldilocksExt2` SPDZ MAC key $\alpha \in \mathbb{F}_{p^2}$ (`0` central RAM).
#[expect(
    clippy::too_many_arguments,
    reason = "One setup ceremony: session, quorum, both DKG transcripts, three tuple budgets, OT mesh and party randomness"
)]
pub fn authenticate_poseidon_dkg_shares_and_preprocess(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[Goldilocks],
    pk_seed: [u8; 32],
    sk_seed_dkg: &[ShamirPoseidonSeedShare],
    sk_prf_dkg: &[ShamirPoseidonSeedShare],
    num_pow7: usize,
    num_extra_beaver: usize,
    num_a2b_masks: usize,
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<
    (
        Vec<Poseidon2SpdzAuthenticatedKeyShare>,
        Vec<PreprocessedPoseidonPartyVault>,
    ),
    Poseidon2MpcError,
> {
    let n = eval_points.len();
    if t < 2
        || t > n
        || sk_seed_dkg.len() != n
        || sk_prf_dkg.len() != n
        || party_rngs.len() != n
        || ot_mesh.n != n
    {
        return Err(Poseidon2MpcError::InvalidQuorum { t, n });
    }
    validate_all_eval_points_goldilocks(eval_points)?;

    for p in 0..n {
        if !sk_seed_dkg[p].is_valid()
            || !sk_prf_dkg[p].is_valid()
            || sk_seed_dkg[p].eval_point != eval_points[p]
            || sk_prf_dkg[p].eval_point != eval_points[p]
        {
            return Err(Poseidon2MpcError::KeySharePoisoned { party_id: p });
        }
    }

    // 1. Pack 256 Boolean-verified DKG bit shares locally into 32 canonical `[0, 255]` byte shares
    let mut flat_bytes_per_party = SecretBuffer(vec![vec![Goldilocks::ZERO; 64]; n]);
    for p in 0..n {
        for byte_idx in 0..32 {
            let mut acc_seed = SecretBuffer(Goldilocks::ZERO);
            let mut acc_prf = SecretBuffer(Goldilocks::ZERO);
            let mut pow2 = Goldilocks::ONE;
            for bit in 0..8 {
                *acc_seed += pow2 * sk_seed_dkg[p].bit_shares[8 * byte_idx + bit];
                *acc_prf += pow2 * sk_prf_dkg[p].bit_shares[8 * byte_idx + bit];
                pow2 = pow2 + pow2;
            }
            flat_bytes_per_party[p][byte_idx] = *acc_seed;
            flat_bytes_per_party[p][32 + byte_idx] = *acc_prf;
        }
    }

    // 2. Establish unified dealerless `GoldilocksExt2` SPDZ MAC key `\alpha` across `0..n`
    let alpha_sid = cshake256_32(b"QSAG.POS2.UNIFIED.ALPHA/v1", &session_id);
    let (alpha_contribs_raw, alpha_shamir_raw) =
        spdz_setup_alpha_goldilocks(&alpha_sid, t, eval_points, party_rngs)?;
    let alpha_contribs = SecretBuffer(alpha_contribs_raw);
    let alpha_shamir = SecretBuffer(alpha_shamir_raw);

    // 3. Authenticate all 64 secret byte shares via LHL Gilboa OLE + SPDZ sacrifice (`0` central RAM!)
    let key_auth_sid = cshake256_32(b"QSAG.POS2.KEY.AUTH/v1", &session_id);
    let key_macs = SecretBuffer(spdz_authenticate_goldilocks_batch_ext2(
        &key_auth_sid,
        t,
        eval_points,
        ot_mesh,
        &alpha_contribs,
        &alpha_shamir,
        &flat_bytes_per_party,
        party_rngs,
    )?);

    // 4. Generate correlated `Π_pow7` + Beaver + Canonical `< p` A2B vaults under the SAME `\alpha`
    let vault_sid = cshake256_32(b"QSAG.POS2.VAULT.POW7/v1", &session_id);
    let vaults = run_dealerless_pi_pow7_with_alpha(
        vault_sid,
        t,
        eval_points,
        num_pow7,
        num_extra_beaver,
        num_a2b_masks,
        &alpha_contribs,
        &alpha_shamir,
        ot_mesh,
        party_rngs,
    )?;
    drop(alpha_contribs);

    let mut key_shares = Vec::with_capacity(n);
    for p in 0..n {
        let mut sk_seed_bytes = [Goldilocks::ZERO; 32];
        let mut sk_seed_macs = [GoldilocksExt2::ZERO; 32];
        let mut sk_prf_bytes = [Goldilocks::ZERO; 32];
        let mut sk_prf_macs = [GoldilocksExt2::ZERO; 32];
        sk_seed_bytes.copy_from_slice(&flat_bytes_per_party[p][0..32]);
        sk_seed_macs.copy_from_slice(&key_macs[p][0..32]);
        sk_prf_bytes.copy_from_slice(&flat_bytes_per_party[p][32..64]);
        sk_prf_macs.copy_from_slice(&key_macs[p][32..64]);
        key_shares.push(Poseidon2SpdzAuthenticatedKeyShare {
            party_id: p,
            committee_size: n,
            eval_point: eval_points[p],
            pk_seed,
            mac_alpha_share: alpha_shamir[p],
            sk_seed_bytes,
            sk_seed_macs,
            sk_prf_bytes,
            sk_prf_macs,
            enrolled_profile: None,
            enrolled_hem_profile: None,
            enrolled_latch_authority: None,
            poisoned: false,
        });
    }

    Ok((key_shares, vaults))
}

#[inline]
fn apply_m4_auth(b: [AuthGlWire; 4]) -> [AuthGlWire; 4] {
    let s = b[0].add(b[1]).add(b[2].add(b[3]));
    [
        s.add(b[0].add(b[1].scale(Goldilocks::TWO))),
        s.add(b[1].add(b[2].scale(Goldilocks::TWO))),
        s.add(b[2].add(b[3].scale(Goldilocks::TWO))),
        s.add(b[3].add(b[0].scale(Goldilocks::TWO))),
    ]
}

fn apply_me_auth(st: &mut [AuthGlWire; 12]) {
    let y0 = apply_m4_auth([st[0], st[1], st[2], st[3]]);
    let y1 = apply_m4_auth([st[4], st[5], st[6], st[7]]);
    let y2 = apply_m4_auth([st[8], st[9], st[10], st[11]]);
    for i in 0..4 {
        let s = y0[i].add(y1[i]).add(y2[i]);
        st[i] = y0[i].add(s);
        st[4 + i] = y1[i].add(s);
        st[8 + i] = y2[i].add(s);
    }
}

fn apply_mi_auth(st: &mut [AuthGlWire; 12]) {
    let mut s = AuthGlWire::ZERO;
    for lane in st.iter() {
        s = s.add(*lane);
    }
    st[0] = st[0].scale(Goldilocks::TWO).neg().add(s);
    st[1] = st[1].add(s);
    let mut d = Goldilocks::TWO;
    for lane in st.iter_mut().skip(2) {
        *lane = lane.scale(d).add(s);
        d = d + d;
    }
}

/// Evaluate a batch of $x \mapsto x^7 \bmod p$ S-boxes in 1 communication round across the quorum
/// using pre-verified [`AuthenticatedPower7Share`]s and Binomial expansion $(y - r)^7$.
fn eval_sbox7_batch_spdz(
    t: usize,
    quorum_pts: &[Goldilocks],
    inputs_per_party: &[Vec<AuthGlWire>],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    pending: &mut SpdzGoldilocksPendingChecks,
) -> Result<Vec<Vec<AuthGlWire>>, PreprocessError> {
    let m = quorum_pts.len();
    let count = inputs_per_party[0].len();
    let mut tuples_p = Vec::with_capacity(m);
    let alphas = SecretBuffer(vaults.iter().map(|v| v.mac_alpha_share).collect::<Vec<_>>());
    let mut masked_wires = SecretBuffer(vec![Vec::with_capacity(count); m]);
    for (p, vault) in vaults.iter_mut().enumerate() {
        let p_tups = vault.reserve_pow7(count)?;
        for (input, tup) in inputs_per_party[p][..count].iter().zip(p_tups) {
            let r_wire = AuthGlWire {
                val: tup.r_pows[0],
                mac: tup.r_macs[0],
            };
            masked_wires[p].push(input.add(r_wire));
        }
        tuples_p.push(p_tups);
    }

    pending.record_batch(&masked_wires);

    let mut y_opened = Vec::with_capacity(count);
    let mut sh_buf = SecretBuffer(vec![Goldilocks::ZERO; m]);
    for k in 0..count {
        for (buf, wires) in sh_buf.iter_mut().zip(masked_wires.iter()) {
            *buf = wires[k].val;
        }
        y_opened.push(open_and_check_degree_goldilocks(
            t,
            quorum_pts,
            &sh_buf,
            "pos2_sbox7_y",
        )?);
    }
    drop(sh_buf);

    let c7 = Goldilocks::from_u64_reduced(7);
    let c21 = Goldilocks::from_u64_reduced(21);
    let c35 = Goldilocks::from_u64_reduced(35);

    let mut out = SecretBuffer(vec![Vec::with_capacity(count); m]);
    for p in 0..m {
        let alpha_p = alphas[p];
        for k in 0..count {
            let y = y_opened[k];
            let y2 = y * y;
            let y3 = y2 * y;
            let y4 = y2 * y2;
            let y5 = y4 * y;
            let y6 = y3 * y3;
            let y7 = y6 * y;
            let tup = &tuples_p[p][k];
            let rw = |idx: usize| AuthGlWire {
                val: tup.r_pows[idx],
                mac: tup.r_macs[idx],
            };
            // (y - r)^7 = y^7 - 7 y^6 r + 21 y^5 r^2 - 35 y^4 r^3 + 35 y^3 r^4 - 21 y^2 r^5 + 7 y r^6 - r^7
            let mut acc = AuthGlWire::public_const(y7, alpha_p);
            acc = acc.sub(rw(0).scale(c7 * y6));
            acc = acc.add(rw(1).scale(c21 * y5));
            acc = acc.sub(rw(2).scale(c35 * y4));
            acc = acc.add(rw(3).scale(c35 * y3));
            acc = acc.sub(rw(4).scale(c21 * y2));
            acc = acc.add(rw(5).scale(c7 * y));
            acc = acc.sub(rw(6));
            out[p].push(acc);
        }
    }
    Ok(core::mem::take(&mut out.0))
}

/// Evaluate $B$ parallel Width-12 `poseidon2_perm12` permutations in SPDZ (`30` S-box rounds total
/// regardless of batch size $B$, consuming `118 * B` `AuthenticatedPower7Share`s).
fn eval_spdz_poseidon2_perm12_batch(
    t: usize,
    quorum_pts: &[Goldilocks],
    states_per_party: &mut [Vec<[AuthGlWire; 12]>],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    pending: &mut SpdzGoldilocksPendingChecks,
) -> Result<(), PreprocessError> {
    let m = quorum_pts.len();
    let batch = states_per_party[0].len();
    if batch == 0 {
        return Ok(());
    }

    for states in &mut states_per_party[..m] {
        for st in &mut states[..batch] {
            apply_me_auth(st);
        }
    }

    // First 4 external rounds (`tag = 0`)
    for r in 0..POSEIDON2_HALF_EXTERNAL_ROUNDS {
        let mut sbox_in = SecretBuffer(vec![Vec::with_capacity(batch * 12); m]);
        for p in 0..m {
            let alpha_p = vaults[p].mac_alpha_share;
            for st in &states_per_party[p][..batch] {
                for (lane, wire) in st.iter().enumerate() {
                    let rc =
                        AuthGlWire::public_const(poseidon2_const_at(0, r, lane as u64), alpha_p);
                    sbox_in[p].push(wire.add(rc));
                }
            }
        }
        let sbox_out = SecretBuffer(eval_sbox7_batch_spdz(
            t, quorum_pts, &sbox_in, vaults, pending,
        )?);
        for p in 0..m {
            for b in 0..batch {
                for lane in 0..12 {
                    states_per_party[p][b][lane] = sbox_out[p][12 * b + lane];
                }
                apply_me_auth(&mut states_per_party[p][b]);
            }
        }
    }

    // 22 internal partial rounds (`tag = 1`, S-box on lane 0 BEFORE `apply_mi`)
    for r in 0..POSEIDON2_INTERNAL_ROUNDS {
        let mut sbox_in = SecretBuffer(vec![Vec::with_capacity(batch); m]);
        for p in 0..m {
            let alpha_p = vaults[p].mac_alpha_share;
            let rc0 = AuthGlWire::public_const(poseidon2_const_at(1, r, 0), alpha_p);
            for st in &states_per_party[p][..batch] {
                sbox_in[p].push(st[0].add(rc0));
            }
        }
        let sbox_out = SecretBuffer(eval_sbox7_batch_spdz(
            t, quorum_pts, &sbox_in, vaults, pending,
        )?);
        for p in 0..m {
            for b in 0..batch {
                states_per_party[p][b][0] = sbox_out[p][b];
                apply_mi_auth(&mut states_per_party[p][b]);
            }
        }
    }

    // Final 4 external rounds (`tag = 2`)
    for r in 0..POSEIDON2_HALF_EXTERNAL_ROUNDS {
        let mut sbox_in = SecretBuffer(vec![Vec::with_capacity(batch * 12); m]);
        for p in 0..m {
            let alpha_p = vaults[p].mac_alpha_share;
            for st in &states_per_party[p][..batch] {
                for (lane, wire) in st.iter().enumerate() {
                    let rc =
                        AuthGlWire::public_const(poseidon2_const_at(2, r, lane as u64), alpha_p);
                    sbox_in[p].push(wire.add(rc));
                }
            }
        }
        let sbox_out = SecretBuffer(eval_sbox7_batch_spdz(
            t, quorum_pts, &sbox_in, vaults, pending,
        )?);
        for p in 0..m {
            for b in 0..batch {
                for lane in 0..12 {
                    states_per_party[p][b][lane] = sbox_out[p][12 * b + lane];
                }
                apply_me_auth(&mut states_per_party[p][b]);
            }
        }
    }

    Ok(())
}

/// Pack a batch of `(template_with_zeroed_32b_slot, secret_offset)` preimages paired with 32
/// SPDZ-authenticated canonical `[0, 255]` secret byte shares per item, and evaluate the full
/// `Poseidon2` rate-8 sponge (`bytes_to_limbs56` + `poseidon2_pad`), returning the 4 output
/// squeeze lanes `st[0..4]` per batch item (`0` A2B conversions on input!).
fn eval_spdz_poseidon2_hash32_templates(
    t: usize,
    quorum_pts: &[Goldilocks],
    templates: &[(Vec<u8>, usize)],
    secrets_per_party: &[Vec<[AuthGlWire; 32]>],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    pending: &mut SpdzGoldilocksPendingChecks,
) -> Result<Vec<Vec<[AuthGlWire; 4]>>, PreprocessError> {
    let m = quorum_pts.len();
    let batch = templates.len();
    if batch == 0 {
        return Ok(vec![Vec::new(); m]);
    }

    // Precompute public padded limbs and block count for each template
    let mut padded_templates: Vec<Vec<Goldilocks>> = Vec::with_capacity(batch);
    let mut max_blocks = 0usize;
    for (tmpl, _) in templates {
        let mut limbs = bytes_to_limbs56(tmpl);
        poseidon2_pad(&mut limbs);
        max_blocks = max_blocks.max(limbs.len() / 8);
        padded_templates.push(limbs);
    }

    // Build authenticated limb vectors per `(party, item)` using exact 56-bit byte weights
    let mut item_limbs_p: SecretBuffer<Vec<Vec<Vec<AuthGlWire>>>> =
        SecretBuffer(vec![Vec::with_capacity(batch); m]);
    for p in 0..m {
        let alpha_p = vaults[p].mac_alpha_share;
        for item in 0..batch {
            let mut limbs: Vec<AuthGlWire> = padded_templates[item]
                .iter()
                .map(|&c| AuthGlWire::public_const(c, alpha_p))
                .collect();
            let off = templates[item].1;
            for (k, secret) in secrets_per_party[p][item].iter().enumerate() {
                let pos = off + k;
                let limb_idx = pos / 7;
                let byte_slot = pos % 7;
                let weight = Goldilocks::from_u64_reduced(1u64 << ((6 - byte_slot) * 8));
                limbs[limb_idx] = limbs[limb_idx].add(secret.scale(weight));
            }
            item_limbs_p[p].push(limbs);
        }
    }

    // Initialize sponge states to `POSEIDON2_INIT_STATE`
    let mut states_p: SecretBuffer<Vec<Vec<[AuthGlWire; 12]>>> =
        SecretBuffer(vec![Vec::with_capacity(batch); m]);
    for p in 0..m {
        let alpha_p = vaults[p].mac_alpha_share;
        let mut init_st = [AuthGlWire::ZERO; 12];
        for lane in 0..12 {
            init_st[lane] = AuthGlWire::public_const(POSEIDON2_INIT_STATE[lane], alpha_p);
        }
        for _ in 0..batch {
            states_p[p].push(init_st);
        }
    }

    // Step through absorb blocks in lockstep across active items
    for blk in 0..max_blocks {
        let active_indices: Vec<usize> = (0..batch)
            .filter(|&item| blk < padded_templates[item].len() / 8)
            .collect();
        let mut sub_states = SecretBuffer(vec![Vec::with_capacity(active_indices.len()); m]);
        for p in 0..m {
            for &item in &active_indices {
                let mut st = states_p[p][item];
                for lane in 0..8 {
                    st[lane] = st[lane].add(item_limbs_p[p][item][8 * blk + lane]);
                }
                sub_states[p].push(st);
            }
        }
        eval_spdz_poseidon2_perm12_batch(t, quorum_pts, &mut sub_states, vaults, pending)?;
        for p in 0..m {
            for (slot, &item) in active_indices.iter().enumerate() {
                states_p[p][item] = sub_states[p][slot];
            }
        }
    }

    let mut out = SecretBuffer(vec![Vec::with_capacity(batch); m]);
    for p in 0..m {
        for st in &states_p[p][..batch] {
            out[p].push([st[0], st[1], st[2], st[3]]);
        }
    }
    Ok(core::mem::take(&mut out.0))
}

/// Batched SPDZ Beaver multiplication `[x_k * y_k]` in 1 communication round, recording all
/// `(d_k, e_k)` masked wires into `pending` for pre-cut SPDZ `MacCheck`.
fn eval_spdz_beaver_mul_batch(
    t: usize,
    quorum_pts: &[Goldilocks],
    xs_per_party: &[Vec<AuthGlWire>],
    ys_per_party: &[Vec<AuthGlWire>],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    pending: &mut SpdzGoldilocksPendingChecks,
) -> Result<Vec<Vec<AuthGlWire>>, PreprocessError> {
    let m = quorum_pts.len();
    let count = xs_per_party[0].len();
    if count == 0 {
        return Ok(vec![Vec::new(); m]);
    }
    let mut triples_p = Vec::with_capacity(m);
    let alphas = SecretBuffer(vaults.iter().map(|v| v.mac_alpha_share).collect::<Vec<_>>());
    let mut de_wires = SecretBuffer(vec![Vec::with_capacity(2 * count); m]);
    for (p, vault) in vaults.iter_mut().enumerate() {
        let p_tr = vault.reserve_beaver(count)?;
        for (k, tr) in p_tr.iter().enumerate() {
            let a_w = AuthGlWire {
                val: tr.a,
                mac: tr.a_mac,
            };
            let b_w = AuthGlWire {
                val: tr.b,
                mac: tr.b_mac,
            };
            de_wires[p].push(xs_per_party[p][k].sub(a_w));
            de_wires[p].push(ys_per_party[p][k].sub(b_w));
        }
        triples_p.push(p_tr);
    }

    pending.record_batch(&de_wires);

    let mut de_open = Vec::with_capacity(2 * count);
    let mut sh_buf = SecretBuffer(vec![Goldilocks::ZERO; m]);
    for idx in 0..(2 * count) {
        for (buf, wires) in sh_buf.iter_mut().zip(de_wires.iter()) {
            *buf = wires[idx].val;
        }
        de_open.push(open_and_check_degree_goldilocks(
            t,
            quorum_pts,
            &sh_buf,
            "pos2_beaver_de",
        )?);
    }
    drop(sh_buf);

    let mut out = SecretBuffer(vec![Vec::with_capacity(count); m]);
    for p in 0..m {
        let alpha_p = alphas[p];
        for k in 0..count {
            let d = de_open[2 * k];
            let e = de_open[2 * k + 1];
            let tr = &triples_p[p][k];
            let a_w = AuthGlWire {
                val: tr.a,
                mac: tr.a_mac,
            };
            let b_w = AuthGlWire {
                val: tr.b,
                mac: tr.b_mac,
            };
            let c_w = AuthGlWire {
                val: tr.c,
                mac: tr.c_mac,
            };
            let de_const = AuthGlWire::public_const(d * e, alpha_p);
            let z = c_w.add(b_w.scale(d)).add(a_w.scale(e)).add(de_const);
            out[p].push(z);
        }
    }
    Ok(core::mem::take(&mut out.0))
}

/// Exact canonical `< p` Arithmetic-to-Binary (`A2B`) conversion of a batch of 4-lane sponge
/// outputs (`st[0..4]`) into 32 canonical big-endian byte shares `[0, 255]` (`to_be_bytes()`)
/// WITHOUT opening `st[0..4]`.
///
/// Consumes `4` [`CanonicalBitMask64Share`]s + `760` [`GoldilocksBeaverShare`]s per 32-byte digest.
fn eval_spdz_canonical_a2b_state4_batch_to_bytes32(
    t: usize,
    quorum_pts: &[Goldilocks],
    states4_per_party: &[Vec<[AuthGlWire; 4]>],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    pending: &mut SpdzGoldilocksPendingChecks,
) -> Result<Vec<Vec<[AuthGlWire; 32]>>, PreprocessError> {
    let m = quorum_pts.len();
    let batch = states4_per_party[0].len();
    let num_lanes = 4 * batch;
    if num_lanes == 0 {
        return Ok(vec![Vec::new(); m]);
    }

    // 1. Pop 1 `CanonicalBitMask64Share` (`r < p`) per lane and open `z = (x - r) mod p`
    let mut r_bits_p: SecretBuffer<Vec<Vec<[AuthGlWire; 64]>>> =
        SecretBuffer(vec![Vec::with_capacity(num_lanes); m]);
    let mut z_wires = SecretBuffer(vec![Vec::with_capacity(num_lanes); m]);
    for p in 0..m {
        for st4 in &states4_per_party[p][..batch] {
            for lane_wire in st4 {
                let mask = vaults[p].pop_a2b_mask()?;
                let r_sum = AuthGlWire {
                    val: mask.field_sum_share,
                    mac: mask.field_sum_mac,
                };
                z_wires[p].push(lane_wire.sub(r_sum));
                let rb: [AuthGlWire; 64] = core::array::from_fn(|bit| AuthGlWire {
                    val: mask.bit_shares[bit],
                    mac: mask.bit_macs[bit],
                });
                r_bits_p[p].push(rb);
            }
        }
    }

    pending.record_batch(&z_wires);

    let mut z_pub = Vec::with_capacity(num_lanes);
    let mut sh_buf = SecretBuffer(vec![Goldilocks::ZERO; m]);
    for idx in 0..num_lanes {
        for (buf, wires) in sh_buf.iter_mut().zip(z_wires.iter()) {
            *buf = wires[idx].val;
        }
        let z_f = open_and_check_degree_goldilocks(t, quorum_pts, &sh_buf, "pos2_a2b_z")?;
        z_pub.push(z_f.to_canonical_u64());
    }
    drop(sh_buf);

    // 2. Run dual 64-bit public+secret ripple adders in lockstep across all `num_lanes`:
    //    Adder A: `z + r` -> sum bits `u_bits[0..64]`
    //    Adder B: `(z + 2^32 - 1) + r` -> sum bits `v_bits[0..64]`, carry `c_b` (`c_b == 1 iff z + r >= p`)
    let mut u_bits_p = SecretBuffer(vec![vec![[AuthGlWire::ZERO; 64]; num_lanes]; m]);
    let mut v_bits_p = SecretBuffer(vec![vec![[AuthGlWire::ZERO; 64]; num_lanes]; m]);
    let mut carry_a_p = SecretBuffer(vec![vec![AuthGlWire::ZERO; num_lanes]; m]);
    let mut carry_b_p = SecretBuffer(vec![vec![AuthGlWire::ZERO; num_lanes]; m]);

    // Bit 0 (`carry_in == 0`, 0 Beaver triples!)
    for p in 0..m {
        let alpha_p = vaults[p].mac_alpha_share;
        let one_c = AuthGlWire::public_const(Goldilocks::ONE, alpha_p);
        for idx in 0..num_lanes {
            let za0 = (z_pub[idx] & 1) == 1;
            let zb0 = ((z_pub[idx] + GOLDILOCKS_EPSILON) & 1) == 1;
            let r0 = r_bits_p[p][idx][0];
            if za0 {
                u_bits_p[p][idx][0] = one_c.sub(r0);
                carry_a_p[p][idx] = r0;
            } else {
                u_bits_p[p][idx][0] = r0;
                carry_a_p[p][idx] = AuthGlWire::ZERO;
            }
            if zb0 {
                v_bits_p[p][idx][0] = one_c.sub(r0);
                carry_b_p[p][idx] = r0;
            } else {
                v_bits_p[p][idx][0] = r0;
                carry_b_p[p][idx] = AuthGlWire::ZERO;
            }
        }
    }

    // Bits 1..64 (`2 * num_lanes` Beaver multiplications per bit position across all lanes in parallel)
    for bit in 1..64 {
        let mut mul_x = SecretBuffer(vec![Vec::with_capacity(2 * num_lanes); m]);
        let mut mul_y = SecretBuffer(vec![Vec::with_capacity(2 * num_lanes); m]);
        for p in 0..m {
            for idx in 0..num_lanes {
                let rk = r_bits_p[p][idx][bit];
                mul_x[p].push(rk);
                mul_y[p].push(carry_a_p[p][idx]);
                mul_x[p].push(rk);
                mul_y[p].push(carry_b_p[p][idx]);
            }
        }
        let prods = SecretBuffer(eval_spdz_beaver_mul_batch(
            t, quorum_pts, &mul_x, &mul_y, vaults, pending,
        )?);
        for p in 0..m {
            let alpha_p = vaults[p].mac_alpha_share;
            let one_c = AuthGlWire::public_const(Goldilocks::ONE, alpha_p);
            for idx in 0..num_lanes {
                let rk = r_bits_p[p][idx][bit];
                let ca = carry_a_p[p][idx];
                let cb = carry_b_p[p][idx];
                let pa = prods[p][2 * idx];
                let pb = prods[p][2 * idx + 1];

                let za = ((z_pub[idx] >> bit) & 1) == 1;
                if za {
                    // u_k = 1 - r_k - c_a + 2 * (r_k * c_a), c_a' = r_k + c_a - (r_k * c_a)
                    u_bits_p[p][idx][bit] = one_c.sub(rk).sub(ca).add(pa.scale(Goldilocks::TWO));
                    carry_a_p[p][idx] = rk.add(ca).sub(pa);
                } else {
                    // u_k = r_k + c_a - 2 * (r_k * c_a), c_a' = r_k * c_a
                    u_bits_p[p][idx][bit] = rk.add(ca).sub(pa.scale(Goldilocks::TWO));
                    carry_a_p[p][idx] = pa;
                }

                let zb = (((z_pub[idx] + GOLDILOCKS_EPSILON) >> bit) & 1) == 1;
                if zb {
                    v_bits_p[p][idx][bit] = one_c.sub(rk).sub(cb).add(pb.scale(Goldilocks::TWO));
                    carry_b_p[p][idx] = rk.add(cb).sub(pb);
                } else {
                    v_bits_p[p][idx][bit] = rk.add(cb).sub(pb.scale(Goldilocks::TWO));
                    carry_b_p[p][idx] = pb;
                }
            }
        }
    }

    // 3. Mux all 64 bits in 1 batched Beaver round: `x_k = u_k + c_b * (v_k - u_k)`
    let mut mux_x = SecretBuffer(vec![Vec::with_capacity(64 * num_lanes); m]);
    let mut mux_y = SecretBuffer(vec![Vec::with_capacity(64 * num_lanes); m]);
    for p in 0..m {
        for idx in 0..num_lanes {
            let cb = carry_b_p[p][idx];
            for bit in 0..64 {
                mux_x[p].push(cb);
                mux_y[p].push(v_bits_p[p][idx][bit].sub(u_bits_p[p][idx][bit]));
            }
        }
    }
    let mux_prods = SecretBuffer(eval_spdz_beaver_mul_batch(
        t, quorum_pts, &mux_x, &mux_y, vaults, pending,
    )?);

    // 4. Pack canonical big-endian bytes `to_be_bytes()` (`byte 0` = bits `56..64`, ..., `byte 7` = bits `0..8`)
    let mut out_bytes_p = SecretBuffer(vec![Vec::with_capacity(batch); m]);
    for p in 0..m {
        for item in 0..batch {
            let mut bytes32 = [AuthGlWire::ZERO; 32];
            for lane in 0..4 {
                let idx = 4 * item + lane;
                for byte_in_lane in 0..8 {
                    let bit_lo = 8 * (7 - byte_in_lane);
                    let mut acc = AuthGlWire::ZERO;
                    let mut pow2 = Goldilocks::ONE;
                    for b in 0..8 {
                        let bit = bit_lo + b;
                        let x_bit = u_bits_p[p][idx][bit].add(mux_prods[p][64 * idx + bit]);
                        acc = acc.add(x_bit.scale(pow2));
                        pow2 = pow2 + pow2;
                    }
                    bytes32[8 * lane + byte_in_lane] = acc;
                }
            }
            out_bytes_p[p].push(bytes32);
        }
    }
    Ok(core::mem::take(&mut out_bytes_p.0))
}

/// Publicly opened cut-boundary values: `(4-lane digests as 32 bytes, extra canonical byte blocks)`.
type CutOpenings = (Vec<[u8; 32]>, Vec<[u8; 32]>);

/// Strictly verify ALL queued intermediate SPDZ wires AND open a batch of cut-boundary 4-lane
/// digests (`[u8; 32]` via `Goldilocks::to_be_bytes()`) using committed zero-masked SPDZ `MacCheck`.
///
/// If any wire or cut digest fails commitment, degree-`< t`, or `GoldilocksExt2` `MacCheck`,
/// immediately burns (`poison_and_wipe()`) all key shares and preprocessing vaults!
#[expect(
    clippy::too_many_arguments,
    reason = "One cut-boundary opening: transcript context, quorum, both cut batches, pending checks and per-party state"
)]
fn flush_verify_and_open_cut_states4(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    quorum_pts: &[Goldilocks],
    cut_states4_per_party: &[Vec<[AuthGlWire; 4]>],
    extra_cut_bytes_per_party: &[Vec<[AuthGlWire; 32]>],
    pending: &mut SpdzGoldilocksPendingChecks,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<CutOpenings, Poseidon2MpcError> {
    let m = quorum_pts.len();
    let num_states = cut_states4_per_party[0].len();
    let num_byte_blocks = extra_cut_bytes_per_party[0].len();
    let pend_len = pending.shares_per_party[0].len();
    // Intermediate openings must authenticate before any unmasked cut share is copied.
    let alpha = SecretBuffer(vaults.iter().map(|v| v.mac_alpha_share).collect::<Vec<_>>());
    let intermediate = commit_and_open_spdz_goldilocks_batch_quorum(
        session_id,
        "pre_cut_intermediate_mac",
        t,
        quorum_pts,
        &pending.shares_per_party,
        &pending.macs_per_party,
        &alpha,
        party_rngs,
    );
    pending.clear_and_wipe();
    match intermediate {
        Ok(mut values) => wipe_goldilocks(&mut values),
        Err(e) => {
            poison_all_on_abort(key_shares, vaults);
            return Err(Poseidon2MpcError::Preprocess(e));
        }
    }
    let _ = pend_len;
    let pend_len = 0;
    let total_wires = 4 * num_states + 32 * num_byte_blocks;

    let mut all_sh = SecretBuffer(vec![Vec::with_capacity(total_wires); m]);
    let mut all_mac = SecretBuffer(vec![Vec::with_capacity(total_wires); m]);
    let mut alpha_sh = SecretBuffer(Vec::with_capacity(m));
    for p in 0..m {
        alpha_sh.push(vaults[p].mac_alpha_share);
        for st in &cut_states4_per_party[p] {
            for w in st {
                all_sh[p].push(w.val);
                all_mac[p].push(w.mac);
            }
        }
        for blk in &extra_cut_bytes_per_party[p] {
            for w in blk {
                all_sh[p].push(w.val);
                all_mac[p].push(w.mac);
            }
        }
    }
    pending.clear_and_wipe();

    let opened_res = commit_and_open_spdz_goldilocks_batch_quorum(
        session_id, phase, t, quorum_pts, &all_sh, &all_mac, &alpha_sh, party_rngs,
    );
    drop(all_sh);
    drop(all_mac);
    drop(alpha_sh);

    let opened = SecretBuffer(match opened_res {
        Ok(v) => v,
        Err(e) => {
            poison_all_on_abort(key_shares, vaults);
            return Err(Poseidon2MpcError::Preprocess(e));
        }
    });

    let mut out_digests = Vec::with_capacity(num_states);
    for s in 0..num_states {
        let base = pend_len + 4 * s;
        let mut d32 = [0u8; 32];
        for lane in 0..4 {
            d32[8 * lane..8 * (lane + 1)].copy_from_slice(&opened[base + lane].to_be_bytes());
        }
        out_digests.push(d32);
    }

    let mut out_extra = Vec::with_capacity(num_byte_blocks);
    let extra_base = pend_len + 4 * num_states;
    for blk in 0..num_byte_blocks {
        let mut b32 = [0u8; 32];
        for b in 0..32 {
            let v = opened[extra_base + 32 * blk + b].to_canonical_u64();
            if v > 255 {
                poison_all_on_abort(key_shares, vaults);
                return Err(Poseidon2MpcError::Preprocess(
                    PreprocessError::NonBooleanBitDetected { phase },
                ));
            }
            b32[b] = v as u8;
        }
        out_extra.push(b32);
    }

    Ok((out_digests, out_extra))
}

fn validate_quorum_slices(
    t: usize,
    key_shares: &[&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &[&mut PreprocessedPoseidonPartyVault],
    party_rngs: &[PartyPrivateRng],
) -> Result<([u8; 32], Vec<Goldilocks>), Poseidon2MpcError> {
    let m = key_shares.len();
    if t < 2 || m < t || vaults.len() != m || party_rngs.len() != m {
        return Err(Poseidon2MpcError::InvalidQuorum { t, n: m });
    }
    let pk_seed = key_shares[0].pk_seed;
    let n = key_shares[0].committee_size;
    if m > n
        || key_shares
            .iter()
            .any(|ks| ks.committee_size != n || ks.party_id >= n)
    {
        return Err(Poseidon2MpcError::InvalidQuorum { t, n: m });
    }
    let mut pts = Vec::with_capacity(m);
    for p in 0..m {
        if key_shares[p].poisoned || vaults[p].is_poisoned() {
            return Err(Poseidon2MpcError::KeySharePoisoned {
                party_id: key_shares[p].party_id,
            });
        }
        if !ct_eq_bytes32(&key_shares[p].pk_seed, &pk_seed)
            || key_shares[p].eval_point != vaults[p].eval_point
        {
            return Err(Poseidon2MpcError::PublicSeedMismatch);
        }
        pts.push(key_shares[p].eval_point);
    }
    validate_all_eval_points_goldilocks(&pts)?;
    Ok((pk_seed, pts))
}

#[inline]
fn key_seed_wires(ks: &Poseidon2SpdzAuthenticatedKeyShare) -> [AuthGlWire; 32] {
    core::array::from_fn(|i| AuthGlWire {
        val: ks.sk_seed_bytes[i],
        mac: ks.sk_seed_macs[i],
    })
}

#[inline]
fn key_prf_wires(ks: &Poseidon2SpdzAuthenticatedKeyShare) -> [AuthGlWire; 32] {
    core::array::from_fn(|i| AuthGlWire {
        val: ks.sk_prf_bytes[i],
        mac: ks.sk_prf_macs[i],
    })
}

/// Evaluate all WOTS+C chains for a batch of `(layer, tree, kp, chain_idx, steps)` targets in MPC:
/// - `steps == 0`: `th_secret_prf` directly produces the cut-boundary `st[0..4]` (`0` A2B needed!);
/// - `steps >= 1`: intermediate unrevealed steps convert `st[0..4]` -> `[bytes32]` via
///   [`eval_spdz_canonical_a2b_state4_batch_to_bytes32`], and ONLY the final step `steps - 1`
///   lands at the cut boundary!
#[expect(
    clippy::too_many_arguments,
    reason = "One MPC phase: transcript context, quorum, public seed, chain targets and per-party state"
)]
fn eval_wots_chains_mpc_cut(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    quorum_pts: &[Goldilocks],
    pk_seed: &[u8; 32],
    targets: &[(u32, u64, u32, u32, usize)],
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<[u8; 32]>, Poseidon2MpcError> {
    let m = quorum_pts.len();
    let count = targets.len();
    if count == 0 {
        return Ok(Vec::new());
    }
    let mut pending = SpdzGoldilocksPendingChecks::new(m);

    // Step 0: derive WOTS secret base `th_secret_prf(TAG_PRF, pk_seed, sk_seed, adrs)` for all targets
    let mut prf_tmpls = Vec::with_capacity(count);
    for &(layer, tree, kp, ch_idx, _) in targets {
        let adrs = HashAdrs {
            layer,
            tree,
            kind: AdrsKind::WotsPrf,
            key_pair: kp,
            chain_idx: ch_idx,
            hash_step: 0,
        };
        prf_tmpls.push(build_single_secret32_template(TAG_PRF, pk_seed, &adrs));
    }
    let mut prf_secrets = SecretBuffer(vec![Vec::with_capacity(count); m]);
    for p in 0..m {
        let seed_w = SecretBuffer(key_seed_wires(key_shares[p]));
        for _ in 0..count {
            prf_secrets[p].push(*seed_w);
        }
    }

    let mut cur_states = SecretBuffer(
        match eval_spdz_poseidon2_hash32_templates(
            t,
            quorum_pts,
            &prf_tmpls,
            &prf_secrets,
            vaults,
            &mut pending,
        ) {
            Ok(s) => s,
            Err(e) => {
                poison_all_on_abort(key_shares, vaults);
                return Err(Poseidon2MpcError::Preprocess(e));
            }
        },
    );

    let max_steps = targets.iter().map(|x| x.4).max().unwrap_or(0);
    for step in 0..max_steps {
        let active: Vec<usize> = (0..count).filter(|&i| step < targets[i].4).collect();
        let mut active_st = SecretBuffer(vec![Vec::with_capacity(active.len()); m]);
        for p in 0..m {
            for &i in &active {
                active_st[p].push(cur_states[p][i]);
            }
        }
        let active_bytes = SecretBuffer(
            match eval_spdz_canonical_a2b_state4_batch_to_bytes32(
                t,
                quorum_pts,
                &active_st,
                vaults,
                &mut pending,
            ) {
                Ok(b) => b,
                Err(e) => {
                    poison_all_on_abort(key_shares, vaults);
                    return Err(Poseidon2MpcError::Preprocess(e));
                }
            },
        );

        let mut step_tmpls = Vec::with_capacity(active.len());
        for &i in &active {
            let (layer, tree, kp, ch_idx, _) = targets[i];
            let adrs = HashAdrs {
                layer,
                tree,
                kind: AdrsKind::WotsHash,
                key_pair: kp,
                chain_idx: ch_idx,
                hash_step: step as u32,
            };
            step_tmpls.push(build_single_secret32_template(TAG_TH_F, pk_seed, &adrs));
        }

        let next_st = SecretBuffer(
            match eval_spdz_poseidon2_hash32_templates(
                t,
                quorum_pts,
                &step_tmpls,
                &active_bytes,
                vaults,
                &mut pending,
            ) {
                Ok(s) => s,
                Err(e) => {
                    poison_all_on_abort(key_shares, vaults);
                    return Err(Poseidon2MpcError::Preprocess(e));
                }
            },
        );

        for p in 0..m {
            for (slot, &i) in active.iter().enumerate() {
                cur_states[p][i] = next_st[p][slot];
            }
        }
    }

    let empty_extra = vec![Vec::new(); m];
    let (digests, _) = flush_verify_and_open_cut_states4(
        session_id,
        phase,
        t,
        quorum_pts,
        &cur_states,
        &empty_extra,
        &mut pending,
        key_shares,
        vaults,
        party_rngs,
    )?;
    Ok(digests)
}

/// Evaluate every WOTS+C chain of subtree `(layer, tree)` to full depth in MPC and compress each
/// key pair's endpoints into its public leaf digest.
#[expect(
    clippy::too_many_arguments,
    reason = "One MPC phase: transcript context, parameters, quorum, subtree address and per-party state"
)]
fn compute_subtree_wots_pks_mpc(
    session_id: &[u8; 32],
    phase: &'static str,
    params: &PqHashParams,
    t: usize,
    quorum_pts: &[Goldilocks],
    pk_seed: &[u8; 32],
    layer_u32: u32,
    tree_idx: u64,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<[u8; 32]>, Poseidon2MpcError> {
    let sub_leaves = 1usize << params.subtree_height;
    let steps = params.w - 1;
    let mut targets = Vec::with_capacity(sub_leaves * params.ell1);
    for kp in 0..sub_leaves {
        for r in 0..params.ell1 {
            targets.push((layer_u32, tree_idx, kp as u32, r as u32, steps));
        }
    }
    let endpoints = eval_wots_chains_mpc_cut(
        session_id, phase, t, quorum_pts, pk_seed, &targets, key_shares, vaults, party_rngs,
    )?;
    let mut leaves = Vec::with_capacity(sub_leaves);
    for kp in 0..sub_leaves {
        let slice = &endpoints[kp * params.ell1..(kp + 1) * params.ell1];
        let pk_adrs = HashAdrs {
            layer: layer_u32,
            tree: tree_idx,
            kind: AdrsKind::WotsPk,
            key_pair: kp as u32,
            chain_idx: 0,
            hash_step: 0,
        };
        leaves.push(th_tweak_tl(Poseidon2Suite, pk_seed, &pk_adrs, slice));
    }
    Ok(leaves)
}

/// Count the same padded sponge blocks as the online evaluator, including framing.
fn template_permutations(template: &(Vec<u8>, usize)) -> usize {
    let mut limbs = bytes_to_limbs56(&template.0);
    poseidon2_pad(&mut limbs);
    limbs.len() / 8
}

fn chain_template_permutations() -> (usize, usize) {
    let prf = build_single_secret32_template(TAG_PRF, &[0; 32], &HashAdrs::ZERO);
    let step = build_single_secret32_template(TAG_TH_F, &[0; 32], &HashAdrs::ZERO);
    (template_permutations(&prf), template_permutations(&step))
}

/// Compute exact preprocessing tuple budget `(num_pow7, num_beaver, num_a2b)` required by
/// [`build_distributed_poseidon2_key`].
pub fn required_poseidon2_keygen_preprocessing_budget(
    params: &PqHashParams,
) -> (usize, usize, usize) {
    let sub_leaves = 1usize << params.subtree_height;
    let chains = sub_leaves * params.ell1;
    let steps = params.w.saturating_sub(1);
    let (prf_perms, step_perms) = chain_template_permutations();
    let perms_per_chain = prf_perms + steps * step_perms;
    let num_pow7 = chains * perms_per_chain * POSEIDON2_SBOXES_PER_PERM;
    let num_a2b_hashes = chains * steps;
    (
        num_pow7,
        num_a2b_hashes * POSEIDON2_BEAVER_PER_A2B_HASH32,
        num_a2b_hashes * 4,
    )
}

/// Compute exact preprocessing tuple budget `(num_pow7, num_beaver, num_a2b)` required by one
/// [`sign_jorts_poseidon2_mpc`] or [`sign_stateless_tsw_poseidon2_mpc`] signature.
pub fn required_poseidon2_sign_preprocessing_budget(
    params: &PqHashParams,
) -> (usize, usize, usize) {
    sign_preprocessing_budget(params, false)
}

/// Preprocessing tuple budget `(num_pow7, num_beaver, num_a2b)` sufficient for one signature made
/// with a top-subtree leaf cache ([`sign_jorts_poseidon2_mpc_cached`],
/// [`retry_jorts_poseidon2_mpc_cached`] or [`sign_stateless_tsw_poseidon2_mpc_cached`]
/// with `Some(cache)`).
///
/// It is smaller than [`required_poseidon2_sign_preprocessing_budget`] by exactly one
/// [`required_poseidon2_keygen_preprocessing_budget`]: the top subtree's `2^subtree_height * ell1`
/// full-depth chains are not evaluated.
pub fn required_poseidon2_sign_preprocessing_budget_cached(
    params: &PqHashParams,
) -> (usize, usize, usize) {
    sign_preprocessing_budget(params, true)
}

fn sign_preprocessing_budget(
    params: &PqHashParams,
    top_subtree_cached: bool,
) -> (usize, usize, usize) {
    let sub_leaves = 1usize << params.subtree_height;
    let steps_max = params.w.saturating_sub(1);
    let fors_leaves = if params.stateful {
        0
    } else {
        params.fors_trees * (1usize << params.fors_height)
    };
    // With a top-subtree leaf cache the top layer evaluates only its `ell1` signing chains.
    let mpc_subtrees = params
        .num_layers
        .saturating_sub(usize::from(top_subtree_cached));
    let hypertree_chains =
        params.num_layers * params.ell1 + mpc_subtrees * sub_leaves * params.ell1;
    let (prf_perms, step_perms) = chain_template_permutations();
    let opt_domain = if params.stateful {
        build_stateful_det_opt_domain(0, &[0; 32])
    } else {
        build_stateless_det_opt_domain(&[0; 32])
    };
    let randomizer_perms = template_permutations(&build_prf_msg_template(&opt_domain, &[0; 32]));
    let total_perms = randomizer_perms
        + fors_leaves * (prf_perms + step_perms)
        + hypertree_chains * (prf_perms + steps_max * step_perms);
    let total_a2b_hashes = fors_leaves + hypertree_chains * steps_max;
    (
        total_perms * POSEIDON2_SBOXES_PER_PERM,
        total_a2b_hashes * POSEIDON2_BEAVER_PER_A2B_HASH32,
        total_a2b_hashes * 4,
    )
}

/// Build the distributed `PqPublicKey` (`pk_seed`, `pk_root`) over `Poseidon2Suite` via dishonest-
/// majority SPDZ MPC without ever reconstructing `SK.seed` or `SK.prf`.
pub fn build_distributed_poseidon2_key(
    session_id: [u8; 32],
    params: &PqHashParams,
    t: usize,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<PqPublicKey, Poseidon2MpcError> {
    build_distributed_poseidon2_key_cached(session_id, params, t, key_shares, vaults, party_rngs)
        .map(|cache| cache.pk)
}

/// [`build_distributed_poseidon2_key`], additionally keeping the top subtree's public leaf digests.
///
/// The returned [`DkgCachedSubtrees`] holds the `2^subtree_height` WOTS+C public-key digests of
/// subtree `(layer = num_layers - 1, tree = 0)` together with the public key they hash to. Passing
/// it to the `_cached` signing functions lets a signature skip recomputing that subtree in MPC.
pub fn build_distributed_poseidon2_key_cached(
    session_id: [u8; 32],
    params: &PqHashParams,
    t: usize,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<DkgCachedSubtrees, Poseidon2MpcError> {
    if !params.is_well_formed() {
        return Err(Poseidon2MpcError::InvalidParams);
    }
    let (pk_seed, quorum_pts) = validate_quorum_slices(t, key_shares, vaults, party_rngs)?;
    let first_enrolled = key_shares[0].enrolled_profile;
    for ks in key_shares.iter().skip(1) {
        match (first_enrolled, ks.enrolled_profile) {
            (None, None) => {}
            (Some((p0, k0)), Some((pi, ki)))
                if p0 == pi
                    && ct_eq_bytes32(&k0.pk_seed, &ki.pk_seed)
                    && ct_eq_bytes32(&k0.pk_root, &ki.pk_root) => {}
            _ => return Err(Poseidon2MpcError::KeyProfileMismatch),
        }
    }
    if let Some((ep, _)) = first_enrolled
        && ep != *params
    {
        return Err(Poseidon2MpcError::KeyProfileMismatch);
    }
    let top_layer = (params.num_layers - 1) as u32;
    let top_leaves = compute_subtree_wots_pks_mpc(
        &session_id,
        "pos2_keygen_top_leaves",
        params,
        t,
        &quorum_pts,
        &pk_seed,
        top_layer,
        0,
        key_shares,
        vaults,
        party_rngs,
    )?;
    let (pk_root, _) = build_merkle_from_leaves_topdown(
        Poseidon2Suite,
        &pk_seed,
        top_layer,
        0,
        AdrsKind::Tree,
        0,
        &top_leaves,
        params.subtree_height,
        0,
        0,
    );
    let pk = PqPublicKey { pk_seed, pk_root };
    for ks in key_shares.iter_mut() {
        ks.enroll_key_profile(*params, pk)?;
    }
    Ok(DkgCachedSubtrees {
        top_layer,
        top_leaves,
        pk,
    })
}

/// Check that an optional top-subtree leaf cache belongs to `(params, pk)`.
///
/// The cache is public data from the caller, so it is accepted only if it names the top layer,
/// carries this public key, has `2^subtree_height` leaves, and those leaves hash to `pk_root`.
/// Runs before any epoch is latched or any preprocessing is consumed.
fn validate_top_subtree_cache(
    params: &PqHashParams,
    pk: &PqPublicKey,
    cache: Option<&DkgCachedSubtrees>,
) -> Result<(), Poseidon2MpcError> {
    let Some(cache) = cache else {
        return Ok(());
    };
    let top_layer = (params.num_layers - 1) as u32;
    if cache.top_layer != top_layer
        || cache.pk != *pk
        || cache.top_leaves.len() != 1usize << params.subtree_height
    {
        return Err(Poseidon2MpcError::CachedSubtreeMismatch);
    }
    let (root, _) = build_merkle_from_leaves_topdown(
        Poseidon2Suite,
        &pk.pk_seed,
        top_layer,
        0,
        AdrsKind::Tree,
        0,
        &cache.top_leaves,
        params.subtree_height,
        0,
        0,
    );
    if root != pk.pk_root {
        return Err(Poseidon2MpcError::CachedSubtreeMismatch);
    }
    Ok(())
}

#[expect(
    clippy::too_many_arguments,
    reason = "One signature: transcript context, parameters, public key, optional leaf cache, message inputs and per-party state"
)]
fn sign_hypertree_poseidon2_mpc_core(
    session_id: &[u8; 32],
    params: &PqHashParams,
    pk: &PqPublicKey,
    cache: Option<&DkgCachedSubtrees>,
    t: usize,
    quorum_pts: &[Goldilocks],
    mu: &[u8; 32],
    r_rand: [u8; 32],
    leaf_global_idx: usize,
    fors_idxs: Option<&[usize]>,
    max_grind: u32,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<PqHashSig, Poseidon2MpcError> {
    let m = quorum_pts.len();
    let sub_leaves = 1usize << params.subtree_height;
    if cache.is_some_and(|c| c.top_layer as usize != params.num_layers - 1) {
        return Err(Poseidon2MpcError::CachedSubtreeMismatch);
    }

    let (fors_openings, mut cur_root) = if params.stateful {
        (Vec::new(), *mu)
    } else {
        let idxs = fors_idxs.ok_or(Poseidon2MpcError::InvalidParams)?;
        let kp0 = (leaf_global_idx % sub_leaves) as u32;
        let tree0 = (leaf_global_idx / sub_leaves) as u64;
        let fors_leaf_count = 1usize << params.fors_height;
        let total_fors = params.fors_trees * fors_leaf_count;

        let mut pending = SpdzGoldilocksPendingChecks::new(m);
        let mut prf_tmpls = Vec::with_capacity(total_fors);
        let mut f_tmpls = Vec::with_capacity(total_fors);
        for j in 0..params.fors_trees {
            for u in 0..fors_leaf_count {
                let prf_adrs = HashAdrs {
                    layer: 0,
                    tree: tree0,
                    kind: AdrsKind::ForsPrf,
                    key_pair: kp0,
                    chain_idx: j as u32,
                    hash_step: u as u32,
                };
                prf_tmpls.push(build_single_secret32_template(
                    TAG_PRF,
                    &pk.pk_seed,
                    &prf_adrs,
                ));
                let tree_adrs = HashAdrs {
                    layer: 0,
                    tree: tree0,
                    kind: AdrsKind::ForsTree,
                    key_pair: kp0,
                    chain_idx: j as u32,
                    hash_step: u as u32,
                };
                f_tmpls.push(build_single_secret32_template(
                    TAG_TH_F,
                    &pk.pk_seed,
                    &tree_adrs,
                ));
            }
        }
        let mut prf_secs = SecretBuffer(vec![Vec::with_capacity(total_fors); m]);
        for p in 0..m {
            let sw = SecretBuffer(key_seed_wires(key_shares[p]));
            for _ in 0..total_fors {
                prf_secs[p].push(*sw);
            }
        }
        let sec_states = SecretBuffer(
            match eval_spdz_poseidon2_hash32_templates(
                t,
                quorum_pts,
                &prf_tmpls,
                &prf_secs,
                vaults,
                &mut pending,
            ) {
                Ok(s) => s,
                Err(e) => {
                    poison_all_on_abort(key_shares, vaults);
                    return Err(Poseidon2MpcError::Preprocess(e));
                }
            },
        );

        // Convert ALL `total_fors` secret states to canonical byte shares via A2B so unrevealed
        // FORS leaves NEVER open `sec_states`, and open ONLY the `fors_trees` selected `secret_val`s
        // plus the `total_fors` public leaf hashes at the cut boundary!
        let sec_bytes = SecretBuffer(
            match eval_spdz_canonical_a2b_state4_batch_to_bytes32(
                t,
                quorum_pts,
                &sec_states,
                vaults,
                &mut pending,
            ) {
                Ok(b) => b,
                Err(e) => {
                    poison_all_on_abort(key_shares, vaults);
                    return Err(Poseidon2MpcError::Preprocess(e));
                }
            },
        );

        let leaf_states = match eval_spdz_poseidon2_hash32_templates(
            t,
            quorum_pts,
            &f_tmpls,
            &sec_bytes,
            vaults,
            &mut pending,
        ) {
            Ok(s) => s,
            Err(e) => {
                poison_all_on_abort(key_shares, vaults);
                return Err(Poseidon2MpcError::Preprocess(e));
            }
        };

        // Selected `fors_trees` revealed `secret_val` states are also cut-boundary digests!
        let mut cut_states = SecretBuffer(leaf_states);
        for p in 0..m {
            secret_vec_reserve(&mut cut_states[p], params.fors_trees);
            for (j, &idx_j) in idxs.iter().enumerate().take(params.fors_trees) {
                secret_vec_push(
                    &mut cut_states[p],
                    sec_states[p][j * fors_leaf_count + idx_j],
                );
            }
        }
        let empty_extra = vec![Vec::new(); m];
        let (opened_fors, _) = flush_verify_and_open_cut_states4(
            session_id,
            "pos2_fors_cut",
            t,
            quorum_pts,
            &cut_states,
            &empty_extra,
            &mut pending,
            key_shares,
            vaults,
            party_rngs,
        )?;

        let mut openings = Vec::with_capacity(params.fors_trees);
        let mut roots = Vec::with_capacity(params.fors_trees);
        for (j, &idx_j) in idxs.iter().enumerate().take(params.fors_trees) {
            let leaves_j = &opened_fors[j * fors_leaf_count..(j + 1) * fors_leaf_count];
            let revealed_sec = opened_fors[total_fors + j];
            let (root_j, path_j) = build_merkle_from_leaves_topdown(
                Poseidon2Suite,
                &pk.pk_seed,
                0,
                tree0,
                AdrsKind::ForsTree,
                kp0,
                leaves_j,
                params.fors_height,
                j,
                idx_j,
            );
            roots.push(root_j);
            openings.push(ForsTreeOpening {
                secret_val: revealed_sec,
                auth_path: path_j,
            });
        }
        let fors_pk_adrs = HashAdrs {
            layer: 0,
            tree: tree0,
            kind: AdrsKind::ForsRoots,
            key_pair: kp0,
            chain_idx: 0,
            hash_step: 0,
        };
        let fors_pk = th_tweak_tl(Poseidon2Suite, &pk.pk_seed, &fors_pk_adrs, &roots);
        (openings, fors_pk)
    };

    let mut layer_sigs = Vec::with_capacity(params.num_layers);
    let mut cur_global = leaf_global_idx;
    for layer_idx in 0..params.num_layers {
        let kp_idx = cur_global % sub_leaves;
        let tree_idx_nat = cur_global / sub_leaves;
        let tree_idx = tree_idx_nat as u64;
        let layer_u32 = layer_idx as u32;
        let kp_u32 = kp_idx as u32;

        // Public leaves of this layer's subtree, when the caller's cache covers it.
        let cached_leaves: Option<&[[u8; 32]]> = match cache {
            Some(c) if c.top_layer == layer_u32 => {
                if tree_idx != 0 || c.pk != *pk || c.top_leaves.len() != sub_leaves {
                    return Err(Poseidon2MpcError::CachedSubtreeMismatch);
                }
                Some(&c.top_leaves)
            }
            _ => None,
        };

        let (ctr, digits, _) = if params.stateful && layer_idx == 0 {
            grind_tsw_leaf_counter(
                Poseidon2Suite,
                params.w,
                params.ell1,
                params.target_sum(),
                &r_rand,
                &pk.pk_seed,
                &pk.pk_root,
                &cur_root,
                tree_idx,
                kp_u32,
                max_grind,
            )
            .ok_or(Poseidon2MpcError::TswGrindExhausted)?
        } else {
            grind_tsw_internal_counter(
                Poseidon2Suite,
                params.w,
                params.ell1,
                params.target_sum(),
                &pk.pk_seed,
                &pk.pk_root,
                &cur_root,
                layer_u32,
                tree_idx,
                kp_u32,
                max_grind,
            )
            .ok_or(Poseidon2MpcError::TswGrindExhausted)?
        };

        let mut sig_targets = Vec::with_capacity(params.ell1);
        for (r, &dr) in digits.iter().enumerate().take(params.ell1) {
            sig_targets.push((layer_u32, tree_idx, kp_u32, r as u32, dr));
        }
        let wots_chains = eval_wots_chains_mpc_cut(
            session_id,
            "pos2_layer_wots_sig",
            t,
            quorum_pts,
            &pk.pk_seed,
            &sig_targets,
            key_shares,
            vaults,
            party_rngs,
        )?;

        // Sibling leaves are public and static per `(layer, tree)`: a cached subtree needs no MPC
        // beyond the signing chains above.
        let computed_leaves;
        let subtree_leaves = match cached_leaves {
            Some(leaves) => leaves,
            None => {
                computed_leaves = compute_subtree_wots_pks_mpc(
                    session_id,
                    "pos2_layer_subtree_pks",
                    params,
                    t,
                    quorum_pts,
                    &pk.pk_seed,
                    layer_u32,
                    tree_idx,
                    key_shares,
                    vaults,
                    party_rngs,
                )?;
                &computed_leaves[..]
            }
        };
        let (next_root, auth_path) = build_merkle_from_leaves_topdown(
            Poseidon2Suite,
            &pk.pk_seed,
            layer_u32,
            tree_idx,
            AdrsKind::Tree,
            0,
            subtree_leaves,
            params.subtree_height,
            0,
            kp_idx,
        );
        layer_sigs.push(LayerXmssSig {
            tsw_ctr: ctr,
            wots_chains,
            auth_path,
        });
        cur_root = next_root;
        cur_global = tree_idx_nat;
    }

    let sig = PqHashSig {
        r_rand,
        leaf_global_idx,
        msg_tsw_ctr: 0,
        fors_openings,
        layer_sigs,
    };
    Ok(sig)
}

#[expect(
    clippy::too_many_arguments,
    reason = "One MPC phase: transcript context, quorum, PRF inputs and per-party state"
)]
fn eval_prf_msg_mpc_cut(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    quorum_pts: &[Goldilocks],
    opt_rand: &[u8],
    mu: &[u8; 32],
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<[u8; 32], Poseidon2MpcError> {
    let m = quorum_pts.len();
    let mut pending = SpdzGoldilocksPendingChecks::new(m);
    let tmpl = build_prf_msg_template(opt_rand, mu);
    let tmpls = [tmpl];
    let mut prf_secs = SecretBuffer(vec![Vec::with_capacity(1); m]);
    for p in 0..m {
        let pw = SecretBuffer(key_prf_wires(key_shares[p]));
        prf_secs[p].push(*pw);
    }
    let st4 = SecretBuffer(
        match eval_spdz_poseidon2_hash32_templates(
            t,
            quorum_pts,
            &tmpls,
            &prf_secs,
            vaults,
            &mut pending,
        ) {
            Ok(s) => s,
            Err(e) => {
                poison_all_on_abort(key_shares, vaults);
                return Err(Poseidon2MpcError::Preprocess(e));
            }
        },
    );
    let empty_extra = vec![Vec::new(); m];
    let (digests, _) = flush_verify_and_open_cut_states4(
        session_id,
        phase,
        t,
        quorum_pts,
        &st4,
        &empty_extra,
        &mut pending,
        key_shares,
        vaults,
        party_rngs,
    )?;
    Ok(digests[0])
}

fn validate_enrolled_key_profile(
    params: &PqHashParams,
    pk: &PqPublicKey,
    quorum_pk_seed: &[u8; 32],
    key_shares: &[&mut Poseidon2SpdzAuthenticatedKeyShare],
) -> Result<(), Poseidon2MpcError> {
    if !ct_eq_bytes32(&pk.pk_seed, quorum_pk_seed) {
        return Err(Poseidon2MpcError::PublicSeedMismatch);
    }
    for ks in key_shares {
        let Some((ep, epk)) = ks.enrolled_profile.as_ref() else {
            return Err(Poseidon2MpcError::KeyNotEnrolled);
        };
        if *ep != *params
            || !ct_eq_bytes32(&epk.pk_seed, &pk.pk_seed)
            || !ct_eq_bytes32(&epk.pk_root, &pk.pk_root)
        {
            return Err(Poseidon2MpcError::KeyProfileMismatch);
        }
    }
    Ok(())
}

fn resolve_enrolled_latch_authority<'a>(
    key_shares: &'a [&mut Poseidon2SpdzAuthenticatedKeyShare],
) -> Result<Option<&'a EpochLatchAuthorityPublic>, Poseidon2MpcError> {
    let first = key_shares[0].enrolled_latch_authority.as_ref();
    for ks in key_shares.iter().skip(1) {
        if ks.enrolled_latch_authority.as_ref() != first {
            return Err(Poseidon2MpcError::LatchCertificateRejected(
                QuorumLatchError::CertificateCommitteeMismatch,
            ));
        }
    }
    Ok(first)
}

/// Committee-wide latch gate of the stateful signers.
///
/// A one-time leaf may open for one message only, whichever `t` members sign. Local latches
/// enforce that among the members present; two signing sets that overlap only in corrupt members
/// could still each reserve the same epoch for a different message. So local latches are accepted
/// on their own only at full attendance (`signers == n`, where the set is itself a latch quorum:
/// `2n > n + (t - 1)`), and any smaller signing set must present a certificate that a quorum `q`
/// with `2q > n + (t - 1)` reserved exactly this `(key, epoch, mu)` under the committee's pinned
/// [`EpochLatchAuthorityPublic`].
///
/// Reads public values only and changes nothing.
#[expect(
    clippy::too_many_arguments,
    reason = "Latch authorization binds public key, committee threshold, attendance, pinned authority, certificate, epoch and message digest"
)]
fn check_committee_latch_authorisation(
    pk: &PqPublicKey,
    t: usize,
    n: usize,
    signers: usize,
    pinned_authority: Option<&EpochLatchAuthorityPublic>,
    latch_cert: Option<&EpochLatchCertificate>,
    epoch: u64,
    mu: &[u8; 32],
) -> Result<(), Poseidon2MpcError> {
    match latch_cert {
        Some(cert) => {
            let binding = epoch_latch_binding(&pk.pk_seed, &pk.pk_root, epoch, mu);
            if let Some(authority) = pinned_authority {
                cert.verify_against(authority, n, t, epoch, &binding)
                    .map_err(Poseidon2MpcError::LatchCertificateRejected)
            } else {
                cert.verify_for(n, t, epoch, &binding)
                    .map_err(Poseidon2MpcError::LatchCertificateRejected)?;
                Err(Poseidon2MpcError::LatchCertificateRejected(
                    QuorumLatchError::CertificateCommitteeMismatch,
                ))
            }
        }
        None if signers == n && latch_quorum_intersects_honestly(signers, n, t) => Ok(()),
        None => Err(Poseidon2MpcError::LatchCertificateRequired {
            signers,
            committee: n,
        }),
    }
}

/// Pick the epoch of a new stateful signature and reserve it in every signer's latch.
///
/// With a certificate the epoch is the certified one; a signer whose latch is behind skips
/// forward to it, and one already holding `(epoch, mu)` in flight keeps it. Without a certificate
/// (full attendance only) the epoch is the next epoch of the latches, which must all agree.
///
/// Every check runs before the first latch moves: a missing or rejected certificate, latches
/// that disagree, a latch already past the epoch or holding it for another digest, and an
/// exhausted key all return with every latch unchanged. The only way to return an error after
/// some latches moved is a durable latch failing to persist in the second pass; the latches
/// before it in the slice then hold `(epoch, mu)`, which is the reservation the gate authorised
/// and is accepted again when the same certificate is presented.
#[expect(
    clippy::too_many_arguments,
    reason = "Epoch reservation checks parameters, public key, threshold, pinned authority, certificate, latches and message digest"
)]
fn reserve_authorised_epoch<L: StatefulEpochLatch>(
    params: &PqHashParams,
    pk: &PqPublicKey,
    t: usize,
    n: usize,
    pinned_authority: Option<&EpochLatchAuthorityPublic>,
    latch_cert: Option<&EpochLatchCertificate>,
    latches: &mut [&mut L],
    mu: &[u8; 32],
) -> Result<u64, Poseidon2MpcError> {
    let Some(first) = latches.first() else {
        return Err(Poseidon2MpcError::InvalidQuorum { t, n: 0 });
    };
    let epoch = match latch_cert {
        Some(cert) => cert.epoch(),
        None => first.peek_next_epoch(),
    };
    check_committee_latch_authorisation(
        pk,
        t,
        n,
        latches.len(),
        pinned_authority,
        latch_cert,
        epoch,
        mu,
    )?;
    if latch_cert.is_none() && latches.iter().any(|l| l.peek_next_epoch() != epoch) {
        return Err(Poseidon2MpcError::EpochLatch(
            EpochLatchError::LatchesDisagree,
        ));
    }
    for l in latches.iter() {
        l.check_reserve_epoch_at(epoch, params.max_sigs_log2, mu)?;
    }
    for l in latches.iter_mut() {
        l.reserve_epoch_at(epoch, params.max_sigs_log2, mu)?;
    }
    Ok(epoch)
}

/// Sign a message under stateful `JortsPoseidon2` via dishonest-majority $t$-of-$n$ Shamir SPDZ:
/// - Requires committee-wide latch authorisation for `mu = H_pre(pk_seed, pk_root, msg)`: either
///   all `n` members sign (then `latch_cert` may be `None`), or `latch_cert` certifies that a
///   quorum `q` with `2q > n + (t - 1)` reserved this `(key, epoch, mu)`. Fewer than `n` signers
///   without a certificate get [`Poseidon2MpcError::LatchCertificateRequired`]; a certificate
///   for another committee, key, epoch or message gets
///   [`Poseidon2MpcError::LatchCertificateRejected`]. Both are returned before any latch moves
///   and before any share or preprocessing is used;
/// - Reserves the epoch in EVERY participating party's non-clonable [`StatefulEpochLatch`]
///   BEFORE any secret MPC wire is opened (all latches are checked first, so a latch that cannot
///   take the epoch leaves the others where they were);
/// - Derives `r_rand = PRF_msg(SK.prf, build_stateful_det_opt_domain(epoch, pk_seed), mu)` in SPDZ;
/// - Evaluates the hypertree WOTS+C chains and verifies `verify_pq_hash_sig` before returning.
///
/// Availability is that of the latch quorum: `floor((n + t - 1) / 2) + 1` members must
/// acknowledge every signature, which for `(t, n) = (2, 3)` is all three.
#[expect(
    clippy::too_many_arguments,
    reason = "One signing session: parameters, public key, committee latch certificate, quorum latches, message and per-party state"
)]
pub fn sign_jorts_poseidon2_mpc<L: StatefulEpochLatch>(
    session_id: [u8; 32],
    params: &PqHashParams,
    pk: &PqPublicKey,
    t: usize,
    latch_cert: Option<&EpochLatchCertificate>,
    latches: &mut [&mut L],
    msg: &[u8],
    max_grind: u32,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(u64, PqHashSig), Poseidon2MpcError> {
    sign_jorts_poseidon2_mpc_cached(
        session_id, params, pk, None, t, latch_cert, latches, msg, max_grind, key_shares, vaults,
        party_rngs,
    )
}

/// [`sign_jorts_poseidon2_mpc`] with an optional top-subtree leaf cache.
///
/// With `Some(cache)` the top layer's Merkle root and authentication path come from
/// `cache.top_leaves`, and MPC evaluates only that layer's `ell1` signing chains. The signature is
/// byte-identical to the uncached one. A cache that does not match `(params, pk)` is rejected with
/// [`Poseidon2MpcError::CachedSubtreeMismatch`] before any epoch is latched.
#[expect(
    clippy::too_many_arguments,
    reason = "One signing session: parameters, public key, optional leaf cache, committee latch certificate, quorum latches, message and per-party state"
)]
pub fn sign_jorts_poseidon2_mpc_cached<L: StatefulEpochLatch>(
    session_id: [u8; 32],
    params: &PqHashParams,
    pk: &PqPublicKey,
    cache: Option<&DkgCachedSubtrees>,
    t: usize,
    latch_cert: Option<&EpochLatchCertificate>,
    latches: &mut [&mut L],
    msg: &[u8],
    max_grind: u32,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(u64, PqHashSig), Poseidon2MpcError> {
    if !params.is_well_formed() || !params.stateful {
        return Err(Poseidon2MpcError::InvalidParams);
    }
    validate_top_subtree_cache(params, pk, cache)?;
    if latches.len() != key_shares.len() {
        return Err(Poseidon2MpcError::InvalidQuorum {
            t,
            n: latches.len(),
        });
    }
    let (quorum_pk_seed, quorum_pts) = validate_quorum_slices(t, key_shares, vaults, party_rngs)?;
    validate_enrolled_key_profile(params, pk, &quorum_pk_seed, key_shares)?;
    let committee_size = key_shares[0].committee_size;
    let mu = th_pre_hash(Poseidon2Suite, &pk.pk_seed, &pk.pk_root, msg);

    let ep0 = {
        let pinned_authority = resolve_enrolled_latch_authority(key_shares)?;
        reserve_authorised_epoch(
            params,
            pk,
            t,
            committee_size,
            pinned_authority,
            latch_cert,
            latches,
            &mu,
        )?
    };
    let leaf_global_idx = usize::try_from(ep0)
        .map_err(|_| Poseidon2MpcError::EpochLatch(EpochLatchError::Exhausted))?;

    let opt_domain = build_stateful_det_opt_domain(ep0, &pk.pk_seed);
    let r_rand = eval_prf_msg_mpc_cut(
        &session_id,
        "pos2_stateful_r_rand",
        t,
        &quorum_pts,
        &opt_domain,
        &mu,
        key_shares,
        vaults,
        party_rngs,
    )?;

    let sig = sign_hypertree_poseidon2_mpc_core(
        &session_id,
        params,
        pk,
        cache,
        t,
        &quorum_pts,
        &mu,
        r_rand,
        leaf_global_idx,
        None,
        max_grind,
        key_shares,
        vaults,
        party_rngs,
    )?;
    if !verify_pq_hash_sig(Poseidon2Suite, params, pk, msg, &sig) {
        return Err(Poseidon2MpcError::SignatureSelfCheckFailed);
    }
    Ok((ep0, sig))
}

/// Safe crash-recovery retry for stateful `JortsPoseidon2` (`[P0-04]`):
/// - Applies the same committee-wide latch gate as [`sign_jorts_poseidon2_mpc`] to
///   `(epoch, mu)`: full attendance, or a certificate for exactly this key, epoch and message;
/// - Verifies `latch.retry_latched_epoch(epoch, &mu)` across all quorum latches (refusing any
///   unlatched epoch or equivocated message digest); no latch is advanced;
/// - Re-derives the exact deterministic `r_rand` and bit-identical `PqHashSig`.
#[expect(
    clippy::too_many_arguments,
    reason = "One retry session: parameters, public key, committee latch certificate, quorum latches, latched epoch, message and per-party state"
)]
pub fn retry_jorts_poseidon2_mpc<L: StatefulEpochLatch>(
    session_id: [u8; 32],
    params: &PqHashParams,
    pk: &PqPublicKey,
    t: usize,
    latch_cert: Option<&EpochLatchCertificate>,
    latches: &mut [&mut L],
    epoch: u64,
    msg: &[u8],
    max_grind: u32,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<PqHashSig, Poseidon2MpcError> {
    retry_jorts_poseidon2_mpc_cached(
        session_id, params, pk, None, t, latch_cert, latches, epoch, msg, max_grind, key_shares,
        vaults, party_rngs,
    )
}

/// [`retry_jorts_poseidon2_mpc`] with an optional top-subtree leaf cache (same cache
/// rules as [`sign_jorts_poseidon2_mpc_cached`]).
#[expect(
    clippy::too_many_arguments,
    reason = "One retry session: parameters, public key, optional leaf cache, committee latch certificate, quorum latches, latched epoch, message and per-party state"
)]
pub fn retry_jorts_poseidon2_mpc_cached<L: StatefulEpochLatch>(
    session_id: [u8; 32],
    params: &PqHashParams,
    pk: &PqPublicKey,
    cache: Option<&DkgCachedSubtrees>,
    t: usize,
    latch_cert: Option<&EpochLatchCertificate>,
    latches: &mut [&mut L],
    epoch: u64,
    msg: &[u8],
    max_grind: u32,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<PqHashSig, Poseidon2MpcError> {
    if !params.is_well_formed() || !params.stateful {
        return Err(Poseidon2MpcError::InvalidParams);
    }
    validate_top_subtree_cache(params, pk, cache)?;
    if latches.len() != key_shares.len() {
        return Err(Poseidon2MpcError::InvalidQuorum {
            t,
            n: latches.len(),
        });
    }
    let (quorum_pk_seed, quorum_pts) = validate_quorum_slices(t, key_shares, vaults, party_rngs)?;
    validate_enrolled_key_profile(params, pk, &quorum_pk_seed, key_shares)?;
    let committee_size = key_shares[0].committee_size;
    let mu = th_pre_hash(Poseidon2Suite, &pk.pk_seed, &pk.pk_root, msg);

    {
        let pinned_authority = resolve_enrolled_latch_authority(key_shares)?;
        check_committee_latch_authorisation(
            pk,
            t,
            committee_size,
            latches.len(),
            pinned_authority,
            latch_cert,
            epoch,
            &mu,
        )?;
    }
    for l in latches.iter_mut() {
        let ep = l.retry_latched_epoch(epoch, &mu)?;
        if ep != epoch {
            return Err(Poseidon2MpcError::EpochLatch(
                EpochLatchError::EquivocationRefused,
            ));
        }
    }
    let leaf_global_idx = usize::try_from(epoch)
        .map_err(|_| Poseidon2MpcError::EpochLatch(EpochLatchError::Exhausted))?;
    let opt_domain = build_stateful_det_opt_domain(epoch, &pk.pk_seed);
    let r_rand = eval_prf_msg_mpc_cut(
        &session_id,
        "pos2_stateful_retry_r_rand",
        t,
        &quorum_pts,
        &opt_domain,
        &mu,
        key_shares,
        vaults,
        party_rngs,
    )?;

    let sig = sign_hypertree_poseidon2_mpc_core(
        &session_id,
        params,
        pk,
        cache,
        t,
        &quorum_pts,
        &mu,
        r_rand,
        leaf_global_idx,
        None,
        max_grind,
        key_shares,
        vaults,
        party_rngs,
    )?;
    if !verify_pq_hash_sig(Poseidon2Suite, params, pk, msg, &sig) {
        return Err(Poseidon2MpcError::SignatureSelfCheckFailed);
    }
    Ok(sig)
}

/// The stateless signers' randomiser `R = PRF_msg(SK.prf, build_stateless_det_opt_domain(pk_seed), mu)`,
/// evaluated on shares and opened after its MAC check.
///
/// Every input other than the shared `SK.prf` is fixed by the key and the message digest, so no
/// caller, signer or session contributes to `R`: aborting and retrying a session reproduces the
/// same `R` and therefore the same hypertree leaf and FORS instance.
#[expect(
    clippy::too_many_arguments,
    reason = "One MPC phase: transcript context, quorum, public key, message digest and per-party state"
)]
fn eval_stateless_r_rand_mpc(
    session_id: &[u8; 32],
    t: usize,
    quorum_pts: &[Goldilocks],
    pk: &PqPublicKey,
    mu: &[u8; 32],
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<[u8; 32], Poseidon2MpcError> {
    let transcript = crate::sponge::keccak::encode_multi_frame(&[session_id, mu]);
    for rng in party_rngs.iter_mut() {
        rng.hedge_transcript(&transcript);
    }
    let opt_domain = build_stateless_det_opt_domain(&pk.pk_seed);
    eval_prf_msg_mpc_cut(
        session_id,
        "pos2_stateless_r_rand",
        t,
        quorum_pts,
        &opt_domain,
        mu,
        key_shares,
        vaults,
        party_rngs,
    )
}

/// Sign a message under stateless `Corduroy` / `Baggy` over `Poseidon2Suite` in SPDZ MPC.
///
/// The randomiser `R` is derived under MPC from `SK.prf` and the message digest alone (see
/// [`build_stateless_det_opt_domain`]); there is no randomiser input. Signing the same message
/// again, in any session and with any signing set, yields the same signature.
#[expect(
    clippy::too_many_arguments,
    reason = "One signing session: parameters, public key, message and per-party state"
)]
pub fn sign_stateless_tsw_poseidon2_mpc(
    session_id: [u8; 32],
    params: &PqHashParams,
    pk: &PqPublicKey,
    t: usize,
    msg: &[u8],
    max_grind: u32,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<PqHashSig, Poseidon2MpcError> {
    sign_stateless_tsw_poseidon2_mpc_cached(
        session_id, params, pk, None, t, msg, max_grind, key_shares, vaults, party_rngs,
    )
}

/// [`sign_stateless_tsw_poseidon2_mpc`] with an optional top-subtree leaf cache (same cache rules
/// as [`sign_jorts_poseidon2_mpc_cached`]; rejection happens before any MPC wire opens).
#[expect(
    clippy::too_many_arguments,
    reason = "One signing session: parameters, public key, optional leaf cache, message and per-party state"
)]
pub fn sign_stateless_tsw_poseidon2_mpc_cached(
    session_id: [u8; 32],
    params: &PqHashParams,
    pk: &PqPublicKey,
    cache: Option<&DkgCachedSubtrees>,
    t: usize,
    msg: &[u8],
    max_grind: u32,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<PqHashSig, Poseidon2MpcError> {
    if !params.is_well_formed() || params.stateful {
        return Err(Poseidon2MpcError::InvalidParams);
    }
    validate_top_subtree_cache(params, pk, cache)?;
    let (quorum_pk_seed, quorum_pts) = validate_quorum_slices(t, key_shares, vaults, party_rngs)?;
    validate_enrolled_key_profile(params, pk, &quorum_pk_seed, key_shares)?;
    let mu = th_pre_hash(Poseidon2Suite, &pk.pk_seed, &pk.pk_root, msg);

    let r_rand = eval_stateless_r_rand_mpc(
        &session_id,
        t,
        &quorum_pts,
        pk,
        &mu,
        key_shares,
        vaults,
        party_rngs,
    )?;
    let (leaf_global_idx, fors_idxs) = derive_stateless_leaf_and_fors_indices(
        Poseidon2Suite,
        params,
        &r_rand,
        &pk.pk_seed,
        &pk.pk_root,
        &mu,
    )
    .ok_or(Poseidon2MpcError::InvalidParams)?;

    let sig = sign_hypertree_poseidon2_mpc_core(
        &session_id,
        params,
        pk,
        cache,
        t,
        &quorum_pts,
        &mu,
        r_rand,
        leaf_global_idx,
        Some(&fors_idxs),
        max_grind,
        key_shares,
        vaults,
        party_rngs,
    )?;
    if !verify_pq_hash_sig(Poseidon2Suite, params, pk, msg, &sig) {
        return Err(Poseidon2MpcError::SignatureSelfCheckFailed);
    }
    Ok(sig)
}

impl core::fmt::Display for Poseidon2MpcError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl core::error::Error for Poseidon2MpcError {}

// ============================================================================
// `Hem`-Compatible Native `[Goldilocks; 4]` `JortsPoseidon2` SPDZ MPC Engine
// (`w = 4, chains = 128, target_sum = 192, height = 6`, `0` Intermediate A2B)
// ============================================================================

/// Wire profile tag for `Hem`-aggregatable `JortsPoseidon2` (`AggSigProfile::JortsPoseidon2 = 1`).
pub const HEM_JORTS_PROFILE_BYTE: u8 = 1;
/// Number of base-4 `WOTS+C` chains in `Hem` `JortsPoseidon2` (`128`).
pub const HEM_WOTS_CHAINS: usize = 128;
/// Winternitz base `w = 4` (`0..=3` steps per chain).
pub const HEM_WOTS_BASE_W: usize = 4;
/// Maximum step index per chain (`w - 1 = 3`).
pub const HEM_WOTS_MAX_STEP: usize = HEM_WOTS_BASE_W - 1;
/// Exact constant digit sum (`192 = 128 * 1.5`), fixing online & verifier step count to `192`.
pub const HEM_WOTS_TARGET_SUM: usize = 192;
/// Height of the `Hem` `JortsPoseidon2` XMSS tree (`2^6 = 64` leaves).
pub const HEM_JORTS_XMSS_HEIGHT: usize = 6;
/// Number of leaves in the `Hem` `JortsPoseidon2` XMSS tree (`64`).
pub const HEM_JORTS_MAX_LEAVES: usize = 1usize << HEM_JORTS_XMSS_HEIGHT;
/// Canonical serialized byte length of a `HemJortsPublicKey` (`65` bytes).
pub const HEM_JORTS_PK_BYTES: usize = 1 + 32 + 32;
/// Canonical serialized byte length of a `HemJortsSignature` (`4,328` bytes).
pub const HEM_JORTS_SIG_BYTES: usize =
    32 + 4 + 4 + HEM_WOTS_CHAINS * 32 + HEM_JORTS_XMSS_HEIGHT * 32;

/// Domain tags matching `qsag_agg::sig` bit-for-bit.
pub const HEM_DOMAIN_PRF_WOTS: u64 = 0x5153_4147_5750_5246; // "QSAGWPRF"
pub const HEM_DOMAIN_WOTS_STEP: u64 = 0x5153_4147_5753_5450; // "QSAGWSTP"
pub const HEM_DOMAIN_WOTS_PK: u64 = 0x5153_4147_5750_4B31; // "QSAGWPK1"
pub const HEM_DOMAIN_MERKLE_NODE: u64 = 0x5153_4147_4D52_4B4C; // "QSAGMRKL"
pub const HEM_DOMAIN_H_MSG_STATEFUL: u64 = 0x5153_4147_484D_5331; // "QSAGHMS1"
pub const HEM_DOMAIN_PRF_MSG: u64 = 0x5153_4147_5052_464D; // "QSAGPRFM"

/// Domain tags for deterministic 56-bit injective seed expansion and unassigned-leaf commitments.
pub const HEM_DOMAIN_PK_SEED_EXPAND: u64 = 0x5153_4147_4850_4B53; // "QSAGHPKS"
pub const HEM_DOMAIN_SK_SEED_EXPAND: u64 = 0x5153_4147_4853_4B53; // "QSAGHSKS"
pub const HEM_DOMAIN_SK_PRF_EXPAND: u64 = 0x5153_4147_4853_4B50; // "QSAGHSKP"
pub const HEM_DOMAIN_PRF_CHECK: u64 = 0x5153_4147_4850_4348; // "QSAGHPCH"
pub const HEM_DOMAIN_UNASSIGNED_LEAF: u64 = 0x5153_4147_4855_4E41; // "QSAGHUNA"

/// 4-limb algebraic `Goldilocks` digest (`32` canonical little-endian bytes).
pub type HemDigest4 = [Goldilocks; 4];

/// 5-limb 56-bit injective `Goldilocks` packing of a 32-byte digest (`0` mod-`p` collisions).
pub type HemDigest5 = [Goldilocks; 5];

/// Bijectively pack 32 raw bytes into 5 canonical `Goldilocks` limbs (`4 × 56` bits + `1 × 32` bits),
/// matching `qsag_agg::sig::bytes32_to_limbs56` bit-for-bit.
#[inline]
pub fn hem_bytes32_to_limbs56(bytes: &[u8; 32]) -> HemDigest5 {
    let mut out = [Goldilocks::ZERO; 5];
    for i in 0..4 {
        let mut v = 0u64;
        for b in 0..7 {
            v |= (bytes[7 * i + b] as u64) << (8 * b);
        }
        out[i] = Goldilocks::from_u64_reduced(v);
    }
    let last = u32::from_le_bytes([bytes[28], bytes[29], bytes[30], bytes[31]]) as u64;
    out[4] = Goldilocks::from_u64_reduced(last);
    out
}

/// Serialize a `HemDigest4` to 32 canonical little-endian bytes (`qsag_agg::sig::digest4_to_bytes`).
#[inline]
pub fn hem_digest4_to_bytes(d: &HemDigest4) -> [u8; 32] {
    let mut out = [0u8; 32];
    for i in 0..4 {
        out[8 * i..8 * (i + 1)].copy_from_slice(&d[i].to_le_bytes());
    }
    out
}

/// Decode a `HemDigest4` from 32 canonical little-endian bytes (`< p` per limb).
#[inline]
pub fn hem_digest4_from_bytes_canonical(bytes: &[u8; 32]) -> Option<HemDigest4> {
    let mut out = [Goldilocks::ZERO; 4];
    for i in 0..4 {
        let mut limb = [0u8; 8];
        limb.copy_from_slice(&bytes[8 * i..8 * (i + 1)]);
        out[i] = Goldilocks::from_le_bytes_canonical(limb)?;
    }
    Some(out)
}

/// Deterministically derive a canonical `HemDigest4` `pk_seed` from a 32-byte DKG public seed.
#[inline]
pub fn hem_pk_seed_from_bytes32(pk_seed_bytes: &[u8; 32]) -> HemDigest4 {
    let limbs5 = hem_bytes32_to_limbs56(pk_seed_bytes);
    let mut st = [
        limbs5[0],
        limbs5[1],
        limbs5[2],
        limbs5[3],
        limbs5[4],
        Goldilocks::ZERO,
        Goldilocks::ZERO,
        Goldilocks::ZERO,
        Goldilocks::from_u64_reduced(HEM_DOMAIN_PK_SEED_EXPAND),
        Goldilocks::ZERO,
        Goldilocks::ZERO,
        Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV),
    ];
    poseidon2_perm12(&mut st);
    [
        st[0] + limbs5[0],
        st[1] + limbs5[1],
        st[2] + limbs5[2],
        st[3] + limbs5[3],
    ]
}

/// Expand a 32-byte secret seed (`SK.seed` or `SK.prf`) in the clear via the exact same 5-limb
/// 56-bit linear packing + feed-forward `poseidon2_perm12` evaluated inside SPDZ MPC.
pub fn hem_expand_secret_bytes32_clear(
    secret_bytes: &[u8; 32],
    pk_seed: HemDigest4,
    domain_tag: u64,
) -> HemDigest4 {
    let mut limbs5 = hem_bytes32_to_limbs56(secret_bytes);
    let mut st = [
        limbs5[0],
        limbs5[1],
        limbs5[2],
        limbs5[3],
        limbs5[4],
        pk_seed[0],
        pk_seed[1],
        pk_seed[2],
        pk_seed[3],
        Goldilocks::from_u64_reduced(domain_tag),
        Goldilocks::ZERO,
        Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV),
    ];
    poseidon2_perm12(&mut st);
    let out = [
        st[0] + limbs5[0],
        st[1] + limbs5[1],
        st[2] + limbs5[2],
        st[3] + limbs5[3],
    ];
    wipe_goldilocks(&mut limbs5);
    wipe_goldilocks(&mut st);
    out
}

/// Canonical 65-byte `Hem`-compatible `JortsPoseidon2` validator public key
/// (`0x01 || pk_seed_le32 || pk_root_le32`, byte-identical to `qsag_agg::ValidatorPublicKey`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct HemJortsPublicKey {
    pub pk_seed: HemDigest4,
    pub pk_root: HemDigest4,
}

impl HemJortsPublicKey {
    /// Serialize to canonical 65-byte `ValidatorPublicKey` wire format.
    pub fn to_bytes(&self) -> [u8; HEM_JORTS_PK_BYTES] {
        let mut out = [0u8; HEM_JORTS_PK_BYTES];
        out[0] = HEM_JORTS_PROFILE_BYTE;
        out[1..33].copy_from_slice(&hem_digest4_to_bytes(&self.pk_seed));
        out[33..65].copy_from_slice(&hem_digest4_to_bytes(&self.pk_root));
        out
    }

    /// Parse from canonical 65-byte `ValidatorPublicKey` wire format.
    pub fn from_bytes_canonical(bytes: &[u8; HEM_JORTS_PK_BYTES]) -> Option<Self> {
        if bytes[0] != HEM_JORTS_PROFILE_BYTE {
            return None;
        }
        let mut s = [0u8; 32];
        let mut r = [0u8; 32];
        s.copy_from_slice(&bytes[1..33]);
        r.copy_from_slice(&bytes[33..65]);
        Some(Self {
            pk_seed: hem_digest4_from_bytes_canonical(&s)?,
            pk_root: hem_digest4_from_bytes_canonical(&r)?,
        })
    }

    /// Projection to [`PqPublicKey`] used by [`EpochLatchCertificate`] and [`crate::dkg::QuorumEpochLatchCluster`].
    #[inline]
    pub fn latch_pq_public_key(&self, dkg_pk_seed: [u8; 32]) -> PqPublicKey {
        PqPublicKey {
            pk_seed: dkg_pk_seed,
            pk_root: hem_digest4_to_bytes(&self.pk_root),
        }
    }
}

/// Canonical 4,328-byte `Hem`-compatible `JortsPoseidon2` signature, byte-identical to
/// `qsag_agg::ValidatorSignature` (`AggSigProfile::JortsPoseidon2`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HemJortsSignature {
    pub r_rand: HemDigest4,
    pub stateful_leaf_idx: u32,
    pub tsw_ctr: u32,
    pub wots_chains: Vec<HemDigest4>,
    pub merkle_path: Vec<HemDigest4>,
}

impl HemJortsSignature {
    /// Encode to canonical 4,328-byte `qsag_agg::ValidatorSignature` wire format.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(HEM_JORTS_SIG_BYTES);
        out.extend_from_slice(&hem_digest4_to_bytes(&self.r_rand));
        out.extend_from_slice(&self.stateful_leaf_idx.to_le_bytes());
        out.extend_from_slice(&self.tsw_ctr.to_le_bytes());
        for c in &self.wots_chains {
            out.extend_from_slice(&hem_digest4_to_bytes(c));
        }
        for sib in &self.merkle_path {
            out.extend_from_slice(&hem_digest4_to_bytes(sib));
        }
        out
    }

    /// Decode from canonical 4,328-byte `qsag_agg::ValidatorSignature` wire format.
    pub fn from_bytes_canonical(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != HEM_JORTS_SIG_BYTES {
            return None;
        }
        let mut pos = 0usize;
        let read_d4 = |buf: &[u8], p: &mut usize| -> Option<HemDigest4> {
            let slice: &[u8; 32] = buf.get(*p..*p + 32)?.try_into().ok()?;
            *p += 32;
            hem_digest4_from_bytes_canonical(slice)
        };
        let read_u32 = |buf: &[u8], p: &mut usize| -> Option<u32> {
            let slice: &[u8; 4] = buf.get(*p..*p + 4)?.try_into().ok()?;
            *p += 4;
            Some(u32::from_le_bytes(*slice))
        };

        let r_rand = read_d4(bytes, &mut pos)?;
        let stateful_leaf_idx = read_u32(bytes, &mut pos)?;
        if (stateful_leaf_idx as usize) >= HEM_JORTS_MAX_LEAVES {
            return None;
        }
        let tsw_ctr = read_u32(bytes, &mut pos)?;
        let mut wots_chains = Vec::with_capacity(HEM_WOTS_CHAINS);
        for _ in 0..HEM_WOTS_CHAINS {
            wots_chains.push(read_d4(bytes, &mut pos)?);
        }
        let mut merkle_path = Vec::with_capacity(HEM_JORTS_XMSS_HEIGHT);
        for _ in 0..HEM_JORTS_XMSS_HEIGHT {
            merkle_path.push(read_d4(bytes, &mut pos)?);
        }
        if pos != bytes.len() {
            return None;
        }
        Some(Self {
            r_rand,
            stateful_leaf_idx,
            tsw_ctr,
            wots_chains,
            merkle_path,
        })
    }
}

/// Public cached height-6 XMSS leaf table and `SK.prf` check digest produced during distributed
/// `HemJortsPoseidon2` key generation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HemJortsCachedTree {
    pub dkg_pk_seed: [u8; 32],
    pub pk: HemJortsPublicKey,
    pub active_leaves: usize,
    pub leaves: Vec<HemDigest4>,
    pub prf_check: HemDigest4,
}

impl HemJortsCachedTree {
    /// Verify public structural consistency: `active_leaves in 1..=64`, `leaves.len() == 64`,
    /// `pk.pk_seed` matches `dkg_pk_seed`, any inactive leaves equal `hem_unassigned_leaf_digest`,
    /// and the 64 leaves Merkle-hash to `pk.pk_root`.
    pub fn verify_consistency(&self) -> bool {
        if self.active_leaves == 0
            || self.active_leaves > HEM_JORTS_MAX_LEAVES
            || self.leaves.len() != HEM_JORTS_MAX_LEAVES
        {
            return false;
        }
        if self.pk.pk_seed != hem_pk_seed_from_bytes32(&self.dkg_pk_seed) {
            return false;
        }
        for kp in self.active_leaves..HEM_JORTS_MAX_LEAVES {
            if self.leaves[kp] != hem_unassigned_leaf_digest(self.pk.pk_seed, kp as u32) {
                return false;
            }
        }
        hem_merkle_root_from_leaves(self.pk.pk_seed, &self.leaves) == Some(self.pk.pk_root)
    }
}

/// Algebraic 256-bit Jive/feed-forward compression `H_comp(in0, in1, tweak) -> HemDigest4`,
/// matching `qsag_agg::sponge::poseidon2_compress12_ff` bit-for-bit.
#[inline]
pub fn hem_poseidon2_compress12_ff(
    mut in0: HemDigest4,
    in1: HemDigest4,
    tweak: HemDigest4,
) -> HemDigest4 {
    let mut st = [
        in0[0], in0[1], in0[2], in0[3], in1[0], in1[1], in1[2], in1[3], tweak[0], tweak[1],
        tweak[2], tweak[3],
    ];
    poseidon2_perm12(&mut st);
    let out = [
        st[0] + in0[0],
        st[1] + in0[1],
        st[2] + in0[2],
        st[3] + in0[3],
    ];
    wipe_goldilocks(&mut st);
    wipe_goldilocks(&mut in0);
    out
}

/// Bijective address packing for `WOTS+C` steps (`qsag_agg::sig::pack_wots_addr_limb`).
#[inline]
pub fn hem_pack_wots_addr_limb(
    layer: u32,
    kp_idx: u32,
    chain_idx: u32,
    step_idx: u32,
) -> Goldilocks {
    debug_assert!(layer < 64 && kp_idx < (1 << 20) && chain_idx < 256 && step_idx < 16);
    let packed = ((layer as u64) << 44)
        | ((kp_idx as u64) << 16)
        | ((chain_idx as u64) << 4)
        | (step_idx as u64);
    Goldilocks::from_u64_reduced(packed)
}

/// Clear single-party `WOTS+C` chain base secret `y^(0)` (`qsag_agg::sig::ValidatorKeypair::wots_base_secret`).
#[inline]
pub fn hem_wots_base_secret_clear(
    sk_seed: HemDigest4,
    pk_seed: HemDigest4,
    layer: u32,
    tree_idx: u64,
    kp_idx: u32,
    chain_idx: u32,
) -> HemDigest4 {
    let tweak = [
        Goldilocks::from_u64_reduced(HEM_DOMAIN_PRF_WOTS),
        hem_pack_wots_addr_limb(layer, kp_idx, chain_idx, 0),
        Goldilocks::from_u64_reduced(tree_idx & 0xFFFF_FFFF),
        Goldilocks::from_u64_reduced(tree_idx >> 32),
    ];
    hem_poseidon2_compress12_ff(sk_seed, pk_seed, tweak)
}

/// Public `WOTS+C` step transition `y^(step + 1) = F(pk_seed, y^(step), adrs)`
/// (`qsag_agg::sig::wots_step_hash_injective`).
#[inline]
pub fn hem_wots_step_hash_injective(
    pk_seed: HemDigest4,
    cur: HemDigest4,
    layer: u32,
    tree_idx: u64,
    kp_idx: u32,
    chain_idx: u32,
    step_idx: u32,
) -> HemDigest4 {
    let tweak = [
        Goldilocks::from_u64_reduced(HEM_DOMAIN_WOTS_STEP),
        hem_pack_wots_addr_limb(layer, kp_idx, chain_idx, step_idx),
        Goldilocks::from_u64_reduced(tree_idx & 0xFFFF_FFFF),
        Goldilocks::from_u64_reduced(tree_idx >> 32),
    ];
    hem_poseidon2_compress12_ff(cur, pk_seed, tweak)
}

/// Compress all 128 `WOTS+C` chain endpoints (`y^(3)`) into a 4-limb `wots_pk` leaf digest,
/// matching `qsag_agg::sig::compress_wots_endpoints_sponge` bit-for-bit.
pub fn hem_compress_wots_endpoints_sponge(
    pk_seed: HemDigest4,
    layer: u32,
    tree_idx: u64,
    kp_idx: u32,
    endpoints: &[HemDigest4; HEM_WOTS_CHAINS],
) -> HemDigest4 {
    let layer_kp = ((layer as u64) << 32) | (kp_idx as u64);
    let mut st = [
        pk_seed[0],
        pk_seed[1],
        pk_seed[2],
        pk_seed[3],
        Goldilocks::from_u64_reduced(layer_kp),
        Goldilocks::from_u64_reduced(tree_idx & 0xFFFF_FFFF),
        Goldilocks::from_u64_reduced(tree_idx >> 32),
        Goldilocks::from_u64_reduced(HEM_WOTS_CHAINS as u64),
        Goldilocks::from_u64_reduced(HEM_DOMAIN_WOTS_PK),
        Goldilocks::ZERO,
        Goldilocks::ZERO,
        Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV),
    ];
    poseidon2_perm12(&mut st);
    for pair_idx in 0..(HEM_WOTS_CHAINS / 2) {
        let e0 = endpoints[2 * pair_idx];
        let e1 = endpoints[2 * pair_idx + 1];
        for i in 0..4 {
            st[i] += e0[i];
            st[4 + i] += e1[i];
        }
        poseidon2_perm12(&mut st);
    }
    st[0] += Goldilocks::ONE;
    poseidon2_perm12(&mut st);
    [st[0], st[1], st[2], st[3]]
}

/// Domain-separated public digest for an unassigned leaf slot (`kp_idx >= active_leaves`),
/// disjoint from `HEM_DOMAIN_WOTS_PK` so no valid `WOTS+C` endpoint vector can collide with it.
#[inline]
pub fn hem_unassigned_leaf_digest(pk_seed: HemDigest4, kp_idx: u32) -> HemDigest4 {
    let tweak = [
        Goldilocks::from_u64_reduced(HEM_DOMAIN_UNASSIGNED_LEAF),
        Goldilocks::from_u64_reduced(kp_idx as u64),
        Goldilocks::ZERO,
        Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV),
    ];
    hem_poseidon2_compress12_ff(pk_seed, pk_seed, tweak)
}

/// 2-block binary Merkle node sponge matching `qsag_agg::sig::merkle_node_hash` (`DOMAIN_MERKLE_NODE`).
#[inline]
pub fn hem_merkle_node_hash(
    pk_seed: HemDigest4,
    layer: u32,
    tree_idx: u64,
    level: u32,
    node_idx: u32,
    left: HemDigest4,
    right: HemDigest4,
) -> HemDigest4 {
    debug_assert!(layer <= 0xFFFE && level <= 0xFFFF);
    let meta0 = ((layer as u64) << 48) | ((level as u64) << 32) | (node_idx as u64);
    let mut st = [
        pk_seed[0],
        pk_seed[1],
        pk_seed[2],
        pk_seed[3],
        left[0],
        left[1],
        left[2],
        left[3],
        Goldilocks::from_u64_reduced(HEM_DOMAIN_MERKLE_NODE),
        Goldilocks::from_u64_reduced(meta0),
        Goldilocks::from_u64_reduced(tree_idx & 0xFFFF_FFFF),
        Goldilocks::from_u64_reduced(tree_idx >> 32),
    ];
    poseidon2_perm12(&mut st);
    for i in 0..4 {
        st[i] += right[i];
    }
    st[4] += Goldilocks::ONE;
    st[5] += Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV);
    poseidon2_perm12(&mut st);
    [st[0], st[1], st[2], st[3]]
}

/// Compute the height-6 XMSS Merkle root from 64 leaf digests.
pub fn hem_merkle_root_from_leaves(
    pk_seed: HemDigest4,
    leaves: &[HemDigest4],
) -> Option<HemDigest4> {
    if leaves.len() != HEM_JORTS_MAX_LEAVES {
        return None;
    }
    let mut cur = leaves.to_vec();
    for lvl in 0..HEM_JORTS_XMSS_HEIGHT {
        let mut next = Vec::with_capacity(cur.len() / 2);
        for p in 0..(cur.len() / 2) {
            next.push(hem_merkle_node_hash(
                pk_seed,
                0,
                0,
                (lvl + 1) as u32,
                p as u32,
                cur[2 * p],
                cur[2 * p + 1],
            ));
        }
        cur = next;
    }
    Some(cur[0])
}

/// Extract the 6-sibling XMSS authentication path and Merkle root for `leaf_idx < 64`.
pub fn hem_merkle_auth_path(
    pk_seed: HemDigest4,
    leaves: &[HemDigest4],
    leaf_idx: usize,
) -> Option<(Vec<HemDigest4>, HemDigest4)> {
    if leaves.len() != HEM_JORTS_MAX_LEAVES || leaf_idx >= HEM_JORTS_MAX_LEAVES {
        return None;
    }
    let mut path = Vec::with_capacity(HEM_JORTS_XMSS_HEIGHT);
    let mut cur = leaves.to_vec();
    let mut idx = leaf_idx;
    for lvl in 0..HEM_JORTS_XMSS_HEIGHT {
        path.push(cur[idx ^ 1]);
        let mut next = Vec::with_capacity(cur.len() / 2);
        for p in 0..(cur.len() / 2) {
            next.push(hem_merkle_node_hash(
                pk_seed,
                0,
                0,
                (lvl + 1) as u32,
                p as u32,
                cur[2 * p],
                cur[2 * p + 1],
            ));
        }
        cur = next;
        idx >>= 1;
    }
    Some((path, cur[0]))
}

/// Compute collision-free 5-limb 56-bit message representative `mu`, matching
/// `qsag_agg::sig::compute_message_mu` bit-for-bit.
#[inline]
pub fn hem_compute_message_mu(pk: &HemJortsPublicKey, msg: &[u8]) -> ([u8; 32], HemDigest5) {
    let pk_bytes = pk.to_bytes();
    let framed = crate::sponge::keccak::encode_multi_frame(&[b"QSAG.MU/v2", &pk_bytes, msg]);
    let h = poseidon2_hash32(&framed);
    (h, hem_bytes32_to_limbs56(&h))
}

/// Clear single-party `r_rand` derivation matching `qsag_agg::sig::ValidatorKeypair::derive_deterministic_r_rand`.
#[inline]
pub fn hem_derive_r_rand_clear(
    sk_prf: HemDigest4,
    pk_seed: HemDigest4,
    mu: HemDigest5,
    epoch: u64,
) -> HemDigest4 {
    let mut st = [
        sk_prf[0],
        sk_prf[1],
        sk_prf[2],
        sk_prf[3],
        pk_seed[0],
        pk_seed[1],
        pk_seed[2],
        pk_seed[3],
        Goldilocks::from_u64_reduced(HEM_DOMAIN_PRF_MSG),
        Goldilocks::from_u64_reduced(epoch),
        mu[4],
        Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV),
    ];
    poseidon2_perm12(&mut st);
    for i in 0..4 {
        st[i] += mu[i];
    }
    poseidon2_perm12(&mut st);
    let out = [st[0], st[1], st[2], st[3]];
    wipe_goldilocks(&mut st);
    out
}

/// Public check digest committing to `sk_prf` (`poseidon2_compress12_ff(sk_prf, pk_seed, [HEM_DOMAIN_PRF_CHECK, 0, 0, IV])`).
#[inline]
pub fn hem_prf_check_digest_clear(sk_prf: HemDigest4, pk_seed: HemDigest4) -> HemDigest4 {
    let tweak = [
        Goldilocks::from_u64_reduced(HEM_DOMAIN_PRF_CHECK),
        Goldilocks::ZERO,
        Goldilocks::ZERO,
        Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV),
    ];
    hem_poseidon2_compress12_ff(sk_prf, pk_seed, tweak)
}

/// Stateful layer-0 randomized message hash `H_msg_stateful` (`qsag_agg::sig::compute_hmsg_stateful`).
pub fn hem_compute_hmsg_stateful(
    pk_seed: HemDigest4,
    pk_root: HemDigest4,
    r_rand: HemDigest4,
    mu: HemDigest5,
    kp_idx: u32,
    tsw_ctr: u32,
) -> HemDigest5 {
    let kp_ctr = ((kp_idx as u64) << 32) | (tsw_ctr as u64);
    let mut st = [
        pk_seed[0],
        pk_seed[1],
        pk_seed[2],
        pk_seed[3],
        pk_root[0],
        pk_root[1],
        pk_root[2],
        pk_root[3],
        Goldilocks::from_u64_reduced(HEM_DOMAIN_H_MSG_STATEFUL),
        Goldilocks::from_u64_reduced(kp_ctr),
        mu[4],
        Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV),
    ];
    poseidon2_perm12(&mut st);
    for i in 0..4 {
        st[i] += r_rand[i];
        st[4 + i] += mu[i];
    }
    poseidon2_perm12(&mut st);
    st[0] += Goldilocks::ONE;
    poseidon2_perm12(&mut st);
    [st[0], st[1], st[2], st[3], st[4]]
}

/// Extract 128 base-4 digits (`256` bits) from `hmsg[0..5]` requiring `< 2^63` per limb
/// (`qsag_agg::sig::extract_wots_digits_checked`).
pub fn hem_extract_wots_digits_checked(hmsg: &HemDigest5) -> Option<[u8; HEM_WOTS_CHAINS]> {
    for limb in hmsg {
        if (limb.to_canonical_u64() >> 63) != 0 {
            return None;
        }
    }
    let mut digits = [0u8; HEM_WOTS_CHAINS];
    for limb_idx in 0..4 {
        let v = hmsg[limb_idx].to_canonical_u64();
        for i in 0..31 {
            digits[31 * limb_idx + i] = ((v >> (2 * i)) & 3) as u8;
        }
    }
    let v4 = hmsg[4].to_canonical_u64();
    for i in 0..4 {
        digits[124 + i] = ((v4 >> (2 * i)) & 3) as u8;
    }
    Some(digits)
}

/// Deterministically grind `tsw_ctr` upward from `0` until `hem_extract_wots_digits_checked`
/// succeeds and the 128 base-4 digits sum to `HEM_WOTS_TARGET_SUM = 192`.
pub fn hem_grind_stateful_tsw_digits(
    pk_seed: HemDigest4,
    pk_root: HemDigest4,
    r_rand: HemDigest4,
    mu: HemDigest5,
    kp_idx: u32,
    max_grind: u32,
) -> Option<(u32, [u8; HEM_WOTS_CHAINS])> {
    let mut ctr = 0u32;
    loop {
        let hmsg = hem_compute_hmsg_stateful(pk_seed, pk_root, r_rand, mu, kp_idx, ctr);
        if let Some(digits) = hem_extract_wots_digits_checked(&hmsg) {
            let sum: usize = digits.iter().map(|&d| d as usize).sum();
            if sum == HEM_WOTS_TARGET_SUM {
                return Some((ctr, digits));
            }
        }
        if ctr >= max_grind {
            return None;
        }
        ctr = ctr.checked_add(1)?;
    }
}

/// Standalone reference verifier matching `qsag_agg::verify_individual_signature`
/// (`AggSigProfile::JortsPoseidon2`) bit-for-bit.
pub fn verify_hem_jorts_signature(
    pk: &HemJortsPublicKey,
    msg: &[u8],
    sig: &HemJortsSignature,
) -> bool {
    let kp_idx = sig.stateful_leaf_idx;
    if (kp_idx as usize) >= HEM_JORTS_MAX_LEAVES
        || sig.wots_chains.len() != HEM_WOTS_CHAINS
        || sig.merkle_path.len() != HEM_JORTS_XMSS_HEIGHT
    {
        return false;
    }
    let (_, mu) = hem_compute_message_mu(pk, msg);
    let hmsg =
        hem_compute_hmsg_stateful(pk.pk_seed, pk.pk_root, sig.r_rand, mu, kp_idx, sig.tsw_ctr);
    let Some(digits) = hem_extract_wots_digits_checked(&hmsg) else {
        return false;
    };
    let sum: usize = digits.iter().map(|&d| d as usize).sum();
    if sum != HEM_WOTS_TARGET_SUM {
        return false;
    }
    let mut endpoints = [[Goldilocks::ZERO; 4]; HEM_WOTS_CHAINS];
    for r in 0..HEM_WOTS_CHAINS {
        let mut cur = sig.wots_chains[r];
        for step in (digits[r] as u32)..(HEM_WOTS_MAX_STEP as u32) {
            cur = hem_wots_step_hash_injective(pk.pk_seed, cur, 0, 0, kp_idx, r as u32, step);
        }
        endpoints[r] = cur;
    }
    let mut node = hem_compress_wots_endpoints_sponge(pk.pk_seed, 0, 0, kp_idx, &endpoints);
    let mut idx = kp_idx;
    for (lvl, &sib) in sig
        .merkle_path
        .iter()
        .enumerate()
        .take(HEM_JORTS_XMSS_HEIGHT)
    {
        let parent_idx = idx >> 1;
        node = if (idx & 1) == 0 {
            hem_merkle_node_hash(pk.pk_seed, 0, 0, (lvl + 1) as u32, parent_idx, node, sib)
        } else {
            hem_merkle_node_hash(pk.pk_seed, 0, 0, (lvl + 1) as u32, parent_idx, sib, node)
        };
        idx = parent_idx;
    }
    node == pk.pk_root
}

/// Exact preprocessing budget `(num_pow7, num_beaver, num_a2b)` for distributed `HemJortsPoseidon2`
/// key generation with `active_leaves` active `WOTS+C` leaves (`0` Beaver triples, `0` A2B masks!).
pub fn required_hem_jorts_keygen_preprocessing_budget(
    active_leaves: usize,
) -> Result<(usize, usize, usize), Poseidon2MpcError> {
    if active_leaves == 0 || active_leaves > HEM_JORTS_MAX_LEAVES {
        return Err(Poseidon2MpcError::InvalidParams);
    }
    let perms = 2 + 1 + active_leaves * HEM_WOTS_CHAINS * HEM_WOTS_BASE_W;
    Ok((perms * POSEIDON2_SBOXES_PER_PERM, 0, 0))
}

/// Exact preprocessing budget `(num_pow7, 0, 0)` for `verify_reshared_hem_jorts_key_mpc`
/// (`515` `poseidon2_perm12`s = `60,770` `pow7` tuples, `0` Beaver triples, `0` A2B masks).
#[inline]
pub const fn required_hem_jorts_reshare_verify_preprocessing_budget() -> (usize, usize, usize) {
    let perms = 2 + 1 + HEM_WOTS_CHAINS * HEM_WOTS_BASE_W;
    (perms * POSEIDON2_SBOXES_PER_PERM, 0, 0)
}

/// Exact constant preprocessing budget `(num_pow7, 0, 0)` for one `sign_hem_jorts_poseidon2_mpc_cached`
/// or `retry_hem_jorts_poseidon2_mpc_cached` signature (`324` `poseidon2_perm12`s = `38,232` `pow7`
/// tuples, `0` Beaver triples, `0` A2B masks — constant across all messages because `sum(digits) == 192`!).
#[inline]
pub const fn required_hem_jorts_sign_preprocessing_budget_cached() -> (usize, usize, usize) {
    let perms = 2 + 2 + HEM_WOTS_CHAINS + HEM_WOTS_TARGET_SUM;
    (perms * POSEIDON2_SBOXES_PER_PERM, 0, 0)
}

#[inline]
fn pack_secret_bytes32_to_limbs56_auth(bytes32: &[AuthGlWire; 32]) -> [AuthGlWire; 5] {
    let mut out = [AuthGlWire::ZERO; 5];
    for i in 0..4 {
        let mut acc = AuthGlWire::ZERO;
        for b in 0..7 {
            let weight = Goldilocks::from_u64_reduced(1u64 << (8 * b));
            acc = acc.add(bytes32[7 * i + b].scale(weight));
        }
        out[i] = acc;
    }
    let mut acc4 = AuthGlWire::ZERO;
    for b in 0..4 {
        let weight = Goldilocks::from_u64_reduced(1u64 << (8 * b));
        acc4 = acc4.add(bytes32[28 + b].scale(weight));
    }
    out[4] = acc4;
    out
}

/// Expand `(sk_seed_bytes, sk_prf_bytes)` into `(sk_seed, sk_prf)` native `[AuthGlWire; 4]` shares
/// across the quorum in 1 parallel `eval_spdz_poseidon2_perm12_batch` (`2` perms, `0` A2B!).
fn expand_hem_secret_digests_mpc(
    t: usize,
    quorum_pts: &[Goldilocks],
    pk_seed: HemDigest4,
    key_shares: &[&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    pending: &mut SpdzGoldilocksPendingChecks,
) -> Result<(Vec<[AuthGlWire; 4]>, Vec<[AuthGlWire; 4]>), PreprocessError> {
    let m = quorum_pts.len();
    let mut states = SecretBuffer(vec![Vec::with_capacity(2); m]);
    let mut seed_low4 = SecretBuffer(vec![[AuthGlWire::ZERO; 4]; m]);
    let mut prf_low4 = SecretBuffer(vec![[AuthGlWire::ZERO; 4]; m]);

    for p in 0..m {
        let alpha_p = vaults[p].mac_alpha_share;
        let sw = SecretBuffer(key_seed_wires(key_shares[p]));
        let pw = SecretBuffer(key_prf_wires(key_shares[p]));
        let ls = SecretBuffer(pack_secret_bytes32_to_limbs56_auth(&sw));
        let lp = SecretBuffer(pack_secret_bytes32_to_limbs56_auth(&pw));
        seed_low4[p] = [ls[0], ls[1], ls[2], ls[3]];
        prf_low4[p] = [lp[0], lp[1], lp[2], lp[3]];

        let pks: [AuthGlWire; 4] =
            core::array::from_fn(|i| AuthGlWire::public_const(pk_seed[i], alpha_p));
        let iv = AuthGlWire::public_const(
            Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV),
            alpha_p,
        );
        let dom_s = AuthGlWire::public_const(
            Goldilocks::from_u64_reduced(HEM_DOMAIN_SK_SEED_EXPAND),
            alpha_p,
        );
        let dom_p = AuthGlWire::public_const(
            Goldilocks::from_u64_reduced(HEM_DOMAIN_SK_PRF_EXPAND),
            alpha_p,
        );

        states[p].push([
            ls[0], ls[1], ls[2], ls[3], ls[4], pks[0], pks[1], pks[2], pks[3], dom_s,
            AuthGlWire::ZERO, iv,
        ]);
        states[p].push([
            lp[0], lp[1], lp[2], lp[3], lp[4], pks[0], pks[1], pks[2], pks[3], dom_p,
            AuthGlWire::ZERO, iv,
        ]);
    }

    eval_spdz_poseidon2_perm12_batch(t, quorum_pts, &mut states, vaults, pending)?;

    let mut sk_seed_out = SecretBuffer(vec![[AuthGlWire::ZERO; 4]; m]);
    let mut sk_prf_out = SecretBuffer(vec![[AuthGlWire::ZERO; 4]; m]);
    for p in 0..m {
        for i in 0..4 {
            sk_seed_out[p][i] = states[p][0][i].add(seed_low4[p][i]);
            sk_prf_out[p][i] = states[p][1][i].add(prf_low4[p][i]);
        }
    }
    Ok((
        core::mem::take(&mut sk_seed_out.0),
        core::mem::take(&mut sk_prf_out.0),
    ))
}

/// Evaluate a batch of native `[AuthGlWire; 4]` Jive/feed-forward compressions
/// `poseidon2_compress12_ff(in0_secret, pk_seed_public, tweak_public)` in SPDZ (`0` A2B!).
fn eval_spdz_hem_compress12_ff_batch(
    t: usize,
    quorum_pts: &[Goldilocks],
    in0_per_party: &[Vec<[AuthGlWire; 4]>],
    pk_seed: HemDigest4,
    tweaks: &[HemDigest4],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    pending: &mut SpdzGoldilocksPendingChecks,
) -> Result<Vec<Vec<[AuthGlWire; 4]>>, PreprocessError> {
    let m = quorum_pts.len();
    let batch = tweaks.len();
    if batch == 0 {
        return Ok(vec![Vec::new(); m]);
    }
    let mut states = SecretBuffer(vec![Vec::with_capacity(batch); m]);
    for p in 0..m {
        let alpha_p = vaults[p].mac_alpha_share;
        let pks: [AuthGlWire; 4] =
            core::array::from_fn(|i| AuthGlWire::public_const(pk_seed[i], alpha_p));
        for (k, tw) in tweaks.iter().enumerate() {
            let x = in0_per_party[p][k];
            let tw_w: [AuthGlWire; 4] =
                core::array::from_fn(|i| AuthGlWire::public_const(tw[i], alpha_p));
            states[p].push([
                x[0], x[1], x[2], x[3], pks[0], pks[1], pks[2], pks[3], tw_w[0], tw_w[1], tw_w[2],
                tw_w[3],
            ]);
        }
    }

    eval_spdz_poseidon2_perm12_batch(t, quorum_pts, &mut states, vaults, pending)?;

    let mut out = SecretBuffer(vec![Vec::with_capacity(batch); m]);
    for p in 0..m {
        for k in 0..batch {
            let x = in0_per_party[p][k];
            out[p].push([
                states[p][k][0].add(x[0]),
                states[p][k][1].add(x[1]),
                states[p][k][2].add(x[2]),
                states[p][k][3].add(x[3]),
            ]);
        }
    }
    Ok(core::mem::take(&mut out.0))
}

/// Strictly verify ALL queued intermediate SPDZ wires AND open a batch of cut-boundary native
/// `HemDigest4` (`[Goldilocks; 4]`) digests via committed zero-masked `GoldilocksExt2` `MacCheck`.
#[expect(
    clippy::too_many_arguments,
    reason = "Two-stage cut barrier binds session, phase, quorum, cut digests, pending checks and party state"
)]
fn flush_verify_and_open_hem_digests4(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    quorum_pts: &[Goldilocks],
    cut_digests_per_party: &[Vec<[AuthGlWire; 4]>],
    pending: &mut SpdzGoldilocksPendingChecks,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<HemDigest4>, Poseidon2MpcError> {
    let m = quorum_pts.len();
    let num_digests = cut_digests_per_party[0].len();
    let alpha = SecretBuffer(vaults.iter().map(|v| v.mac_alpha_share).collect::<Vec<_>>());

    let intermediate = commit_and_open_spdz_goldilocks_batch_quorum(
        session_id,
        "hem_pre_cut_intermediate_mac",
        t,
        quorum_pts,
        &pending.shares_per_party,
        &pending.macs_per_party,
        &alpha,
        party_rngs,
    );
    pending.clear_and_wipe();
    match intermediate {
        Ok(mut values) => wipe_goldilocks(&mut values),
        Err(e) => {
            poison_all_on_abort(key_shares, vaults);
            return Err(Poseidon2MpcError::Preprocess(e));
        }
    }

    let total_wires = 4 * num_digests;
    let mut all_sh = SecretBuffer(vec![Vec::with_capacity(total_wires); m]);
    let mut all_mac = SecretBuffer(vec![Vec::with_capacity(total_wires); m]);
    for p in 0..m {
        for st in &cut_digests_per_party[p] {
            for w in st {
                all_sh[p].push(w.val);
                all_mac[p].push(w.mac);
            }
        }
    }

    let opened_res = commit_and_open_spdz_goldilocks_batch_quorum(
        session_id, phase, t, quorum_pts, &all_sh, &all_mac, &alpha, party_rngs,
    );
    drop(all_sh);
    drop(all_mac);
    drop(alpha);

    let opened = SecretBuffer(match opened_res {
        Ok(v) => v,
        Err(e) => {
            poison_all_on_abort(key_shares, vaults);
            return Err(Poseidon2MpcError::Preprocess(e));
        }
    });

    let mut out = Vec::with_capacity(num_digests);
    for s in 0..num_digests {
        out.push([
            opened[4 * s],
            opened[4 * s + 1],
            opened[4 * s + 2],
            opened[4 * s + 3],
        ]);
    }
    Ok(out)
}

/// Evaluate a batch of `(kp_idx, chain_idx, steps)` targets in native `[Goldilocks; 4]` SPDZ
/// (`0` intermediate A2B conversions!) starting from already-expanded `sk_seed_per_party`.
#[expect(
    clippy::too_many_arguments,
    reason = "Batched native WOTS+C chain evaluation takes quorum, seed shares, targets, vaults and pending checks"
)]
fn eval_hem_wots_chains_native_spdz(
    t: usize,
    quorum_pts: &[Goldilocks],
    pk_seed: HemDigest4,
    sk_seed_per_party: &[[AuthGlWire; 4]],
    targets: &[(u32, u32, usize)],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    pending: &mut SpdzGoldilocksPendingChecks,
) -> Result<Vec<Vec<[AuthGlWire; 4]>>, PreprocessError> {
    let m = quorum_pts.len();
    let count = targets.len();
    if count == 0 {
        return Ok(vec![Vec::new(); m]);
    }

    let mut base_in = SecretBuffer(vec![Vec::with_capacity(count); m]);
    for p in 0..m {
        for _ in 0..count {
            base_in[p].push(sk_seed_per_party[p]);
        }
    }
    let mut base_tweaks = Vec::with_capacity(count);
    for &(kp_idx, chain_idx, _) in targets {
        base_tweaks.push([
            Goldilocks::from_u64_reduced(HEM_DOMAIN_PRF_WOTS),
            hem_pack_wots_addr_limb(0, kp_idx, chain_idx, 0),
            Goldilocks::ZERO,
            Goldilocks::ZERO,
        ]);
    }
    let mut cur_states = SecretBuffer(eval_spdz_hem_compress12_ff_batch(
        t,
        quorum_pts,
        &base_in,
        pk_seed,
        &base_tweaks,
        vaults,
        pending,
    )?);

    let max_steps = targets.iter().map(|x| x.2).max().unwrap_or(0);
    for step in 0..max_steps {
        let active: Vec<usize> = (0..count).filter(|&i| step < targets[i].2).collect();
        let mut active_in = SecretBuffer(vec![Vec::with_capacity(active.len()); m]);
        for p in 0..m {
            for &i in &active {
                active_in[p].push(cur_states[p][i]);
            }
        }
        let mut step_tweaks = Vec::with_capacity(active.len());
        for &i in &active {
            let (kp_idx, chain_idx, _) = targets[i];
            step_tweaks.push([
                Goldilocks::from_u64_reduced(HEM_DOMAIN_WOTS_STEP),
                hem_pack_wots_addr_limb(0, kp_idx, chain_idx, step as u32),
                Goldilocks::ZERO,
                Goldilocks::ZERO,
            ]);
        }
        let next_st = SecretBuffer(eval_spdz_hem_compress12_ff_batch(
            t,
            quorum_pts,
            &active_in,
            pk_seed,
            &step_tweaks,
            vaults,
            pending,
        )?);
        for p in 0..m {
            for (slot, &i) in active.iter().enumerate() {
                cur_states[p][i] = next_st[p][slot];
            }
        }
    }

    Ok(core::mem::take(&mut cur_states.0))
}

/// Derive a [`HemJortsCachedTree`] in the clear from `(dkg_pk_seed, sk_seed_bytes, sk_prf_bytes)`
/// for reference comparison in tests and local custody staging.
pub fn derive_hem_jorts_cached_tree_clear(
    dkg_pk_seed: [u8; 32],
    sk_seed_bytes: &[u8; 32],
    sk_prf_bytes: &[u8; 32],
    active_leaves: usize,
) -> Result<HemJortsCachedTree, Poseidon2MpcError> {
    if active_leaves == 0 || active_leaves > HEM_JORTS_MAX_LEAVES {
        return Err(Poseidon2MpcError::InvalidParams);
    }
    let pk_seed = hem_pk_seed_from_bytes32(&dkg_pk_seed);
    let mut sk_seed =
        hem_expand_secret_bytes32_clear(sk_seed_bytes, pk_seed, HEM_DOMAIN_SK_SEED_EXPAND);
    let mut sk_prf =
        hem_expand_secret_bytes32_clear(sk_prf_bytes, pk_seed, HEM_DOMAIN_SK_PRF_EXPAND);
    let prf_check = hem_prf_check_digest_clear(sk_prf, pk_seed);

    let mut leaves = Vec::with_capacity(HEM_JORTS_MAX_LEAVES);
    for kp in 0..active_leaves {
        let mut endpoints = [[Goldilocks::ZERO; 4]; HEM_WOTS_CHAINS];
        for (r, ep) in endpoints.iter_mut().enumerate().take(HEM_WOTS_CHAINS) {
            let mut cur = hem_wots_base_secret_clear(sk_seed, pk_seed, 0, 0, kp as u32, r as u32);
            for step in 0..(HEM_WOTS_MAX_STEP as u32) {
                cur = hem_wots_step_hash_injective(pk_seed, cur, 0, 0, kp as u32, r as u32, step);
            }
            *ep = cur;
            wipe_goldilocks(&mut cur);
        }
        leaves.push(hem_compress_wots_endpoints_sponge(
            pk_seed, 0, 0, kp as u32, &endpoints,
        ));
    }
    for kp in active_leaves..HEM_JORTS_MAX_LEAVES {
        leaves.push(hem_unassigned_leaf_digest(pk_seed, kp as u32));
    }
    wipe_goldilocks(&mut sk_seed);
    wipe_goldilocks(&mut sk_prf);

    let pk_root =
        hem_merkle_root_from_leaves(pk_seed, &leaves).ok_or(Poseidon2MpcError::InvalidParams)?;
    Ok(HemJortsCachedTree {
        dkg_pk_seed,
        pk: HemJortsPublicKey { pk_seed, pk_root },
        active_leaves,
        leaves,
        prf_check,
    })
}

/// Build the full 64-leaf `Hem`-aggregatable `JortsPoseidon2` public key & leaf cache via
/// dishonest-majority SPDZ MPC (`0` secret reconstruction, `0` Beaver triples, `0` A2B!).
pub fn build_distributed_hem_jorts_key_mpc(
    session_id: [u8; 32],
    t: usize,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<HemJortsCachedTree, Poseidon2MpcError> {
    build_distributed_hem_jorts_key_mpc_with_active_leaves(
        session_id,
        HEM_JORTS_MAX_LEAVES,
        t,
        key_shares,
        vaults,
        party_rngs,
    )
}

/// Build a `Hem`-aggregatable `JortsPoseidon2` public key & height-6 leaf cache in SPDZ MPC with
/// `active_leaves in 1..=64` active `WOTS+C` leaves and domain-separated unassigned leaves above it.
pub fn build_distributed_hem_jorts_key_mpc_with_active_leaves(
    session_id: [u8; 32],
    active_leaves: usize,
    t: usize,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<HemJortsCachedTree, Poseidon2MpcError> {
    if active_leaves == 0 || active_leaves > HEM_JORTS_MAX_LEAVES {
        return Err(Poseidon2MpcError::InvalidParams);
    }
    let (dkg_pk_seed, quorum_pts) = validate_quorum_slices(t, key_shares, vaults, party_rngs)?;
    let pk_seed = hem_pk_seed_from_bytes32(&dkg_pk_seed);
    let m = quorum_pts.len();
    let mut pending = SpdzGoldilocksPendingChecks::new(m);

    let (sk_seed_p, sk_prf_p) = match expand_hem_secret_digests_mpc(
        t,
        &quorum_pts,
        pk_seed,
        key_shares,
        vaults,
        &mut pending,
    ) {
        Ok(pair) => (SecretBuffer(pair.0), SecretBuffer(pair.1)),
        Err(e) => {
            poison_all_on_abort(key_shares, vaults);
            return Err(Poseidon2MpcError::Preprocess(e));
        }
    };

    let prf_in: Vec<Vec<[AuthGlWire; 4]>> = (0..m).map(|p| vec![sk_prf_p[p]]).collect();
    let prf_tweak = [[
        Goldilocks::from_u64_reduced(HEM_DOMAIN_PRF_CHECK),
        Goldilocks::ZERO,
        Goldilocks::ZERO,
        Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV),
    ]];
    let prf_chk_p = SecretBuffer(
        match eval_spdz_hem_compress12_ff_batch(
            t,
            &quorum_pts,
            &prf_in,
            pk_seed,
            &prf_tweak,
            vaults,
            &mut pending,
        ) {
            Ok(v) => v,
            Err(e) => {
                poison_all_on_abort(key_shares, vaults);
                return Err(Poseidon2MpcError::Preprocess(e));
            }
        },
    );

    let mut targets = Vec::with_capacity(active_leaves * HEM_WOTS_CHAINS);
    for kp in 0..active_leaves {
        for r in 0..HEM_WOTS_CHAINS {
            targets.push((kp as u32, r as u32, HEM_WOTS_MAX_STEP));
        }
    }
    let mut cut_states = SecretBuffer(
        match eval_hem_wots_chains_native_spdz(
            t,
            &quorum_pts,
            pk_seed,
            &sk_seed_p,
            &targets,
            vaults,
            &mut pending,
        ) {
            Ok(s) => s,
            Err(e) => {
                poison_all_on_abort(key_shares, vaults);
                return Err(Poseidon2MpcError::Preprocess(e));
            }
        },
    );
    for p in 0..m {
        secret_vec_push(&mut cut_states[p], prf_chk_p[p][0]);
    }

    let opened = flush_verify_and_open_hem_digests4(
        &session_id,
        "hem_keygen_endpoints_and_prf",
        t,
        &quorum_pts,
        &cut_states,
        &mut pending,
        key_shares,
        vaults,
        party_rngs,
    )?;

    let prf_check = opened[active_leaves * HEM_WOTS_CHAINS];
    let mut leaves = Vec::with_capacity(HEM_JORTS_MAX_LEAVES);
    for kp in 0..active_leaves {
        let base = kp * HEM_WOTS_CHAINS;
        let endpoints: [HemDigest4; HEM_WOTS_CHAINS] =
            core::array::from_fn(|r| opened[base + r]);
        leaves.push(hem_compress_wots_endpoints_sponge(
            pk_seed, 0, 0, kp as u32, &endpoints,
        ));
    }
    for kp in active_leaves..HEM_JORTS_MAX_LEAVES {
        leaves.push(hem_unassigned_leaf_digest(pk_seed, kp as u32));
    }

    let pk_root =
        hem_merkle_root_from_leaves(pk_seed, &leaves).ok_or(Poseidon2MpcError::InvalidParams)?;
    let pk = HemJortsPublicKey { pk_seed, pk_root };
    for ks in key_shares.iter_mut() {
        ks.enroll_hem_key_profile(pk, prf_check)?;
    }

    Ok(HemJortsCachedTree {
        dkg_pk_seed,
        pk,
        active_leaves,
        leaves,
        prf_check,
    })
}

/// Authenticate reshared `(t', n')` SPDZ key shares against an existing [`HemJortsCachedTree`]
/// without reconstructing `SK.seed` or `SK.prf`: recomputes `leaf[0]` and `prf_check` in SPDZ MPC
/// (`515` permutations = `60,770` `pow7` tuples), verifies both match `cache` (which is Merkle-bound
/// to `cache.pk.pk_root`), and enrolls `(cache.pk, cache.prf_check)` on every share.
pub fn verify_reshared_hem_jorts_key_mpc(
    session_id: [u8; 32],
    cache: &HemJortsCachedTree,
    t: usize,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(), Poseidon2MpcError> {
    if !cache.verify_consistency() {
        return Err(Poseidon2MpcError::CachedSubtreeMismatch);
    }
    let (dkg_pk_seed, quorum_pts) = validate_quorum_slices(t, key_shares, vaults, party_rngs)?;
    if !ct_eq_bytes32(&dkg_pk_seed, &cache.dkg_pk_seed) {
        return Err(Poseidon2MpcError::PublicSeedMismatch);
    }
    let pk_seed = cache.pk.pk_seed;
    let m = quorum_pts.len();
    let mut pending = SpdzGoldilocksPendingChecks::new(m);

    let (sk_seed_p, sk_prf_p) = match expand_hem_secret_digests_mpc(
        t,
        &quorum_pts,
        pk_seed,
        key_shares,
        vaults,
        &mut pending,
    ) {
        Ok(pair) => (SecretBuffer(pair.0), SecretBuffer(pair.1)),
        Err(e) => {
            poison_all_on_abort(key_shares, vaults);
            return Err(Poseidon2MpcError::Preprocess(e));
        }
    };

    let prf_in: Vec<Vec<[AuthGlWire; 4]>> = (0..m).map(|p| vec![sk_prf_p[p]]).collect();
    let prf_tweak = [[
        Goldilocks::from_u64_reduced(HEM_DOMAIN_PRF_CHECK),
        Goldilocks::ZERO,
        Goldilocks::ZERO,
        Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV),
    ]];
    let prf_chk_p = SecretBuffer(
        match eval_spdz_hem_compress12_ff_batch(
            t,
            &quorum_pts,
            &prf_in,
            pk_seed,
            &prf_tweak,
            vaults,
            &mut pending,
        ) {
            Ok(v) => v,
            Err(e) => {
                poison_all_on_abort(key_shares, vaults);
                return Err(Poseidon2MpcError::Preprocess(e));
            }
        },
    );

    let targets: Vec<(u32, u32, usize)> = (0..HEM_WOTS_CHAINS)
        .map(|r| (0u32, r as u32, HEM_WOTS_MAX_STEP))
        .collect();
    let mut cut_states = SecretBuffer(
        match eval_hem_wots_chains_native_spdz(
            t,
            &quorum_pts,
            pk_seed,
            &sk_seed_p,
            &targets,
            vaults,
            &mut pending,
        ) {
            Ok(s) => s,
            Err(e) => {
                poison_all_on_abort(key_shares, vaults);
                return Err(Poseidon2MpcError::Preprocess(e));
            }
        },
    );
    for p in 0..m {
        secret_vec_push(&mut cut_states[p], prf_chk_p[p][0]);
    }

    let opened = flush_verify_and_open_hem_digests4(
        &session_id,
        "hem_reshare_verify_cut",
        t,
        &quorum_pts,
        &cut_states,
        &mut pending,
        key_shares,
        vaults,
        party_rngs,
    )?;

    let endpoints0: [HemDigest4; HEM_WOTS_CHAINS] = core::array::from_fn(|r| opened[r]);
    let leaf0 = hem_compress_wots_endpoints_sponge(pk_seed, 0, 0, 0, &endpoints0);
    let prf_check = opened[HEM_WOTS_CHAINS];
    if leaf0 != cache.leaves[0] || prf_check != cache.prf_check {
        poison_all_on_abort(key_shares, vaults);
        return Err(Poseidon2MpcError::KeyProfileMismatch);
    }

    for ks in key_shares.iter_mut() {
        ks.enroll_hem_key_profile(cache.pk, cache.prf_check)?;
    }
    Ok(())
}

fn validate_enrolled_hem_profile(
    cache: &HemJortsCachedTree,
    quorum_pk_seed: &[u8; 32],
    key_shares: &[&mut Poseidon2SpdzAuthenticatedKeyShare],
) -> Result<(), Poseidon2MpcError> {
    if !ct_eq_bytes32(&cache.dkg_pk_seed, quorum_pk_seed) {
        return Err(Poseidon2MpcError::PublicSeedMismatch);
    }
    for ks in key_shares {
        match ks.enrolled_hem_profile {
            None => return Err(Poseidon2MpcError::KeyNotEnrolled),
            Some((epk, eprf)) => {
                if epk != cache.pk || eprf != cache.prf_check {
                    return Err(Poseidon2MpcError::KeyProfileMismatch);
                }
            }
        }
    }
    Ok(())
}

#[expect(
    clippy::too_many_arguments,
    reason = "Core MPC evaluation takes session, cache, quorum, epoch, message mu, grind bound and party state"
)]
fn sign_hem_jorts_poseidon2_mpc_core(
    session_id: &[u8; 32],
    cache: &HemJortsCachedTree,
    t: usize,
    quorum_pts: &[Goldilocks],
    epoch: u64,
    msg: &[u8],
    mu_bytes: &[u8; 32],
    mu: HemDigest5,
    max_grind: u32,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<HemJortsSignature, Poseidon2MpcError> {
    let kp_usize = usize::try_from(epoch)
        .map_err(|_| Poseidon2MpcError::EpochLatch(EpochLatchError::Exhausted))?;
    if kp_usize >= cache.active_leaves {
        return Err(Poseidon2MpcError::EpochLatch(EpochLatchError::Exhausted));
    }
    let kp_u32 = kp_usize as u32;
    let m = quorum_pts.len();

    let transcript = crate::sponge::keccak::encode_multi_frame(&[
        session_id,
        &epoch.to_le_bytes(),
        mu_bytes,
    ]);
    for rng in party_rngs.iter_mut() {
        rng.hedge_transcript(&transcript);
    }

    // Cut 1: expand `(sk_seed, sk_prf)` (2 perms) + derive `r_rand` (2 perms) and open `r_rand`
    // behind the two-stage committed SPDZ `MacCheck` barrier.
    let mut pending1 = SpdzGoldilocksPendingChecks::new(m);
    let (sk_seed_p, sk_prf_p) = match expand_hem_secret_digests_mpc(
        t,
        quorum_pts,
        cache.pk.pk_seed,
        key_shares,
        vaults,
        &mut pending1,
    ) {
        Ok(pair) => (SecretBuffer(pair.0), SecretBuffer(pair.1)),
        Err(e) => {
            poison_all_on_abort(key_shares, vaults);
            return Err(Poseidon2MpcError::Preprocess(e));
        }
    };

    let mut r_states = SecretBuffer(vec![Vec::with_capacity(1); m]);
    for p in 0..m {
        let alpha_p = vaults[p].mac_alpha_share;
        let c = |g: Goldilocks| AuthGlWire::public_const(g, alpha_p);
        r_states[p].push([
            sk_prf_p[p][0],
            sk_prf_p[p][1],
            sk_prf_p[p][2],
            sk_prf_p[p][3],
            c(cache.pk.pk_seed[0]),
            c(cache.pk.pk_seed[1]),
            c(cache.pk.pk_seed[2]),
            c(cache.pk.pk_seed[3]),
            c(Goldilocks::from_u64_reduced(HEM_DOMAIN_PRF_MSG)),
            c(Goldilocks::from_u64_reduced(epoch)),
            c(mu[4]),
            c(Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV)),
        ]);
    }
    if let Err(e) =
        eval_spdz_poseidon2_perm12_batch(t, quorum_pts, &mut r_states, vaults, &mut pending1)
    {
        poison_all_on_abort(key_shares, vaults);
        return Err(Poseidon2MpcError::Preprocess(e));
    }
    for p in 0..m {
        let alpha_p = vaults[p].mac_alpha_share;
        for i in 0..4 {
            r_states[p][0][i] = r_states[p][0][i].add(AuthGlWire::public_const(mu[i], alpha_p));
        }
    }
    if let Err(e) =
        eval_spdz_poseidon2_perm12_batch(t, quorum_pts, &mut r_states, vaults, &mut pending1)
    {
        poison_all_on_abort(key_shares, vaults);
        return Err(Poseidon2MpcError::Preprocess(e));
    }

    let r_cut: Vec<Vec<[AuthGlWire; 4]>> = (0..m)
        .map(|p| {
            vec![[
                r_states[p][0][0],
                r_states[p][0][1],
                r_states[p][0][2],
                r_states[p][0][3],
            ]]
        })
        .collect();
    let opened_r = flush_verify_and_open_hem_digests4(
        session_id,
        "hem_sign_r_rand_cut",
        t,
        quorum_pts,
        &r_cut,
        &mut pending1,
        key_shares,
        vaults,
        party_rngs,
    )?;
    let r_rand = opened_r[0];

    let (tsw_ctr, digits) = hem_grind_stateful_tsw_digits(
        cache.pk.pk_seed,
        cache.pk.pk_root,
        r_rand,
        mu,
        kp_u32,
        max_grind,
    )
    .ok_or(Poseidon2MpcError::TswGrindExhausted)?;

    // Cut 2: evaluate the 128 base secrets + 192 step transitions in native `[Goldilocks; 4]` SPDZ
    // (`0` Beaver triples, `0` A2B!) and open `wots_chains[0..128]` behind `MacCheck`.
    let mut pending2 = SpdzGoldilocksPendingChecks::new(m);
    let targets: Vec<(u32, u32, usize)> = digits
        .iter()
        .enumerate()
        .map(|(r, &d)| (kp_u32, r as u32, d as usize))
        .collect();
    let chain_states = SecretBuffer(
        match eval_hem_wots_chains_native_spdz(
            t,
            quorum_pts,
            cache.pk.pk_seed,
            &sk_seed_p,
            &targets,
            vaults,
            &mut pending2,
        ) {
            Ok(s) => s,
            Err(e) => {
                poison_all_on_abort(key_shares, vaults);
                return Err(Poseidon2MpcError::Preprocess(e));
            }
        },
    );
    let wots_chains = flush_verify_and_open_hem_digests4(
        session_id,
        "hem_sign_wots_chains_cut",
        t,
        quorum_pts,
        &chain_states,
        &mut pending2,
        key_shares,
        vaults,
        party_rngs,
    )?;

    let (merkle_path, root_chk) = hem_merkle_auth_path(cache.pk.pk_seed, &cache.leaves, kp_usize)
        .ok_or(Poseidon2MpcError::CachedSubtreeMismatch)?;
    if root_chk != cache.pk.pk_root {
        return Err(Poseidon2MpcError::CachedSubtreeMismatch);
    }

    let sig = HemJortsSignature {
        r_rand,
        stateful_leaf_idx: kp_u32,
        tsw_ctr,
        wots_chains,
        merkle_path,
    };
    if !verify_hem_jorts_signature(&cache.pk, msg, &sig) {
        return Err(Poseidon2MpcError::SignatureSelfCheckFailed);
    }
    Ok(sig)
}

/// Sign `msg` under stateful `Hem`-aggregatable `JortsPoseidon2` (`w=4, chains=128, sum=192, height=6`)
/// in dishonest-majority $t$-of-$n$ Shamir SPDZ (`0` intermediate A2B, exact `4,328`-byte wire format):
/// - Enforces committee-wide [`EpochLatchCertificate`] / [`StatefulEpochLatch`] reservation on
///   `mu_bytes = hem_compute_message_mu(&cache.pk, msg).0` **strictly before** any MPC wire opens;
/// - Evaluates `r_rand` and all 128 `WOTS+C` chains in native `[Goldilocks; 4]` SPDZ (`38,232` `pow7` tuples);
/// - Self-checks [`verify_hem_jorts_signature`] before returning `(epoch, HemJortsSignature)`.
#[expect(
    clippy::too_many_arguments,
    reason = "Stateful MPC signing binds session, leaf cache, threshold, latch certificate, latches, message and party state"
)]
pub fn sign_hem_jorts_poseidon2_mpc_cached<L: StatefulEpochLatch>(
    session_id: [u8; 32],
    cache: &HemJortsCachedTree,
    t: usize,
    latch_cert: Option<&EpochLatchCertificate>,
    latches: &mut [&mut L],
    msg: &[u8],
    max_grind: u32,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(u64, HemJortsSignature), Poseidon2MpcError> {
    if !cache.verify_consistency() {
        return Err(Poseidon2MpcError::CachedSubtreeMismatch);
    }
    if latches.len() != key_shares.len() {
        return Err(Poseidon2MpcError::InvalidQuorum {
            t,
            n: latches.len(),
        });
    }
    let (quorum_pk_seed, quorum_pts) = validate_quorum_slices(t, key_shares, vaults, party_rngs)?;
    validate_enrolled_hem_profile(cache, &quorum_pk_seed, key_shares)?;

    let committee_size = key_shares[0].committee_size;
    let (mu_bytes, mu) = hem_compute_message_mu(&cache.pk, msg);
    let latch_pk = cache.pk.latch_pq_public_key(cache.dkg_pk_seed);

    let Some(first) = latches.first() else {
        return Err(Poseidon2MpcError::InvalidQuorum { t, n: 0 });
    };
    let candidate_epoch = match latch_cert {
        Some(cert) => cert.epoch(),
        None => first.peek_next_epoch(),
    };
    if candidate_epoch >= cache.active_leaves as u64 {
        let pinned_authority = resolve_enrolled_latch_authority(key_shares)?;
        check_committee_latch_authorisation(
            &latch_pk,
            t,
            committee_size,
            latches.len(),
            pinned_authority,
            latch_cert,
            candidate_epoch,
            &mu_bytes,
        )?;
        return Err(Poseidon2MpcError::EpochLatch(EpochLatchError::Exhausted));
    }

    let latch_params = PqHashParams {
        w: HEM_WOTS_BASE_W,
        ell1: HEM_WOTS_CHAINS,
        max_sigs_log2: HEM_JORTS_XMSS_HEIGHT as u32,
        num_layers: 1,
        subtree_height: HEM_JORTS_XMSS_HEIGHT,
        fors_trees: 0,
        fors_height: 0,
        stateful: true,
    };
    let ep0 = {
        let pinned_authority = resolve_enrolled_latch_authority(key_shares)?;
        reserve_authorised_epoch(
            &latch_params,
            &latch_pk,
            t,
            committee_size,
            pinned_authority,
            latch_cert,
            latches,
            &mu_bytes,
        )?
    };
    if ep0 >= cache.active_leaves as u64 {
        return Err(Poseidon2MpcError::EpochLatch(EpochLatchError::Exhausted));
    }

    let sig = sign_hem_jorts_poseidon2_mpc_core(
        &session_id,
        cache,
        t,
        &quorum_pts,
        ep0,
        msg,
        &mu_bytes,
        mu,
        max_grind,
        key_shares,
        vaults,
        party_rngs,
    )?;
    Ok((ep0, sig))
}

/// Safe crash-recovery retry for `Hem`-aggregatable `JortsPoseidon2` (`[P0-04]`):
/// verifies `latch.retry_latched_epoch(epoch, &mu_bytes)` across all participating latches without
/// advancing any latch and reproduces the exact deterministic `HemJortsSignature`.
#[expect(
    clippy::too_many_arguments,
    reason = "Crash-recovery retry binds session, leaf cache, threshold, latch certificate, latches, epoch, message and party state"
)]
pub fn retry_hem_jorts_poseidon2_mpc_cached<L: StatefulEpochLatch>(
    session_id: [u8; 32],
    cache: &HemJortsCachedTree,
    t: usize,
    latch_cert: Option<&EpochLatchCertificate>,
    latches: &mut [&mut L],
    epoch: u64,
    msg: &[u8],
    max_grind: u32,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<HemJortsSignature, Poseidon2MpcError> {
    if !cache.verify_consistency() {
        return Err(Poseidon2MpcError::CachedSubtreeMismatch);
    }
    if latches.len() != key_shares.len() {
        return Err(Poseidon2MpcError::InvalidQuorum {
            t,
            n: latches.len(),
        });
    }
    let (quorum_pk_seed, quorum_pts) = validate_quorum_slices(t, key_shares, vaults, party_rngs)?;
    validate_enrolled_hem_profile(cache, &quorum_pk_seed, key_shares)?;

    let committee_size = key_shares[0].committee_size;
    let (mu_bytes, mu) = hem_compute_message_mu(&cache.pk, msg);
    let latch_pk = cache.pk.latch_pq_public_key(cache.dkg_pk_seed);

    {
        let pinned_authority = resolve_enrolled_latch_authority(key_shares)?;
        check_committee_latch_authorisation(
            &latch_pk,
            t,
            committee_size,
            latches.len(),
            pinned_authority,
            latch_cert,
            epoch,
            &mu_bytes,
        )?;
    }
    if epoch >= cache.active_leaves as u64 {
        return Err(Poseidon2MpcError::EpochLatch(EpochLatchError::Exhausted));
    }
    for l in latches.iter_mut() {
        let ep = l.retry_latched_epoch(epoch, &mu_bytes)?;
        if ep != epoch {
            return Err(Poseidon2MpcError::EpochLatch(
                EpochLatchError::EquivocationRefused,
            ));
        }
    }

    sign_hem_jorts_poseidon2_mpc_core(
        &session_id,
        cache,
        t,
        &quorum_pts,
        epoch,
        msg,
        &mu_bytes,
        mu,
        max_grind,
        key_shares,
        vaults,
        party_rngs,
    )
}

#[cfg(test)]
mod tests {
    #[test]
    fn intermediate_mac_failure_precedes_cut_access() {
        let points = [Goldilocks::ONE, Goldilocks::from_u64_reduced(2)];
        let mut vaults: Vec<_> = points
            .iter()
            .enumerate()
            .map(|(p, &x)| PreprocessedPoseidonPartyVault::empty_for_barrier_test(p, x))
            .collect();
        let mut keys: Vec<_> = points
            .iter()
            .enumerate()
            .map(|(p, &x)| Poseidon2SpdzAuthenticatedKeyShare {
                party_id: p,
                committee_size: 2,
                eval_point: x,
                pk_seed: [0; 32],
                mac_alpha_share: GoldilocksExt2::ONE,
                sk_seed_bytes: [Goldilocks::ZERO; 32],
                sk_seed_macs: [GoldilocksExt2::ZERO; 32],
                sk_prf_bytes: [Goldilocks::ZERO; 32],
                sk_prf_macs: [GoldilocksExt2::ZERO; 32],
                enrolled_profile: None,
                enrolled_hem_profile: None,
                enrolled_latch_authority: None,
                poisoned: false,
            })
            .collect();
        let mut pending = SpdzGoldilocksPendingChecks::new(2);
        pending.shares_per_party = vec![vec![Goldilocks::ONE]; 2];
        pending.macs_per_party = vec![vec![GoldilocksExt2::ZERO]; 2];
        let mut rngs = make_rngs(2, 45);
        let cut = vec![
            vec![
                [AuthGlWire {
                    val: Goldilocks::ZERO,
                    mac: GoldilocksExt2::ZERO,
                }; 4],
            ],
            vec![],
        ];
        // The malformed second cut would panic if the implementation reached it.
        let result = flush_verify_and_open_cut_states4(
            &[42; 32],
            "barrier",
            2,
            &points,
            &cut,
            &vec![vec![]; 2],
            &mut pending,
            &mut keys.iter_mut().collect::<Vec<_>>(),
            &mut vaults.iter_mut().collect::<Vec<_>>(),
            &mut rngs,
        );
        assert!(matches!(
            result,
            Err(Poseidon2MpcError::Preprocess(
                PreprocessError::MacCheckFailed {
                    accused_party: None,
                    ..
                }
            ))
        ));
        assert!(vaults.iter().all(|v| v.is_poisoned()));
    }

    use super::*;
    use crate::dkg::{
        QuorumEpochLatchCluster, run_dealerless_dkg_seed32_goldilocks,
        shamir_reconstruct_seed32_goldilocks,
    };
    use crate::field::goldilocks::GOLDILOCKS_PRIME;
    use crate::sponge::poseidon2::poseidon2_hash32;
    use crate::tsw_baggy::{
        MonotonicEpochLatch, PqSecretKey, compute_wots_pk, derive_public_key,
        derive_stateless_r_rand, eval_single_sign_stateful, retry_single_sign_stateful,
    };

    fn make_rngs(n: usize, tag: u8) -> Vec<PartyPrivateRng> {
        (0..n)
            .map(|p| {
                PartyPrivateRng::from_seed([tag.wrapping_add(p as u8 + 1); 32], b"POS2_MPC_TEST")
            })
            .collect()
    }

    #[test]
    fn test_canonical_a2b_boundary_values_exact_no_wraparound() {
        let sid = [0x31; 32];
        let t = 2usize;
        let n = 2usize;
        let pts: Vec<Goldilocks> = (1..=2).map(Goldilocks::from_u64_reduced).collect();
        let mut rngs = make_rngs(n, 0x10);
        let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut rngs);

        let (alpha_c, alpha_sh) = spdz_setup_alpha_goldilocks(&sid, t, &pts, &mut rngs).unwrap();
        let mut vaults = run_dealerless_pi_pow7_with_alpha(
            sid, t, &pts, 0, 0, 0, &alpha_c, &alpha_sh, &mut mesh, &mut rngs,
        )
        .unwrap();

        // This test exercises the online canonical A2B circuit. Offline mask
        // generation/sacrifice has dedicated adversarial preprocessing tests.
        PreprocessedPoseidonPartyVault::fill_two_party_online_fixture(
            &mut vaults,
            (0, 2 * POSEIDON2_BEAVER_PER_A2B_HASH32, 8),
            &mut rngs[0],
        );

        // Test all critical Goldilocks edge cases: 0, 1, 2^32 - 1, 2^32, p - 2, p - 1, random!
        let s0 = [
            Goldilocks::ZERO,
            Goldilocks::ONE,
            Goldilocks::from_u64_reduced((1u64 << 32) - 1),
            Goldilocks::from_u64_reduced(1u64 << 32),
        ];
        let s1 = [
            Goldilocks::from_u64_reduced(GOLDILOCKS_PRIME - 2),
            Goldilocks::from_u64_reduced(GOLDILOCKS_PRIME - 1),
            Goldilocks::from_u64_reduced(0xDEAD_BEEF_CAFE_BABEu64),
            Goldilocks::from_u64_reduced(0xFFFF_FFFE_FFFF_FFFFu64),
        ];

        // Share s0 and s1 genuinely with random degree-1 polynomials (NOT public constants!)
        let mut in_per_party = vec![vec![[AuthGlWire::ZERO; 4]; 2]; t];
        let alpha_global =
            crate::preprocessing::open_and_check_degree_ext2(t, &pts, &alpha_sh, "ag").unwrap();
        for (item, arr) in [s0, s1].iter().enumerate() {
            for lane in 0..4 {
                let x = arr[lane];
                let slope = rngs[0].next_goldilocks();
                let mac_global = alpha_global.mul_base(x);
                let mac_slope = rngs[0].next_ext2();
                for p in 0..t {
                    in_per_party[p][item][lane] = AuthGlWire {
                        val: x + slope * pts[p],
                        mac: mac_global + mac_slope.mul_base(pts[p]),
                    };
                }
            }
        }

        let mut v_refs: Vec<&mut PreprocessedPoseidonPartyVault> =
            vaults.iter_mut().take(t).collect();
        let mut pending = SpdzGoldilocksPendingChecks::new(t);
        let out_bytes = eval_spdz_canonical_a2b_state4_batch_to_bytes32(
            t,
            &pts[..t],
            &in_per_party,
            &mut v_refs,
            &mut pending,
        )
        .unwrap();

        let mut dummy_ks = [
            Poseidon2SpdzAuthenticatedKeyShare {
                party_id: 0,
                committee_size: 3,
                eval_point: pts[0],
                pk_seed: [0; 32],
                mac_alpha_share: v_refs[0].mac_alpha_share,
                sk_seed_bytes: [Goldilocks::ZERO; 32],
                sk_seed_macs: [GoldilocksExt2::ZERO; 32],
                sk_prf_bytes: [Goldilocks::ZERO; 32],
                sk_prf_macs: [GoldilocksExt2::ZERO; 32],
                enrolled_profile: None,
                enrolled_hem_profile: None,
                enrolled_latch_authority: None,
                poisoned: false,
            },
            Poseidon2SpdzAuthenticatedKeyShare {
                party_id: 1,
                committee_size: 3,
                eval_point: pts[1],
                pk_seed: [0; 32],
                mac_alpha_share: v_refs[1].mac_alpha_share,
                sk_seed_bytes: [Goldilocks::ZERO; 32],
                sk_seed_macs: [GoldilocksExt2::ZERO; 32],
                sk_prf_bytes: [Goldilocks::ZERO; 32],
                sk_prf_macs: [GoldilocksExt2::ZERO; 32],
                enrolled_profile: None,
                enrolled_hem_profile: None,
                enrolled_latch_authority: None,
                poisoned: false,
            },
        ];
        let (k0, k1) = dummy_ks.split_at_mut(1);
        let mut ks_refs = [&mut k0[0], &mut k1[0]];
        let empty_st = vec![Vec::new(); t];
        let (_, opened_bytes) = flush_verify_and_open_cut_states4(
            &sid,
            "a2b_edge_test",
            t,
            &pts[..t],
            &empty_st,
            &out_bytes,
            &mut pending,
            &mut ks_refs,
            &mut v_refs,
            &mut rngs[..t],
        )
        .unwrap();

        for (item, arr) in [s0, s1].iter().enumerate() {
            let mut exp = [0u8; 32];
            for lane in 0..4 {
                exp[8 * lane..8 * (lane + 1)].copy_from_slice(&arr[lane].to_be_bytes());
            }
            assert_eq!(opened_bytes[item], exp);
        }
    }

    /// Dishonest-majority 2-of-2 quorum (`2t - 1 = 3 > 2`: 1 of 2 signers may be actively corrupt)
    /// from a real dealerless Goldilocks DKG, with `budget = (pow7, beaver, a2b)` preprocessing.
    /// The reference single-signer key is reconstructed ONLY inside the test harness.
    fn setup_two_party_poseidon2_quorum(
        budget: (usize, usize, usize),
    ) -> (
        Vec<Poseidon2SpdzAuthenticatedKeyShare>,
        Vec<PreprocessedPoseidonPartyVault>,
        Vec<PartyPrivateRng>,
        PqSecretKey,
    ) {
        setup_poseidon2_committee(2, 2, budget)
    }

    /// A `t`-of-`n` committee from a real dealerless Goldilocks DKG, with
    /// `budget = (pow7, beaver, a2b)` preprocessing. The reference single-signer key is
    /// reconstructed ONLY inside the test harness.
    fn setup_poseidon2_committee(
        t: usize,
        n: usize,
        budget: (usize, usize, usize),
    ) -> (
        Vec<Poseidon2SpdzAuthenticatedKeyShare>,
        Vec<PreprocessedPoseidonPartyVault>,
        Vec<PartyPrivateRng>,
        PqSecretKey,
    ) {
        setup_poseidon2_committee_material(t, n, budget, false)
    }

    fn setup_poseidon2_committee_material(
        t: usize,
        n: usize,
        budget: (usize, usize, usize),
        online_fixture: bool,
    ) -> (
        Vec<Poseidon2SpdzAuthenticatedKeyShare>,
        Vec<PreprocessedPoseidonPartyVault>,
        Vec<PartyPrivateRng>,
        PqSecretKey,
    ) {
        let sid = [0x52; 32];
        let pts: Vec<Goldilocks> = (1..=n as u64).map(Goldilocks::from_u64_reduced).collect();
        let mut rngs = make_rngs(n, 0x30);
        let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut rngs);

        let dkg_seed =
            run_dealerless_dkg_seed32_goldilocks([0x61; 32], t, &pts, &mut mesh, &mut rngs)
                .unwrap();
        let dkg_prf =
            run_dealerless_dkg_seed32_goldilocks([0x62; 32], t, &pts, &mut mesh, &mut rngs)
                .unwrap();
        let pk_seed = dkg_seed.1;

        let production_budget = if online_fixture { (0, 0, 0) } else { budget };
        let (key_shares, mut vaults) = authenticate_poseidon_dkg_shares_and_preprocess(
            [0x63; 32],
            t,
            &pts,
            pk_seed,
            &dkg_seed.0,
            &dkg_prf.0,
            production_budget.0,
            production_budget.1,
            production_budget.2,
            &mut mesh,
            &mut rngs,
        )
        .unwrap();

        if online_fixture {
            PreprocessedPoseidonPartyVault::fill_two_party_online_fixture(
                &mut vaults,
                budget,
                &mut rngs[0],
            );
        }
        let ref_sk = PqSecretKey {
            sk_seed: shamir_reconstruct_seed32_goldilocks(
                &dkg_seed.0[..t].iter().collect::<Vec<_>>(),
            )
            .unwrap(),
            sk_prf: shamir_reconstruct_seed32_goldilocks(
                &dkg_prf.0[..t].iter().collect::<Vec<_>>(),
            )
            .unwrap(),
            pk_seed,
        };
        (key_shares, vaults, rngs, ref_sk)
    }

    fn remaining_budget(v: &PreprocessedPoseidonPartyVault) -> (usize, usize, usize) {
        (v.remaining_pow7(), v.remaining_beaver(), v.remaining_a2b())
    }

    fn spent(before: (usize, usize, usize), after: (usize, usize, usize)) -> (usize, usize, usize) {
        (before.0 - after.0, before.1 - after.1, before.2 - after.2)
    }

    /// Flip one bit of one leaf, swap the public key, name the wrong layer, add a leaf.
    fn mismatched_caches(cache: &DkgCachedSubtrees) -> [DkgCachedSubtrees; 4] {
        let mut corrupted_leaf = cache.clone();
        corrupted_leaf.top_leaves[0][7] ^= 0x01;
        let mut other_pk = cache.clone();
        other_pk.pk.pk_root[0] ^= 0x80;
        let mut wrong_layer = cache.clone();
        wrong_layer.top_layer ^= 1;
        let mut wrong_len = cache.clone();
        wrong_len.top_leaves.push([0u8; 32]);
        [corrupted_leaf, other_pk, wrong_layer, wrong_len]
    }

    /// A top-subtree leaf cache that does not belong to `(params, pk)` is refused by every `_cached`
    /// entry point before an epoch is latched or any MPC runs. No preprocessing is provisioned
    /// here, so reaching MPC at all would fail with a different error.
    #[test]
    fn test_poseidon2_mpc_cached_top_subtree_rejects_mismatched_cache() {
        let params = PqHashParams {
            w: 4,
            ell1: 128,
            max_sigs_log2: 2,
            num_layers: 2,
            subtree_height: 1,
            fors_trees: 0,
            fors_height: 0,
            stateful: true,
        };
        let stateless_params = PqHashParams {
            fors_trees: 1,
            fors_height: 1,
            stateful: false,
            ..params
        };
        assert!(params.is_well_formed() && stateless_params.is_well_formed());
        let t = 2usize;
        let (mut key_shares, mut vaults, mut rngs, ref_sk) =
            setup_two_party_poseidon2_quorum((0, 0, 0));
        let (ks0, ks1) = key_shares.split_at_mut(1);
        let (v0, v1) = vaults.split_at_mut(1);
        let mut ks_refs = [&mut ks0[0], &mut ks1[0]];
        let mut v_refs = [&mut v0[0], &mut v1[0]];

        // The true top-subtree leaves, derived in the clear from the harness-only reference key.
        let pk = derive_public_key(Poseidon2Suite, &params, &ref_sk);
        assert_eq!(
            pk,
            derive_public_key(Poseidon2Suite, &stateless_params, &ref_sk)
        );
        let cache = DkgCachedSubtrees {
            top_layer: 1,
            top_leaves: (0..2u32)
                .map(|kp| compute_wots_pk(Poseidon2Suite, &params, &ref_sk, 1, 0, kp))
                .collect(),
            pk,
        };
        assert_eq!(
            validate_top_subtree_cache(&params, &pk, Some(&cache)),
            Ok(())
        );
        assert_eq!(validate_top_subtree_cache(&params, &pk, None), Ok(()));

        let msg = b"mismatched top subtree cache";
        let mut l0 = MonotonicEpochLatch::new(3);
        let mut l1 = MonotonicEpochLatch::new(3);
        let mut foreign_pk = pk;
        foreign_pk.pk_seed[31] ^= 0x01;
        let bad_caches = mismatched_caches(&cache);
        let attempts = bad_caches
            .iter()
            .map(|bad| (bad, pk))
            .chain(core::iter::once((&cache, foreign_pk)));
        for (bad_cache, with_pk) in attempts {
            assert_eq!(
                validate_top_subtree_cache(&params, &with_pk, Some(bad_cache)),
                Err(Poseidon2MpcError::CachedSubtreeMismatch)
            );
            let stateful = sign_jorts_poseidon2_mpc_cached(
                [0x69; 32],
                &params,
                &with_pk,
                Some(bad_cache),
                t,
                None,
                &mut [&mut l0, &mut l1],
                msg,
                100_000,
                &mut ks_refs,
                &mut v_refs,
                &mut rngs,
            );
            assert_eq!(stateful, Err(Poseidon2MpcError::CachedSubtreeMismatch));
            let retry = retry_jorts_poseidon2_mpc_cached(
                [0x6a; 32],
                &params,
                &with_pk,
                Some(bad_cache),
                t,
                None,
                &mut [&mut l0, &mut l1],
                3,
                msg,
                100_000,
                &mut ks_refs,
                &mut v_refs,
                &mut rngs,
            );
            assert_eq!(retry, Err(Poseidon2MpcError::CachedSubtreeMismatch));
            let stateless = sign_stateless_tsw_poseidon2_mpc_cached(
                [0x6b; 32],
                &stateless_params,
                &with_pk,
                Some(bad_cache),
                t,
                msg,
                100_000,
                &mut ks_refs,
                &mut v_refs,
                &mut rngs,
            );
            assert_eq!(stateless, Err(Poseidon2MpcError::CachedSubtreeMismatch));
        }
        // Nothing was latched and nothing was burned.
        assert_eq!(l0, MonotonicEpochLatch::new(3));
        assert_eq!(l1, MonotonicEpochLatch::new(3));
        assert!(!ks_refs[0].poisoned && !ks_refs[1].poisoned);
        assert!(!v_refs[0].is_poisoned() && !v_refs[1].is_poisoned());
    }

    /// A signature made with the keygen's top-subtree leaf cache is byte-identical to the uncached
    /// one and spends exactly one full subtree less preprocessing; a cache that does not belong
    /// to `(params, pk)` yields no signature.
    ///
    /// Real DKG and key authentication, with trusted authenticated preprocessing fixtures
    /// for the online protocol. Dealerless material generation has separate integration tests.
    #[test]
    fn test_poseidon2_mpc_cached_top_subtree_signature_byte_identical() {
        let params = PqHashParams {
            w: 4,
            ell1: 128,
            max_sigs_log2: 1,
            num_layers: 1,
            subtree_height: 1,
            fors_trees: 0,
            fors_height: 0,
            stateful: true,
        };
        assert!(params.is_well_formed());
        let t = 2usize;
        let kg = required_poseidon2_keygen_preprocessing_budget(&params);
        let sg = required_poseidon2_sign_preprocessing_budget(&params);
        let sgc = required_poseidon2_sign_preprocessing_budget_cached(&params);
        assert_eq!((sg.0 - sgc.0, sg.1 - sgc.1, sg.2 - sgc.2), kg);

        // Keygen + one uncached signature + a cached signature and a cached retry.
        let (mut key_shares, mut vaults, mut rngs, ref_sk) = setup_poseidon2_committee_material(
            2,
            2,
            (
                kg.0 + sg.0 + 2 * sgc.0,
                kg.1 + sg.1 + 2 * sgc.1,
                kg.2 + sg.2 + 2 * sgc.2,
            ),
            true,
        );
        let ref_pk = derive_public_key(Poseidon2Suite, &params, &ref_sk);
        let (ks0, ks1) = key_shares.split_at_mut(1);
        let (v0, v1) = vaults.split_at_mut(1);
        let mut ks_refs = [&mut ks0[0], &mut ks1[0]];
        let mut v_refs = [&mut v0[0], &mut v1[0]];

        // 1. Keygen keeps the top subtree's leaves; they are the reference key's leaves.
        let before = remaining_budget(v_refs[0]);
        let cache = build_distributed_poseidon2_key_cached(
            [0x64; 32],
            &params,
            t,
            &mut ks_refs,
            &mut v_refs,
            &mut rngs,
        )
        .unwrap();
        let spent_keygen = spent(before, remaining_budget(v_refs[0]));
        assert_eq!(spent_keygen, kg);
        assert_eq!(cache.pk, ref_pk);
        assert_eq!(cache.top_layer, 0);
        let ref_leaves: Vec<[u8; 32]> = (0..2u32)
            .map(|kp| compute_wots_pk(Poseidon2Suite, &params, &ref_sk, 0, 0, kp))
            .collect();
        assert_eq!(cache.top_leaves, ref_leaves);
        let pk = cache.pk;

        // 2. Uncached signature at epoch 1 (the second leaf, so the auth path is leaf 0).
        let msg = b"JortsPoseidon2 cached top subtree parity vector";
        let mut a0 = MonotonicEpochLatch::new(1);
        let mut a1 = MonotonicEpochLatch::new(1);
        let before = remaining_budget(v_refs[0]);
        let (ep_plain, sig_plain) = sign_jorts_poseidon2_mpc(
            [0x65; 32],
            &params,
            &pk,
            t,
            None,
            &mut [&mut a0, &mut a1],
            msg,
            100_000,
            &mut ks_refs,
            &mut v_refs,
            &mut rngs,
        )
        .unwrap();
        let spent_plain = spent(before, remaining_budget(v_refs[0]));
        assert_eq!(ep_plain, 1);
        let mut ref_latch = MonotonicEpochLatch::new(1);
        let ref_sig = eval_single_sign_stateful(
            Poseidon2Suite,
            &params,
            &ref_sk,
            &ref_pk,
            &mut ref_latch,
            msg,
            100_000,
        )
        .unwrap();
        assert_eq!(sig_plain, ref_sig);
        let plain_bytes = sig_plain.to_wire_bytes(&params).unwrap();

        // 3. A corrupted leaf or a different public key: no signature, nothing latched or spent.
        let mut b0 = MonotonicEpochLatch::new(1);
        let mut b1 = MonotonicEpochLatch::new(1);
        let before = remaining_budget(v_refs[0]);
        for bad in &mismatched_caches(&cache) {
            let refused = sign_jorts_poseidon2_mpc_cached(
                [0x69; 32],
                &params,
                &pk,
                Some(bad),
                t,
                None,
                &mut [&mut b0, &mut b1],
                msg,
                100_000,
                &mut ks_refs,
                &mut v_refs,
                &mut rngs,
            );
            assert_eq!(refused, Err(Poseidon2MpcError::CachedSubtreeMismatch));
        }
        assert_eq!(remaining_budget(v_refs[0]), before);
        assert_eq!(b0, MonotonicEpochLatch::new(1));
        assert_eq!(b1, MonotonicEpochLatch::new(1));

        // 4. Cached signature on fresh latches: the same bytes, one full subtree less MPC.
        let (ep_cached, sig_cached) = sign_jorts_poseidon2_mpc_cached(
            [0x6c; 32],
            &params,
            &pk,
            Some(&cache),
            t,
            None,
            &mut [&mut b0, &mut b1],
            msg,
            100_000,
            &mut ks_refs,
            &mut v_refs,
            &mut rngs,
        )
        .unwrap();
        let spent_cached = spent(before, remaining_budget(v_refs[0]));
        assert_eq!(ep_cached, 1);
        assert_eq!(sig_cached.to_wire_bytes(&params).unwrap(), plain_bytes);
        assert!(verify_pq_hash_sig(
            Poseidon2Suite,
            &params,
            &pk,
            msg,
            &sig_cached
        ));
        assert_eq!(spent(spent_plain, spent_cached), spent_keygen);

        // 5. Cached crash-retry of the epoch latched in step 2 reproduces the same bytes.
        let retry_cached = retry_jorts_poseidon2_mpc_cached(
            [0x6d; 32],
            &params,
            &pk,
            Some(&cache),
            t,
            None,
            &mut [&mut a0, &mut a1],
            1,
            msg,
            100_000,
            &mut ks_refs,
            &mut v_refs,
            &mut rngs,
        )
        .unwrap();
        assert_eq!(retry_cached.to_wire_bytes(&params).unwrap(), plain_bytes);
    }

    /// The latch gate on its own, without MPC: which signing sets may reserve an epoch, and that
    /// a refusal leaves every latch where it was.
    #[test]
    fn test_committee_latch_gate_full_attendance_certificate_and_lagging_latch() {
        let params = PqHashParams {
            max_sigs_log2: 3,
            num_layers: 1,
            subtree_height: 3,
            ..PqHashParams::COMPACT_JORTS
        };
        assert!(params.is_well_formed());
        let pk = PqPublicKey {
            pk_seed: [0x11; 32],
            pk_root: [0x22; 32],
        };
        let (mu_a, mu_b) = ([0xa1; 32], [0xb2; 32]);
        let bind =
            |epoch: u64, mu: &[u8; 32]| epoch_latch_binding(&pk.pk_seed, &pk.pk_root, epoch, mu);

        // n == t == 2: both members attend, so their two latches are the whole committee.
        let (mut a0, mut a1) = (MonotonicEpochLatch::new(0), MonotonicEpochLatch::new(0));
        assert_eq!(
            reserve_authorised_epoch(
                &params,
                &pk,
                2,
                2,
                None,
                None,
                &mut [&mut a0, &mut a1],
                &mu_a
            ),
            Ok(0)
        );
        assert_eq!((a0.next_epoch(), a1.next_epoch()), (1, 1));
        assert_eq!(a0.in_flight(), Some((0, mu_a)));

        // (t, n) = (2, 3): two members' latches authorise nothing by themselves.
        let mut l = [
            MonotonicEpochLatch::new(0),
            MonotonicEpochLatch::new(0),
            MonotonicEpochLatch::new(0),
        ];
        let [l0, l1, l2] = &mut l;
        assert_eq!(
            reserve_authorised_epoch(
                &params,
                &pk,
                2,
                3,
                None,
                None,
                &mut [&mut *l0, &mut *l1],
                &mu_a
            ),
            Err(Poseidon2MpcError::LatchCertificateRequired {
                signers: 2,
                committee: 3
            })
        );
        assert_eq!((l0.next_epoch(), l1.next_epoch()), (0, 0));

        // All three attend: accepted without a certificate.
        assert_eq!(
            reserve_authorised_epoch(
                &params,
                &pk,
                2,
                3,
                None,
                None,
                &mut [&mut *l0, &mut *l1, &mut *l2],
                &mu_a
            ),
            Ok(0)
        );

        // A certified signature by {P0, P1} leaves P2's latch behind.
        let mut cluster = QuorumEpochLatchCluster::new(3, 1).unwrap();
        let auth = cluster.authority();
        cluster
            .certify_epoch(&[0, 1, 2], 0, bind(0, &mu_a))
            .unwrap();
        let cert1 = cluster
            .certify_epoch(&[0, 1, 2], 1, bind(1, &mu_a))
            .unwrap();
        // Without a pinned authority, a certificate is rejected even if structurally valid.
        assert_eq!(
            reserve_authorised_epoch(
                &params,
                &pk,
                2,
                3,
                None,
                Some(&cert1),
                &mut [&mut *l0, &mut *l1],
                &mu_a
            ),
            Err(Poseidon2MpcError::LatchCertificateRejected(
                QuorumLatchError::CertificateCommitteeMismatch
            ))
        );
        assert_eq!(
            reserve_authorised_epoch(
                &params,
                &pk,
                2,
                3,
                Some(&auth),
                Some(&cert1),
                &mut [&mut *l0, &mut *l1],
                &mu_a
            ),
            Ok(1)
        );
        assert_eq!(
            (l0.next_epoch(), l1.next_epoch(), l2.next_epoch()),
            (2, 2, 1)
        );

        // Full attendance with the lagging latch and no certificate: refused, nothing advanced.
        assert_eq!(
            reserve_authorised_epoch(
                &params,
                &pk,
                2,
                3,
                Some(&auth),
                None,
                &mut [&mut *l0, &mut *l1, &mut *l2],
                &mu_b
            ),
            Err(Poseidon2MpcError::EpochLatch(
                EpochLatchError::LatchesDisagree
            ))
        );
        assert_eq!(
            (l0.next_epoch(), l1.next_epoch(), l2.next_epoch()),
            (2, 2, 1)
        );
        assert_eq!(l0.in_flight(), Some((1, mu_a)));

        // A certificate minted by a distinct rogue cluster is rejected by the pinned authority.
        let mut rogue = QuorumEpochLatchCluster::new(3, 1).unwrap();
        let rogue_cert = rogue.certify_epoch(&[0, 1, 2], 1, bind(1, &mu_b)).unwrap();
        assert_eq!(
            reserve_authorised_epoch(
                &params,
                &pk,
                2,
                3,
                Some(&auth),
                Some(&rogue_cert),
                &mut [&mut *l2, &mut *l1],
                &mu_b
            ),
            Err(Poseidon2MpcError::LatchCertificateRejected(
                QuorumLatchError::CertificateCommitteeMismatch
            ))
        );

        // Even under a harness-simulated split authority sharing the same MAC keys, the epoch
        // P0 and P1 already hold for `mu_a` cannot be taken for `mu_b`, and two-phase latch
        // checking leaves `l2` untouched.
        let mut shared_second = cluster.new_with_shared_test_authority();
        let shared_cert = shared_second
            .certify_epoch(&[0, 1, 2], 1, bind(1, &mu_b))
            .unwrap();
        assert_eq!(
            reserve_authorised_epoch(
                &params,
                &pk,
                2,
                3,
                Some(&auth),
                Some(&shared_cert),
                &mut [&mut *l2, &mut *l1],
                &mu_b
            ),
            Err(Poseidon2MpcError::EpochLatch(
                EpochLatchError::EquivocationRefused
            ))
        );
        // P2 was checked first and would have accepted; it must not have moved.
        assert_eq!(l2.next_epoch(), 1);
        assert_eq!(l2.in_flight(), Some((0, mu_a)));

        // The certified next epoch resynchronises the lagging latch: P2 skips epoch 1, which it
        // never used, and all three hold epoch 2.
        assert_eq!(cluster.next_unreserved_epoch(), Some(2));
        let cert2 = cluster
            .certify_epoch(&[0, 1, 2], 2, bind(2, &mu_b))
            .unwrap();
        assert_eq!(
            reserve_authorised_epoch(
                &params,
                &pk,
                2,
                3,
                Some(&auth),
                Some(&cert2),
                &mut [&mut *l1, &mut *l2],
                &mu_b
            ),
            Ok(2)
        );
        assert_eq!((l1.next_epoch(), l2.next_epoch()), (3, 3));
        // Presenting the same certificate again changes nothing.
        assert_eq!(
            reserve_authorised_epoch(
                &params,
                &pk,
                2,
                3,
                Some(&auth),
                Some(&cert2),
                &mut [&mut *l1, &mut *l2],
                &mu_b
            ),
            Ok(2)
        );
        assert_eq!((l1.next_epoch(), l2.next_epoch()), (3, 3));

        // An old certificate cannot move a latch backwards.
        assert_eq!(
            reserve_authorised_epoch(
                &params,
                &pk,
                2,
                3,
                Some(&auth),
                Some(&cert1),
                &mut [&mut *l0, &mut *l1],
                &mu_a
            ),
            Err(Poseidon2MpcError::EpochLatch(EpochLatchError::StaleEpoch))
        );
        assert_eq!(l0.in_flight(), Some((1, mu_a)));

        // Epochs beyond the key's capacity are refused before any latch moves.
        let cert8 = cluster
            .certify_epoch(&[0, 1, 2], 8, bind(8, &mu_b))
            .unwrap();
        assert_eq!(
            reserve_authorised_epoch(
                &params,
                &pk,
                2,
                3,
                Some(&auth),
                Some(&cert8),
                &mut [&mut *l0, &mut *l2],
                &mu_b
            ),
            Err(Poseidon2MpcError::EpochLatch(EpochLatchError::Exhausted))
        );
        assert_eq!((l0.next_epoch(), l2.next_epoch()), (2, 3));
    }

    /// Split-view regression for `(t, n) = (2, 3)`.
    ///
    /// `{P0, P1}` signs message A at epoch 0. P2 took no part, so its latch still says 0. A
    /// corrupt P1 (its latch rolled back) then asks P2 to sign message B: their two local latches
    /// agree on epoch 0, which P0 has already used. Every route to that second signature is
    /// refused before a latch moves or a share is touched.
    ///
    /// No preprocessing is provisioned (one signature's worth takes hours to generate), so the
    /// first signature is represented by its latch step, the reservation `{P0, P1}` make against
    /// the certificate, and any attempt that got past the gate into MPC would exhaust the vaults
    /// and poison every share.
    #[test]
    fn test_stateful_jorts_poseidon2_mpc_split_view_refused_without_committee_latch() {
        let params = PqHashParams {
            w: 4,
            ell1: 128,
            max_sigs_log2: 1,
            num_layers: 1,
            subtree_height: 1,
            fors_trees: 0,
            fors_height: 0,
            stateful: true,
        };
        assert!(params.is_well_formed());
        let (t, n) = (2usize, 3usize);
        let (mut key_shares, mut vaults, mut rngs, ref_sk) =
            setup_poseidon2_committee(t, n, (0, 0, 0));
        assert!(key_shares.iter().all(|ks| ks.committee_size == n));
        let pk = derive_public_key(Poseidon2Suite, &params, &ref_sk);
        let cache = DkgCachedSubtrees {
            top_layer: 0,
            top_leaves: (0..2u32)
                .map(|kp| compute_wots_pk(Poseidon2Suite, &params, &ref_sk, 0, 0, kp))
                .collect(),
            pk,
        };
        let [k0, k1, k2] = key_shares.as_mut_slice() else {
            panic!("three key shares");
        };
        let [v0, v1, v2] = vaults.as_mut_slice() else {
            panic!("three vaults");
        };

        let msg_a = b"message A";
        let msg_b = b"message B";
        let mu_a = th_pre_hash(Poseidon2Suite, &pk.pk_seed, &pk.pk_root, msg_a);
        let mu_b = th_pre_hash(Poseidon2Suite, &pk.pk_seed, &pk.pk_root, msg_b);
        let bind =
            |epoch: u64, mu: &[u8; 32]| epoch_latch_binding(&pk.pk_seed, &pk.pk_root, epoch, mu);

        // The latch quorum of a (2, 3) committee with one corruption is all three members.
        let mut cluster = QuorumEpochLatchCluster::new(n, t - 1).unwrap();
        let cluster_auth = cluster.authority();
        assert_eq!(cluster.latch_quorum(), 3);
        for ks in [&mut *k0, &mut *k1, &mut *k2] {
            ks.enroll_key_profile(params, pk).unwrap();
            ks.enroll_latch_authority(cluster_auth.clone()).unwrap();
        }
        let (mut l0, mut l1, mut l2) = (
            MonotonicEpochLatch::new(0),
            MonotonicEpochLatch::new(0),
            MonotonicEpochLatch::new(0),
        );

        // 1. {P0, P1} without a certificate: refused, although both latches agree on epoch 0.
        let uncertified = sign_jorts_poseidon2_mpc_cached(
            [0x70; 32],
            &params,
            &pk,
            Some(&cache),
            t,
            None,
            &mut [&mut l0, &mut l1],
            msg_a,
            100_000,
            &mut [&mut *k0, &mut *k1],
            &mut [&mut *v0, &mut *v1],
            &mut rngs[0..2],
        );
        assert_eq!(
            uncertified,
            Err(Poseidon2MpcError::LatchCertificateRequired {
                signers: 2,
                committee: 3
            })
        );
        assert_eq!(l0, MonotonicEpochLatch::new(0));
        assert_eq!(l1, MonotonicEpochLatch::new(0));
        assert!(!k0.poisoned && !k1.poisoned);

        // 2. Two acknowledgements are not a latch quorum; three are.
        assert!(cluster.certify_epoch(&[0, 1], 0, bind(0, &mu_a)).is_err());
        let cert_a = cluster
            .certify_epoch(&[0, 1, 2], 0, bind(0, &mu_a))
            .unwrap();
        assert_eq!(cert_a.acknowledging_parties(), &[0, 1, 2]);

        // 3. {P0, P1} reserve epoch 0 for A against the certificate, as their signature does.
        assert_eq!(
            reserve_authorised_epoch(
                &params,
                &pk,
                t,
                n,
                Some(&cluster_auth),
                Some(&cert_a),
                &mut [&mut l0, &mut l1],
                &mu_a
            ),
            Ok(0)
        );
        assert_eq!(l0.in_flight(), Some((0, mu_a)));
        assert_eq!(l1.in_flight(), Some((0, mu_a)));
        assert_eq!(l2, MonotonicEpochLatch::new(0));

        // 4. The split view. P1 presents a rolled-back latch; P2's is honestly at 0.
        let mut l1_rolled_back = MonotonicEpochLatch::new(0);

        // The committee will not certify B at epoch 0, whoever asks.
        assert_eq!(
            cluster.certify_epoch(&[0, 1, 2], 0, bind(0, &mu_b)),
            Err(QuorumLatchError::EquivocationRefused { epoch: 0 })
        );
        assert!(cluster.certify_epoch(&[1, 2], 0, bind(0, &mu_b)).is_err());

        // A second cluster stands in for certificates the committee never issued for this key,
        // including an attacker-minted certificate with the EXACT `(n, t, epoch, bind(0, &mu_b))`.
        let mut rogue_same_epoch = QuorumEpochLatchCluster::new(n, t - 1).unwrap();
        let rogue_exact = rogue_same_epoch
            .certify_epoch(&[0, 1, 2], 0, bind(0, &mu_b))
            .unwrap();
        let mut other = QuorumEpochLatchCluster::new(n, t - 1).unwrap();
        let foreign_key = other
            .certify_epoch(
                &[0, 1, 2],
                0,
                epoch_latch_binding(&[0x5a; 32], &pk.pk_root, 0, &mu_b),
            )
            .unwrap();
        let other_epoch = other.certify_epoch(&[0, 1, 2], 1, bind(1, &mu_b)).unwrap();
        // Bound to epoch 0 but reserved at epoch 2: the signer recomputes the binding per epoch.
        let rebound_epoch = other.certify_epoch(&[0, 1, 2], 2, bind(0, &mu_b)).unwrap();
        let mut two_member = QuorumEpochLatchCluster::new(2, t - 1).unwrap();
        let other_committee = two_member
            .certify_epoch(&[0, 1], 0, bind(0, &mu_b))
            .unwrap();

        let attempts: [(Option<&EpochLatchCertificate>, Poseidon2MpcError); 5] = [
            (
                None,
                Poseidon2MpcError::LatchCertificateRequired {
                    signers: 2,
                    committee: 3,
                },
            ),
            // Exact `(n=3, t=2, epoch=0, bind(0, &mu_b))` from an attacker-controlled cluster
            // MUST be rejected because its custodian MAC keys do not match `cluster_auth`!
            (
                Some(&rogue_exact),
                Poseidon2MpcError::LatchCertificateRejected(
                    QuorumLatchError::CertificateCommitteeMismatch,
                ),
            ),
            // The certificate issued for message A does not authorise message B.
            (
                Some(&cert_a),
                Poseidon2MpcError::LatchCertificateRejected(
                    QuorumLatchError::CertificateBindingMismatch { epoch: 0 },
                ),
            ),
            (
                Some(&foreign_key),
                Poseidon2MpcError::LatchCertificateRejected(
                    QuorumLatchError::CertificateBindingMismatch { epoch: 0 },
                ),
            ),
            (
                Some(&other_committee),
                Poseidon2MpcError::LatchCertificateRejected(
                    QuorumLatchError::CertificateCommitteeMismatch,
                ),
            ),
        ];
        for (latch_cert, expected) in attempts {
            let second = sign_jorts_poseidon2_mpc_cached(
                [0x72; 32],
                &params,
                &pk,
                Some(&cache),
                t,
                latch_cert,
                &mut [&mut l1_rolled_back, &mut l2],
                msg_b,
                100_000,
                &mut [&mut *k1, &mut *k2],
                &mut [&mut *v1, &mut *v2],
                &mut rngs[1..3],
            );
            assert_eq!(second, Err(expected.clone()));
            // The same holds for the retry entry point, which reserves nothing itself.
            let retry = retry_jorts_poseidon2_mpc_cached(
                [0x73; 32],
                &params,
                &pk,
                Some(&cache),
                t,
                latch_cert,
                &mut [&mut l1_rolled_back, &mut l2],
                0,
                msg_b,
                100_000,
                &mut [&mut *k1, &mut *k2],
                &mut [&mut *v1, &mut *v2],
                &mut rngs[1..3],
            );
            assert_eq!(retry, Err(expected));
        }
        let rebound = sign_jorts_poseidon2_mpc_cached(
            [0x74; 32],
            &params,
            &pk,
            Some(&cache),
            t,
            Some(&rebound_epoch),
            &mut [&mut l1_rolled_back, &mut l2],
            msg_b,
            100_000,
            &mut [&mut *k1, &mut *k2],
            &mut [&mut *v1, &mut *v2],
            &mut rngs[1..3],
        );
        assert_eq!(
            rebound,
            Err(Poseidon2MpcError::LatchCertificateRejected(
                QuorumLatchError::CertificateBindingMismatch { epoch: 2 }
            ))
        );
        // A certificate for epoch 1 does not cover a retry of epoch 0.
        let wrong_epoch_retry = retry_jorts_poseidon2_mpc_cached(
            [0x75; 32],
            &params,
            &pk,
            Some(&cache),
            t,
            Some(&other_epoch),
            &mut [&mut l1_rolled_back, &mut l2],
            0,
            msg_b,
            100_000,
            &mut [&mut *k1, &mut *k2],
            &mut [&mut *v1, &mut *v2],
            &mut rngs[1..3],
        );
        assert_eq!(
            wrong_epoch_retry,
            Err(Poseidon2MpcError::LatchCertificateRejected(
                QuorumLatchError::CertificateEpochMismatch {
                    certified_epoch: 1,
                    requested_epoch: 0
                }
            ))
        );

        // No refused attempt reserved an epoch or reached MPC.
        assert_eq!(l1_rolled_back, MonotonicEpochLatch::new(0));
        assert_eq!(l2, MonotonicEpochLatch::new(0));
        assert!(!k0.poisoned && !k1.poisoned && !k2.poisoned);
        assert!(!v0.is_poisoned() && !v1.is_poisoned() && !v2.is_poisoned());
    }

    /// The stateless signers' `R` is a function of the key and the message only. Two sessions
    /// with different session ids and different party randomness open the same `R`, equal to the
    /// single-holder reference. The public entry points take no randomiser argument (see the
    /// calls in `test_poseidon2_mpc_cached_top_subtree_rejects_mismatched_cache`).
    #[test]
    fn test_stateless_poseidon2_mpc_randomiser_is_deterministic_per_key_and_message() {
        let t = 2usize;
        let (mut key_shares, mut vaults, mut rngs, ref_sk) = setup_poseidon2_committee_material(
            2,
            2,
            (2 * 5 * POSEIDON2_SBOXES_PER_PERM, 0, 0),
            true,
        );
        let pts: Vec<Goldilocks> = key_shares.iter().map(|ks| ks.eval_point).collect();
        let [k0, k1] = key_shares.as_mut_slice() else {
            panic!("two key shares");
        };
        let [v0, v1] = vaults.as_mut_slice() else {
            panic!("two vaults");
        };
        let pk = PqPublicKey {
            pk_seed: ref_sk.pk_seed,
            pk_root: [0x3c; 32],
        };
        let mu = th_pre_hash(Poseidon2Suite, &pk.pk_seed, &pk.pk_root, b"same message");
        let mu_other = th_pre_hash(Poseidon2Suite, &pk.pk_seed, &pk.pk_root, b"other message");

        let r_first = eval_stateless_r_rand_mpc(
            &[0x81; 32],
            t,
            &pts,
            &pk,
            &mu,
            &mut [&mut *k0, &mut *k1],
            &mut [&mut *v0, &mut *v1],
            &mut rngs,
        )
        .unwrap();
        // A second session: new session id, and party randomness unrelated to the first run's.
        let mut other_rngs = make_rngs(2, 0x90);
        let r_second = eval_stateless_r_rand_mpc(
            &[0x82; 32],
            t,
            &pts,
            &pk,
            &mu,
            &mut [&mut *k0, &mut *k1],
            &mut [&mut *v0, &mut *v1],
            &mut other_rngs,
        )
        .unwrap();
        assert_eq!(r_first, r_second);
        assert_eq!(
            r_first,
            derive_stateless_r_rand(Poseidon2Suite, &ref_sk.sk_prf, &pk.pk_seed, &mu)
        );

        assert_ne!(
            r_first,
            derive_stateless_r_rand(Poseidon2Suite, &ref_sk.sk_prf, &pk.pk_seed, &mu_other)
        );
        assert!(!k0.poisoned && !k1.poisoned);
    }

    #[test]
    fn test_stateful_jorts_poseidon2_mpc_exact_parity_latch_and_dishonest_majority_abort() {
        // Compact stateful `JortsPoseidon2` parameter set (`w = 4, ell1 = 128, target_sum = 192, h = 2, d = 2`)
        let params = PqHashParams {
            w: 4,
            ell1: 128,
            max_sigs_log2: 2,
            num_layers: 2,
            subtree_height: 1,
            fors_trees: 0,
            fors_height: 0,
            stateful: true,
        };
        assert!(params.is_well_formed());
        let t = 2usize;

        let (kg_pow7, kg_beaver, kg_a2b) = required_poseidon2_keygen_preprocessing_budget(&params);
        let (sg_pow7, sg_beaver, sg_a2b) = required_poseidon2_sign_preprocessing_budget(&params);

        // 1. Run real dealerless Goldilocks DKG for `SK.seed` and `SK.prf`
        let (mut key_shares, mut vaults, mut rngs, ref_sk) = setup_poseidon2_committee_material(
            2,
            2,
            (
                kg_pow7 + 2 * sg_pow7,
                kg_beaver + 2 * sg_beaver,
                kg_a2b + 2 * sg_a2b,
            ),
            true,
        );
        let ref_pk = derive_public_key(Poseidon2Suite, &params, &ref_sk);

        // 2. Build distributed public key in MPC and assert bit-for-bit equality with `derive_public_key`
        let (ks0, ks1) = key_shares.split_at_mut(1);
        let (v0, v1) = vaults.split_at_mut(1);
        let mut ks_refs = [&mut ks0[0], &mut ks1[0]];
        let mut v_refs = [&mut v0[0], &mut v1[0]];

        let mpc_pk = build_distributed_poseidon2_key(
            [0x64; 32],
            &params,
            t,
            &mut ks_refs,
            &mut v_refs,
            &mut rngs,
        )
        .unwrap();
        assert_eq!(mpc_pk, ref_pk);

        // 3. Sign message at epoch 0 via SPDZ MPC and assert bit-for-bit parity with `eval_single_sign_stateful`!
        let msg = b"JortsPoseidon2 threshold signature parity vector";
        let mut l0 = MonotonicEpochLatch::new(0);
        let mut l1 = MonotonicEpochLatch::new(0);
        let mut latch_refs = [&mut l0, &mut l1];

        let (ep, mpc_sig) = sign_jorts_poseidon2_mpc(
            [0x65; 32],
            &params,
            &mpc_pk,
            t,
            None,
            &mut latch_refs,
            msg,
            100_000,
            &mut ks_refs,
            &mut v_refs,
            &mut rngs,
        )
        .unwrap();
        assert_eq!(ep, 0);

        let mut ref_latch = MonotonicEpochLatch::new(0);
        let ref_sig = eval_single_sign_stateful(
            Poseidon2Suite,
            &params,
            &ref_sk,
            &ref_pk,
            &mut ref_latch,
            msg,
            100_000,
        )
        .unwrap();
        assert_eq!(mpc_sig, ref_sig);
        assert!(verify_pq_hash_sig(
            Poseidon2Suite,
            &params,
            &mpc_pk,
            msg,
            &mpc_sig
        ));

        // 4. Crash-retry on `(epoch = 0, same msg)` succeeds with bit-identical signature, while
        //    equivocating `(epoch = 0, different msg)` is strictly refused BEFORE any MPC wire opens!
        let mut latch_refs = [&mut l0, &mut l1];
        let eq_err = retry_jorts_poseidon2_mpc(
            [0x66; 32],
            &params,
            &mpc_pk,
            t,
            None,
            &mut latch_refs,
            0,
            b"equivocated second message at epoch 0",
            100_000,
            &mut ks_refs,
            &mut v_refs,
            &mut rngs,
        )
        .unwrap_err();
        assert_eq!(
            eq_err,
            Poseidon2MpcError::EpochLatch(EpochLatchError::EquivocationRefused)
        );

        let retry_sig = retry_jorts_poseidon2_mpc(
            [0x67; 32],
            &params,
            &mpc_pk,
            t,
            None,
            &mut latch_refs,
            0,
            msg,
            100_000,
            &mut ks_refs,
            &mut v_refs,
            &mut rngs,
        )
        .unwrap();
        let ref_retry = retry_single_sign_stateful(
            Poseidon2Suite,
            &params,
            &ref_sk,
            &ref_pk,
            &mut ref_latch,
            0,
            msg,
            100_000,
        )
        .unwrap();
        assert_eq!(retry_sig, mpc_sig);
        assert_eq!(retry_sig, ref_retry);

        // 5. Active dishonest-majority Byzantine fault: corrupt party `1`'s `sk_prf_bytes[0]` share;
        //    pre-cut SPDZ `MacCheck` MUST abort AND permanently poison both `key_shares` and `vaults`!
        ks_refs[1].sk_prf_bytes[0] += Goldilocks::ONE;
        let abort_err = sign_jorts_poseidon2_mpc(
            [0x68; 32],
            &params,
            &mpc_pk,
            t,
            None,
            &mut latch_refs,
            b"epoch 1 message under active fault",
            100_000,
            &mut ks_refs,
            &mut v_refs,
            &mut rngs,
        )
        .unwrap_err();
        assert!(matches!(
            abort_err,
            Poseidon2MpcError::Preprocess(PreprocessError::MacCheckFailed { .. })
        ));
        assert!(ks_refs[0].poisoned && ks_refs[1].poisoned);
        assert!(v_refs[0].is_poisoned() && v_refs[1].is_poisoned());

        let _ = poseidon2_hash32(b"keep import exercised");
    }

    #[test]
    fn multilayer_corduroy_poseidon2_mpc_end_to_end() {
        let params = PqHashParams {
            w: 4,
            ell1: 128,
            max_sigs_log2: 2,
            num_layers: 2,
            subtree_height: 1,
            fors_trees: 1,
            fors_height: 1,
            stateful: false,
        };
        assert!(params.is_well_formed());
        let kg = required_poseidon2_keygen_preprocessing_budget(&params);
        let sg = required_poseidon2_sign_preprocessing_budget(&params);
        // Real DKG, authentication, and online MPC; offline correlations are a test fixture.
        let (mut keys, mut vaults, mut rngs, sk) =
            setup_poseidon2_committee_material(2, 2, (kg.0 + sg.0, kg.1 + sg.1, kg.2 + sg.2), true);
        let (ka, kb) = keys.split_at_mut(1);
        let (va, vb) = vaults.split_at_mut(1);
        let mut keys = [&mut ka[0], &mut kb[0]];
        let mut vaults = [&mut va[0], &mut vb[0]];
        let pk = build_distributed_poseidon2_key(
            [0xa1; 32],
            &params,
            2,
            &mut keys,
            &mut vaults,
            &mut rngs,
        )
        .unwrap();
        assert_eq!(pk, derive_public_key(Poseidon2Suite, &params, &sk));
        let message = b"Corduroy two-layer online MPC";
        let sig = sign_stateless_tsw_poseidon2_mpc(
            [0xa2; 32],
            &params,
            &pk,
            2,
            message,
            100_000,
            &mut keys,
            &mut vaults,
            &mut rngs,
        )
        .unwrap();
        assert!(verify_pq_hash_sig(
            Poseidon2Suite,
            &params,
            &pk,
            message,
            &sig
        ));
        assert!(!verify_pq_hash_sig(
            Poseidon2Suite,
            &params,
            &pk,
            b"different",
            &sig
        ));
    }

    /// Slippage U5: sign -> policy circuit -> verify for a multi-layer `Corduroy` key.
    ///
    /// The policy barrier of `qsag-policy` releases an [`AuthorizedSignReleaseToken`] for one
    /// canonical intent envelope; the threshold signer signs exactly those bytes and the stock
    /// verifier accepts exactly those bytes. A refused intent yields no token, and a token does
    /// not cover any other payload, key, context or quorum.
    #[test]
    fn multilayer_corduroy_policy_gated_sign_and_verify_end_to_end() {
        use crate::corduroy::Corduroy;
        use crate::sponge::keccak::cshake256_32;
        use qsag_accel::CpuReferenceBackend;
        use qsag_addr::{KeyIdentityKind, QsagAddress, WitnessSuiteTag};
        use qsag_policy::{
            AuthorizedSignReleaseToken, PolicyViolation, QuorumTierRule, SigningPayloadBinding,
            TransactionIntent, TransactionPolicy, evaluate_policy_committed_barrier_authenticated,
            trusted_dealer_setup_for_testing,
        };

        // Two-layer stateless hypertree, 2-of-2 signing committee (guard ids 1 and 2).
        let params = PqHashParams {
            w: 4,
            ell1: 128,
            max_sigs_log2: 2,
            num_layers: 2,
            subtree_height: 1,
            fors_trees: 1,
            fors_height: 1,
            stateful: false,
        };
        assert!(params.is_well_formed() && params.num_layers > 1);
        let kg = required_poseidon2_keygen_preprocessing_budget(&params);
        let sg = required_poseidon2_sign_preprocessing_budget(&params);
        let (mut keys, mut vaults, mut rngs, sk) =
            setup_poseidon2_committee_material(2, 2, (kg.0 + sg.0, kg.1 + sg.1, kg.2 + sg.2), true);
        let (ka, kb) = keys.split_at_mut(1);
        let (va, vb) = vaults.split_at_mut(1);
        let mut keys = [&mut ka[0], &mut kb[0]];
        let mut vaults = [&mut va[0], &mut vb[0]];
        let pk = build_distributed_poseidon2_key(
            [0xb1; 32],
            &params,
            2,
            &mut keys,
            &mut vaults,
            &mut rngs,
        )
        .unwrap();
        assert_eq!(pk, derive_public_key(Poseidon2Suite, &params, &sk));
        let key_id = cshake256_32(
            b"QSAG.TEST.CORDUROY.KEY_ID",
            &[pk.pk_seed, pk.pk_root].concat(),
        );

        // Policy: one allowlisted recipient, a single-transaction cap, two approvers including
        // the hardware guardian (guard 2, whose presence in every quorum carries the velocity
        // window), and an initiator (guard 3) who may not approve their own request.
        let accel = CpuReferenceBackend::new();
        let recipient = QsagAddress::from_pubkey_cshake256(
            "qsp",
            WitnessSuiteTag::SlhDsa128f,
            KeyIdentityKind::SingleOrThreshold,
            b"corduroy-cold-vault",
        )
        .unwrap();
        let policy = TransactionPolicy {
            chain_id: 7,
            pinned_suite: WitnessSuiteTag::SlhDsa128f,
            recipient_allowlist: vec![recipient.commitment_256],
            max_single_tx_amount: 1_000,
            velocity_window_cap: 5_000,
            valid_not_before_secs: 100,
            valid_not_after_secs: 10_000,
            forbid_initiator_self_approval: true,
            hardware_guardian_party: Some(2),
            quorum_tiers: vec![QuorumTierRule {
                max_amount_units: 1_000,
                min_approvers: 2,
                require_hardware_guardian: true,
            }],
        };
        let policy_digest = policy.canonical_digest();
        let authority_pk = [0x5a; 32];
        let quorum = [1u16, 2];
        let ctx = b"corduroy:treasury:v1";
        let mut guards: Vec<_> = trusted_dealer_setup_for_testing([0x91; 32], &[1, 2, 3])
            .into_iter()
            .map(|g| g.with_window_authority([0x42; 32], [0x43; 32]).unwrap())
            .collect();
        let initiator = guards.pop().unwrap();

        let request =
            |amount: u128, session: u8| -> Result<(TransactionIntent, Vec<u8>), PolicyViolation> {
                let (mut intent, _) = TransactionIntent::builder(
                    7,
                    WitnessSuiteTag::SlhDsa128f,
                    recipient.clone(),
                    amount,
                )
                .timestamp_secs(500)
                .initiator_and_approvers(3, &quorum)
                .bind_signing_payload(
                    &SigningPayloadBinding {
                        key_id,
                        payload: b"transfer to cold vault",
                        ctx,
                        session_id: [session; 32],
                        policy_revision: 1,
                        quorum: &quorum,
                        authority_pk,
                    },
                    &policy,
                )?;
                let bytes = initiator.authenticate_initiated_intent(&policy, &mut intent)?;
                Ok((intent, bytes))
            };
        let covers = |token: &AuthorizedSignReleaseToken,
                      key: &[u8; 32],
                      msg: &[u8],
                      ctx: &[u8],
                      quorum: &[u16]| {
            token.matches_signing_for_policy(key, msg, ctx, quorum, &policy_digest, &authority_pk)
        };

        // A request over the cap is refused before any guard is asked: nothing to sign.
        assert!(request(1_001, 0xc0).is_err());

        // The approved request: both guards run the committed barrier and release a token.
        let (intent, approved) = request(250, 0xc1).unwrap();
        let token = evaluate_policy_committed_barrier_authenticated(
            &policy,
            &intent,
            intent.session_id,
            intent.timestamp_secs,
            &mut guards,
            &accel,
        )
        .unwrap();
        assert!(covers(&token, &key_id, &approved, ctx, &quorum));

        // The token covers neither a different amount, key, context nor quorum.
        let mut inflated = intent.clone();
        inflated.amount_units = 251;
        let inflated_bytes = inflated.to_canonical_signing_bytes(&policy_digest);
        assert!(!covers(&token, &key_id, &inflated_bytes, ctx, &quorum));
        assert!(!covers(&token, &[0; 32], &approved, ctx, &quorum));
        assert!(!covers(&token, &key_id, &approved, b"other", &quorum));
        assert!(!covers(&token, &key_id, &approved, ctx, &[1, 3]));

        // An intent edited after the initiator authenticated it gets no token, and the same
        // approved intent cannot be replayed through the barrier for a second token.
        assert!(
            evaluate_policy_committed_barrier_authenticated(
                &policy,
                &inflated,
                inflated.session_id,
                inflated.timestamp_secs,
                &mut guards,
                &accel,
            )
            .is_err()
        );
        assert!(
            evaluate_policy_committed_barrier_authenticated(
                &policy,
                &intent,
                intent.session_id,
                intent.timestamp_secs,
                &mut guards,
                &accel,
            )
            .is_err()
        );

        // Sign exactly the released bytes under MPC; the stock verifier accepts only them.
        assert!(covers(&token, &key_id, &approved, ctx, &quorum));
        let sig = sign_stateless_tsw_poseidon2_mpc(
            *token.session_id(),
            &params,
            &pk,
            2,
            &approved,
            100_000,
            &mut keys,
            &mut vaults,
            &mut rngs,
        )
        .unwrap();
        assert!(Corduroy::verify(&params, &pk, &approved, &sig));
        assert!(!Corduroy::verify(&params, &pk, &inflated_bytes, &sig));
        assert!(!Corduroy::verify(
            &params,
            &pk,
            b"transfer to cold vault",
            &sig
        ));
    }

    #[test]
    fn test_uncached_signing_and_keygen_reject_unenrolled_or_forged_pk_and_params() {
        let stateful_params = PqHashParams {
            w: 4,
            ell1: 128,
            max_sigs_log2: 1,
            num_layers: 1,
            subtree_height: 1,
            fors_trees: 0,
            fors_height: 0,
            stateful: true,
        };
        let alt_stateful_params = PqHashParams {
            max_sigs_log2: 2,
            num_layers: 2,
            ..stateful_params
        };
        let stateless_params = PqHashParams {
            w: 4,
            ell1: 128,
            max_sigs_log2: 1,
            num_layers: 1,
            subtree_height: 1,
            fors_trees: 1,
            fors_height: 1,
            stateful: false,
        };
        assert!(
            stateful_params.is_well_formed()
                && alt_stateful_params.is_well_formed()
                && stateless_params.is_well_formed()
        );

        let kg = required_poseidon2_keygen_preprocessing_budget(&stateful_params);
        let (mut key_shares, mut vaults, mut rngs, ref_sk) =
            setup_poseidon2_committee_material(2, 2, kg, true);
        let ref_pk = derive_public_key(Poseidon2Suite, &stateful_params, &ref_sk);
        let (ks0, ks1) = key_shares.split_at_mut(1);
        let (v0, v1) = vaults.split_at_mut(1);
        let mut ks_refs = [&mut ks0[0], &mut ks1[0]];
        let mut v_refs = [&mut v0[0], &mut v1[0]];

        // 1. Unenrolled shares must refuse all uncached signing entry points before latching or spending.
        let mut l0 = MonotonicEpochLatch::new(0);
        let mut l1 = MonotonicEpochLatch::new(0);
        let before = remaining_budget(v_refs[0]);
        assert_eq!(
            sign_jorts_poseidon2_mpc(
                [0xb0; 32],
                &stateful_params,
                &ref_pk,
                2,
                None,
                &mut [&mut l0, &mut l1],
                b"unenrolled",
                100_000,
                &mut ks_refs,
                &mut v_refs,
                &mut rngs,
            ),
            Err(Poseidon2MpcError::KeyNotEnrolled)
        );
        assert_eq!(
            retry_jorts_poseidon2_mpc(
                [0xb1; 32],
                &stateful_params,
                &ref_pk,
                2,
                None,
                &mut [&mut l0, &mut l1],
                0,
                b"unenrolled",
                100_000,
                &mut ks_refs,
                &mut v_refs,
                &mut rngs,
            ),
            Err(Poseidon2MpcError::KeyNotEnrolled)
        );
        assert_eq!(
            sign_stateless_tsw_poseidon2_mpc(
                [0xb2; 32],
                &stateless_params,
                &ref_pk,
                2,
                b"unenrolled",
                100_000,
                &mut ks_refs,
                &mut v_refs,
                &mut rngs,
            ),
            Err(Poseidon2MpcError::KeyNotEnrolled)
        );
        assert_eq!(remaining_budget(v_refs[0]), before);
        assert_eq!((l0.next_epoch(), l1.next_epoch()), (0, 0));

        // 2. Enroll via `build_distributed_poseidon2_key` (`stateful_params`, `mpc_pk`).
        let mpc_pk = build_distributed_poseidon2_key(
            [0xb3; 32],
            &stateful_params,
            2,
            &mut ks_refs,
            &mut v_refs,
            &mut rngs,
        )
        .unwrap();
        assert_eq!(mpc_pk, ref_pk);
        assert_eq!(remaining_budget(v_refs[0]), (0, 0, 0));

        // 3. Re-running keygen under a different parameter profile is rejected before touching vaults.
        assert_eq!(
            build_distributed_poseidon2_key(
                [0xb4; 32],
                &alt_stateful_params,
                2,
                &mut ks_refs,
                &mut v_refs,
                &mut rngs,
            ),
            Err(Poseidon2MpcError::KeyProfileMismatch)
        );

        // 4. Uncached signing (`cache = None`) with forged `pk_root`, forged `pk_seed`, or mismatched
        //    `params` is rejected strictly before latch reservation or MPC execution (`0` tuples left,
        //    so reaching MPC would fail with `VaultExhausted` and poison the shares!).
        let mut forged_root_pk = mpc_pk;
        forged_root_pk.pk_root[0] ^= 0x80;
        let mut forged_seed_pk = mpc_pk;
        forged_seed_pk.pk_seed[0] ^= 0x01;

        for (bad_params, bad_pk, exp_err) in [
            (
                &stateful_params,
                &forged_root_pk,
                Poseidon2MpcError::KeyProfileMismatch,
            ),
            (
                &stateful_params,
                &forged_seed_pk,
                Poseidon2MpcError::PublicSeedMismatch,
            ),
            (
                &alt_stateful_params,
                &mpc_pk,
                Poseidon2MpcError::KeyProfileMismatch,
            ),
        ] {
            assert_eq!(
                sign_jorts_poseidon2_mpc(
                    [0xb5; 32],
                    bad_params,
                    bad_pk,
                    2,
                    None,
                    &mut [&mut l0, &mut l1],
                    b"forged profile",
                    100_000,
                    &mut ks_refs,
                    &mut v_refs,
                    &mut rngs,
                ),
                Err(exp_err.clone())
            );
            assert_eq!(
                retry_jorts_poseidon2_mpc(
                    [0xb6; 32],
                    bad_params,
                    bad_pk,
                    2,
                    None,
                    &mut [&mut l0, &mut l1],
                    0,
                    b"forged profile",
                    100_000,
                    &mut ks_refs,
                    &mut v_refs,
                    &mut rngs,
                ),
                Err(exp_err)
            );
        }
        assert_eq!(
            sign_stateless_tsw_poseidon2_mpc(
                [0xb7; 32],
                &stateless_params,
                &mpc_pk,
                2,
                b"wrong mode",
                100_000,
                &mut ks_refs,
                &mut v_refs,
                &mut rngs,
            ),
            Err(Poseidon2MpcError::KeyProfileMismatch)
        );
        assert_eq!((l0.next_epoch(), l1.next_epoch()), (0, 0));
        assert!(!ks_refs[0].poisoned && !ks_refs[1].poisoned);
        assert!(!v_refs[0].is_poisoned() && !v_refs[1].is_poisoned());
    }

    #[test]
    fn test_hem_jorts_native_spdz_sign_and_reshare_zero_a2b() {
        use crate::dkg::run_dealerless_reshare_seed32_goldilocks;

        let t = 2usize;
        let n = 3usize;
        let active_leaves = 1usize;
        let keygen_budget = required_hem_jorts_keygen_preprocessing_budget(active_leaves).unwrap();
        let sign_budget = required_hem_jorts_sign_preprocessing_budget_cached();
        assert_eq!(keygen_budget.1, 0);
        assert_eq!(keygen_budget.2, 0);
        assert_eq!(sign_budget, (38_232, 0, 0));

        let pts: Vec<Goldilocks> = (1..=n as u64).map(Goldilocks::from_u64_reduced).collect();
        let mut rngs = make_rngs(n, 0x91);
        let mut mesh = OtMesh::establish_ideal_for_test([0x92; 32], &mut rngs);

        let dkg_seed =
            run_dealerless_dkg_seed32_goldilocks([0x93; 32], t, &pts, &mut mesh, &mut rngs)
                .unwrap();
        let dkg_prf =
            run_dealerless_dkg_seed32_goldilocks([0x94; 32], t, &pts, &mut mesh, &mut rngs)
                .unwrap();
        let pk_seed = dkg_seed.1;

        let total_budget = (keygen_budget.0 + 2 * sign_budget.0, 0, 0);
        let (mut key_shares, mut vaults) = authenticate_poseidon_dkg_shares_and_preprocess(
            [0x95; 32],
            t,
            &pts,
            pk_seed,
            &dkg_seed.0,
            &dkg_prf.0,
            total_budget.0,
            total_budget.1,
            total_budget.2,
            &mut mesh,
            &mut rngs,
        )
        .unwrap();

        let ref_seed =
            shamir_reconstruct_seed32_goldilocks(&dkg_seed.0[..t].iter().collect::<Vec<_>>())
                .unwrap();
        let ref_prf =
            shamir_reconstruct_seed32_goldilocks(&dkg_prf.0[..t].iter().collect::<Vec<_>>())
                .unwrap();
        let clear_cache =
            derive_hem_jorts_cached_tree_clear(pk_seed, &ref_seed, &ref_prf, active_leaves)
                .unwrap();

        let cache = {
            let (ks0, ks_rest) = key_shares.split_at_mut(1);
            let (ks1, _) = ks_rest.split_at_mut(1);
            let (v0, v_rest) = vaults.split_at_mut(1);
            let (v1, _) = v_rest.split_at_mut(1);
            build_distributed_hem_jorts_key_mpc_with_active_leaves(
                [0x96; 32],
                active_leaves,
                t,
                &mut [&mut ks0[0], &mut ks1[0]],
                &mut [&mut v0[0], &mut v1[0]],
                &mut rngs[..t],
            )
            .unwrap()
        };
        assert_eq!(cache, clear_cache);
        assert!(cache.verify_consistency());
        key_shares[2]
            .enroll_hem_key_profile(cache.pk, cache.prf_check)
            .unwrap();

        let mut cluster = QuorumEpochLatchCluster::establish(n, t, 0, &mut rngs).unwrap();
        for ks in &mut key_shares {
            ks.enroll_latch_authority(cluster.authority_public().clone())
                .unwrap();
        }
        let latch_pk = cache.pk.latch_pq_public_key(cache.dkg_pk_seed);
        let msg0 = b"hem native poseidon2 epoch 0";
        let (mu0_bytes, _) = hem_compute_message_mu(&cache.pk, msg0);
        let cert0 = cluster
            .certify_epoch(
                &[0, 1, 2],
                &latch_pk,
                HEM_JORTS_XMSS_HEIGHT as u32,
                &mu0_bytes,
            )
            .unwrap();

        let (ep0, sig0) = {
            let (ks0, ks_rest) = key_shares.split_at_mut(1);
            let (ks1, _) = ks_rest.split_at_mut(1);
            let (v0, v_rest) = vaults.split_at_mut(1);
            let (v1, _) = v_rest.split_at_mut(1);
            let before = remaining_budget(v0.first().unwrap());
            let mut l0 = MonotonicEpochLatch::new(0);
            let mut l1 = MonotonicEpochLatch::new(0);
            let out = sign_hem_jorts_poseidon2_mpc_cached(
                [0x97; 32],
                &cache,
                t,
                Some(&cert0),
                &mut [&mut l0, &mut l1],
                msg0,
                100_000,
                &mut [&mut ks0[0], &mut ks1[0]],
                &mut [&mut v0[0], &mut v1[0]],
                &mut rngs[..t],
            )
            .unwrap();
            let after = remaining_budget(v0.first().unwrap());
            assert_eq!(spent(before, after), sign_budget);

            let retry_sig = retry_hem_jorts_poseidon2_mpc_cached(
                [0x98; 32],
                &cache,
                t,
                Some(&cert0),
                &mut [&mut l0, &mut l1],
                out.0,
                msg0,
                100_000,
                &mut [&mut ks0[0], &mut ks1[0]],
                &mut [&mut v0[0], &mut v1[0]],
                &mut rngs[..t],
            )
            .unwrap();
            assert_eq!(retry_sig, out.1);
            out
        };
        assert_eq!(ep0, 0);
        assert_eq!(sig0.to_bytes().len(), HEM_JORTS_SIG_BYTES);
        assert!(verify_hem_jorts_signature(&cache.pk, msg0, &sig0));
        assert_eq!(
            HemJortsSignature::from_bytes_canonical(&sig0.to_bytes()).as_ref(),
            Some(&sig0)
        );

        // Reshare (2, 3) -> (3, 4) and verify reshared shares in SPDZ MPC without reconstructing secrets!
        let new_t = 3usize;
        let new_n = 4usize;
        let new_pts: Vec<Goldilocks> = (1..=new_n as u64).map(Goldilocks::from_u64_reduced).collect();
        let mut old_seed = dkg_seed.0;
        let mut old_prf = dkg_prf.0;
        let mut old_rngs = make_rngs(t, 0xA1);
        let mut new_rngs = make_rngs(new_n, 0xA2);
        let mut new_mesh = OtMesh::establish_ideal_for_test([0xA3; 32], &mut new_rngs);

        let reshared_seed = run_dealerless_reshare_seed32_goldilocks(
            [0xA4; 32],
            t,
            &mut [&mut old_seed[0], &mut old_seed[1]],
            new_t,
            &new_pts,
            &mut new_mesh,
            &mut old_rngs,
            &mut new_rngs,
            |_, _| Ok(()),
        )
        .unwrap();
        let reshared_prf = run_dealerless_reshare_seed32_goldilocks(
            [0xA5; 32],
            t,
            &mut [&mut old_prf[0], &mut old_prf[1]],
            new_t,
            &new_pts,
            &mut new_mesh,
            &mut old_rngs,
            &mut new_rngs,
            |_, _| Ok(()),
        )
        .unwrap();

        let verify_budget = required_hem_jorts_reshare_verify_preprocessing_budget();
        let (mut new_ks, mut new_vaults) = authenticate_poseidon_dkg_shares_and_preprocess(
            [0xA6; 32],
            new_t,
            &new_pts,
            pk_seed,
            &reshared_seed,
            &reshared_prf,
            verify_budget.0,
            0,
            0,
            &mut new_mesh,
            &mut new_rngs,
        )
        .unwrap();
        {
            let mut ks_refs: Vec<&mut Poseidon2SpdzAuthenticatedKeyShare> =
                new_ks[..new_t].iter_mut().collect();
            let mut v_refs: Vec<&mut PreprocessedPoseidonPartyVault> =
                new_vaults[..new_t].iter_mut().collect();
            verify_reshared_hem_jorts_key_mpc(
                [0xA7; 32],
                &cache,
                new_t,
                &mut ks_refs,
                &mut v_refs,
                &mut new_rngs[..new_t],
            )
            .unwrap();
        }
    }
}
