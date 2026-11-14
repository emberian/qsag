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
    epoch_latch_binding, latch_quorum_intersects_honestly, EpochLatchCertificate,
    EpochLatchError as QuorumLatchError, ShamirPoseidonSeedShare,
};
use crate::field::goldilocks::{Goldilocks, GoldilocksExt2};
use crate::keccak_mpc::DkgCachedSubtrees;
use crate::preprocessing::{
    commit_and_open_spdz_goldilocks_batch_quorum, open_and_check_degree_goldilocks,
    run_dealerless_pi_pow7_with_alpha, spdz_authenticate_goldilocks_batch_ext2,
    spdz_setup_alpha_goldilocks, validate_all_eval_points_goldilocks, OtMesh, PartyPrivateRng,
    PreprocessError, PreprocessedPoseidonPartyVault,
};
use crate::sponge::keccak::{cshake256_32};
use crate::sponge::poseidon2::{
    bytes_to_limbs56, poseidon2_const_at, poseidon2_pad, POSEIDON2_HALF_EXTERNAL_ROUNDS,
    POSEIDON2_INIT_STATE, POSEIDON2_INTERNAL_ROUNDS,
};
use crate::tsw_baggy::{
    build_merkle_from_leaves_topdown, build_prf_msg_template, build_single_secret32_template,
    build_stateful_det_opt_domain, build_stateless_det_opt_domain,
    derive_stateless_leaf_and_fors_indices,
    grind_tsw_internal_counter, grind_tsw_leaf_counter, th_pre_hash, th_tweak_tl, verify_pq_hash_sig,
    AdrsKind, EpochLatchError, ForsTreeOpening, HashAdrs, LayerXmssSig, Poseidon2Suite, PqHashParams,
    PqHashSig, PqPublicKey, StatefulEpochLatch, TAG_PRF, TAG_TH_F,
};
use crate::wipe::{ct_eq_bytes32, wipe_bytes32, wipe_ext2, wipe_goldilocks};

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
    InvalidQuorum { t: usize, n: usize },
    KeySharePoisoned { party_id: usize },
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
    LatchCertificateRequired { signers: usize, committee: usize },
    /// The presented latch certificate does not authorise this `(committee, key, epoch, message)`.
    LatchCertificateRejected(QuorumLatchError),
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
            shares.reserve(wires.len());
            macs.reserve(wires.len());
            for w in wires {
                shares.push(w.val);
                macs.push(w.mac);
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
) -> Result<(Vec<Poseidon2SpdzAuthenticatedKeyShare>, Vec<PreprocessedPoseidonPartyVault>), Poseidon2MpcError>
{
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
    let mut flat_bytes_per_party = vec![vec![Goldilocks::ZERO; 64]; n];
    for p in 0..n {
        for byte_idx in 0..32 {
            let mut acc_seed = Goldilocks::ZERO;
            let mut acc_prf = Goldilocks::ZERO;
            let mut pow2 = Goldilocks::ONE;
            for bit in 0..8 {
                acc_seed += pow2 * sk_seed_dkg[p].bit_shares[8 * byte_idx + bit];
                acc_prf += pow2 * sk_prf_dkg[p].bit_shares[8 * byte_idx + bit];
                pow2 = pow2 + pow2;
            }
            flat_bytes_per_party[p][byte_idx] = acc_seed;
            flat_bytes_per_party[p][32 + byte_idx] = acc_prf;
        }
    }

    // 2. Establish unified dealerless `GoldilocksExt2` SPDZ MAC key `\alpha` across `0..n`
    let alpha_sid = cshake256_32(b"QSAG.POS2.UNIFIED.ALPHA/v1", &session_id);
    let (mut alpha_contribs, mut alpha_shamir) =
        spdz_setup_alpha_goldilocks(&alpha_sid, t, eval_points, party_rngs)?;

    // 3. Authenticate all 64 secret byte shares via LHL Gilboa OLE + SPDZ sacrifice (`0` central RAM!)
    let key_auth_sid = cshake256_32(b"QSAG.POS2.KEY.AUTH/v1", &session_id);
    let key_macs_res = spdz_authenticate_goldilocks_batch_ext2(
        &key_auth_sid,
        t,
        eval_points,
        ot_mesh,
        &alpha_contribs,
        &alpha_shamir,
        &flat_bytes_per_party,
        party_rngs,
    );
    let mut key_macs = match key_macs_res {
        Ok(m) => m,
        Err(e) => {
            for row in &mut flat_bytes_per_party {
                wipe_goldilocks(row);
            }
            wipe_ext2(&mut alpha_contribs);
            wipe_ext2(&mut alpha_shamir);
            return Err(Poseidon2MpcError::Preprocess(e));
        }
    };

    // 4. Generate correlated `Π_pow7` + Beaver + Canonical `< p` A2B vaults under the SAME `\alpha`
    let vault_sid = cshake256_32(b"QSAG.POS2.VAULT.POW7/v1", &session_id);
    let vaults_res = run_dealerless_pi_pow7_with_alpha(
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
    );
    wipe_ext2(&mut alpha_contribs);

    let vaults = match vaults_res {
        Ok(v) => v,
        Err(e) => {
            for p in 0..n {
                wipe_goldilocks(&mut flat_bytes_per_party[p]);
                wipe_ext2(&mut key_macs[p]);
            }
            wipe_ext2(&mut alpha_shamir);
            return Err(Poseidon2MpcError::Preprocess(e));
        }
    };

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
        wipe_goldilocks(&mut flat_bytes_per_party[p]);
        wipe_ext2(&mut key_macs[p]);
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
            poisoned: false,
        });
    }
    wipe_ext2(&mut alpha_shamir);

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
    let mut masked_wires = vec![Vec::with_capacity(count); m];
    for p in 0..m {
        let mut p_tups = Vec::with_capacity(count);
        for input in &inputs_per_party[p][..count] {
            let tup = vaults[p].pop_pow7()?;
            let r_wire = AuthGlWire {
                val: tup.r_pows[0],
                mac: tup.r_macs[0],
            };
            masked_wires[p].push(input.add(r_wire));
            p_tups.push(crate::preprocessing::AuthenticatedPower7Share { r_pows: tup.r_pows, r_macs: tup.r_macs, r1_mac: tup.r1_mac });
        }
        tuples_p.push(p_tups);
    }

    pending.record_batch(&masked_wires);

    let mut y_opened = Vec::with_capacity(count);
    let mut sh_buf = vec![Goldilocks::ZERO; m];
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
    wipe_goldilocks(&mut sh_buf);

    let c7 = Goldilocks::from_u64_reduced(7);
    let c21 = Goldilocks::from_u64_reduced(21);
    let c35 = Goldilocks::from_u64_reduced(35);

    let mut out = vec![Vec::with_capacity(count); m];
    for p in 0..m {
        let alpha_p = vaults[p].mac_alpha_share;
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
    Ok(out)
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
        let mut sbox_in = vec![Vec::with_capacity(batch * 12); m];
        for p in 0..m {
            let alpha_p = vaults[p].mac_alpha_share;
            for st in &states_per_party[p][..batch] {
                for (lane, wire) in st.iter().enumerate() {
                    let rc = AuthGlWire::public_const(poseidon2_const_at(0, r, lane as u64), alpha_p);
                    sbox_in[p].push(wire.add(rc));
                }
            }
        }
        let sbox_out = eval_sbox7_batch_spdz(t, quorum_pts, &sbox_in, vaults, pending)?;
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
        let mut sbox_in = vec![Vec::with_capacity(batch); m];
        for p in 0..m {
            let alpha_p = vaults[p].mac_alpha_share;
            let rc0 = AuthGlWire::public_const(poseidon2_const_at(1, r, 0), alpha_p);
            for st in &states_per_party[p][..batch] {
                sbox_in[p].push(st[0].add(rc0));
            }
        }
        let sbox_out = eval_sbox7_batch_spdz(t, quorum_pts, &sbox_in, vaults, pending)?;
        for p in 0..m {
            for b in 0..batch {
                states_per_party[p][b][0] = sbox_out[p][b];
                apply_mi_auth(&mut states_per_party[p][b]);
            }
        }
    }

    // Final 4 external rounds (`tag = 2`)
    for r in 0..POSEIDON2_HALF_EXTERNAL_ROUNDS {
        let mut sbox_in = vec![Vec::with_capacity(batch * 12); m];
        for p in 0..m {
            let alpha_p = vaults[p].mac_alpha_share;
            for st in &states_per_party[p][..batch] {
                for (lane, wire) in st.iter().enumerate() {
                    let rc = AuthGlWire::public_const(poseidon2_const_at(2, r, lane as u64), alpha_p);
                    sbox_in[p].push(wire.add(rc));
                }
            }
        }
        let sbox_out = eval_sbox7_batch_spdz(t, quorum_pts, &sbox_in, vaults, pending)?;
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
    let mut item_limbs_p: Vec<Vec<Vec<AuthGlWire>>> = vec![Vec::with_capacity(batch); m];
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
    let mut states_p: Vec<Vec<[AuthGlWire; 12]>> = vec![Vec::with_capacity(batch); m];
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
        let mut sub_states = vec![Vec::with_capacity(active_indices.len()); m];
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

    let mut out = vec![Vec::with_capacity(batch); m];
    for p in 0..m {
        for st in &states_p[p][..batch] {
            out[p].push([st[0], st[1], st[2], st[3]]);
        }
    }
    Ok(out)
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
    let mut de_wires = vec![Vec::with_capacity(2 * count); m];
    for p in 0..m {
        let mut p_tr = Vec::with_capacity(count);
        for k in 0..count {
            let tr = vaults[p].pop_beaver()?;
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
            p_tr.push(crate::preprocessing::GoldilocksBeaverShare { a: tr.a, b: tr.b, c: tr.c, a_mac: tr.a_mac, b_mac: tr.b_mac, c_mac: tr.c_mac });
        }
        triples_p.push(p_tr);
    }

    pending.record_batch(&de_wires);

    let mut de_open = Vec::with_capacity(2 * count);
    let mut sh_buf = vec![Goldilocks::ZERO; m];
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
    wipe_goldilocks(&mut sh_buf);

    let mut out = vec![Vec::with_capacity(count); m];
    for p in 0..m {
        let alpha_p = vaults[p].mac_alpha_share;
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
            let z = c_w
                .add(b_w.scale(d))
                .add(a_w.scale(e))
                .add(de_const);
            out[p].push(z);
        }
    }
    Ok(out)
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
    let mut r_bits_p: Vec<Vec<[AuthGlWire; 64]>> = vec![Vec::with_capacity(num_lanes); m];
    let mut z_wires = vec![Vec::with_capacity(num_lanes); m];
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
    let mut sh_buf = vec![Goldilocks::ZERO; m];
    for idx in 0..num_lanes {
        for (buf, wires) in sh_buf.iter_mut().zip(z_wires.iter()) {
            *buf = wires[idx].val;
        }
        let z_f = open_and_check_degree_goldilocks(t, quorum_pts, &sh_buf, "pos2_a2b_z")?;
        z_pub.push(z_f.to_canonical_u64());
    }
    wipe_goldilocks(&mut sh_buf);

    // 2. Run dual 64-bit public+secret ripple adders in lockstep across all `num_lanes`:
    //    Adder A: `z + r` -> sum bits `u_bits[0..64]`
    //    Adder B: `(z + 2^32 - 1) + r` -> sum bits `v_bits[0..64]`, carry `c_b` (`c_b == 1 iff z + r >= p`)
    let mut u_bits_p = vec![vec![[AuthGlWire::ZERO; 64]; num_lanes]; m];
    let mut v_bits_p = vec![vec![[AuthGlWire::ZERO; 64]; num_lanes]; m];
    let mut carry_a_p = vec![vec![AuthGlWire::ZERO; num_lanes]; m];
    let mut carry_b_p = vec![vec![AuthGlWire::ZERO; num_lanes]; m];

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
        let mut mul_x = vec![Vec::with_capacity(2 * num_lanes); m];
        let mut mul_y = vec![Vec::with_capacity(2 * num_lanes); m];
        for p in 0..m {
            for idx in 0..num_lanes {
                let rk = r_bits_p[p][idx][bit];
                mul_x[p].push(rk);
                mul_y[p].push(carry_a_p[p][idx]);
                mul_x[p].push(rk);
                mul_y[p].push(carry_b_p[p][idx]);
            }
        }
        let prods = eval_spdz_beaver_mul_batch(t, quorum_pts, &mul_x, &mul_y, vaults, pending)?;
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
    let mut mux_x = vec![Vec::with_capacity(64 * num_lanes); m];
    let mut mux_y = vec![Vec::with_capacity(64 * num_lanes); m];
    for p in 0..m {
        for idx in 0..num_lanes {
            let cb = carry_b_p[p][idx];
            for bit in 0..64 {
                mux_x[p].push(cb);
                mux_y[p].push(v_bits_p[p][idx][bit].sub(u_bits_p[p][idx][bit]));
            }
        }
    }
    let mux_prods = eval_spdz_beaver_mul_batch(t, quorum_pts, &mux_x, &mux_y, vaults, pending)?;

    // 4. Pack canonical big-endian bytes `to_be_bytes()` (`byte 0` = bits `56..64`, ..., `byte 7` = bits `0..8`)
    let mut out_bytes_p = vec![Vec::with_capacity(batch); m];
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
    Ok(out_bytes_p)
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
    let alpha: Vec<_> = vaults.iter().map(|v| v.mac_alpha_share).collect();
    let intermediate = commit_and_open_spdz_goldilocks_batch_quorum(
        session_id, "pre_cut_intermediate_mac", t, quorum_pts,
        &pending.shares_per_party, &pending.macs_per_party, &alpha, party_rngs,
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

    let mut all_sh = vec![Vec::with_capacity(total_wires); m];
    let mut all_mac = vec![Vec::with_capacity(total_wires); m];
    let mut alpha_sh = Vec::with_capacity(m);
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
        session_id,
        phase,
        t,
        quorum_pts,
        &all_sh,
        &all_mac,
        &alpha_sh,
        party_rngs,
    );
    for p in 0..m {
        wipe_goldilocks(&mut all_sh[p]);
        wipe_ext2(&mut all_mac[p]);
    }
    wipe_ext2(&mut alpha_sh);

    let mut opened = match opened_res {
        Ok(v) => v,
        Err(e) => {
            poison_all_on_abort(key_shares, vaults);
            return Err(Poseidon2MpcError::Preprocess(e));
        }
    };

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
                wipe_goldilocks(&mut opened);
                poison_all_on_abort(key_shares, vaults);
                return Err(Poseidon2MpcError::Preprocess(
                    PreprocessError::NonBooleanBitDetected { phase },
                ));
            }
            b32[b] = v as u8;
        }
        out_extra.push(b32);
    }
    wipe_goldilocks(&mut opened);

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
    if m > n || key_shares.iter().any(|ks| ks.committee_size != n || ks.party_id >= n) {
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
    let mut prf_secrets = vec![Vec::with_capacity(count); m];
    for p in 0..m {
        let seed_w = key_seed_wires(key_shares[p]);
        for _ in 0..count {
            prf_secrets[p].push(seed_w);
        }
    }

    let mut cur_states = match eval_spdz_poseidon2_hash32_templates(
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
    };

    let max_steps = targets.iter().map(|x| x.4).max().unwrap_or(0);
    for step in 0..max_steps {
        let active: Vec<usize> = (0..count).filter(|&i| step < targets[i].4).collect();
        let mut active_st = vec![Vec::with_capacity(active.len()); m];
        for p in 0..m {
            for &i in &active {
                active_st[p].push(cur_states[p][i]);
            }
        }
        let active_bytes = match eval_spdz_canonical_a2b_state4_batch_to_bytes32(
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
        };

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

        let next_st = match eval_spdz_poseidon2_hash32_templates(
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
        };

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
        session_id,
        phase,
        t,
        quorum_pts,
        pk_seed,
        &targets,
        key_shares,
        vaults,
        party_rngs,
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

fn sign_preprocessing_budget(params: &PqHashParams, top_subtree_cached: bool) -> (usize, usize, usize) {
    let sub_leaves = 1usize << params.subtree_height;
    let steps_max = params.w.saturating_sub(1);
    let fors_leaves = if params.stateful {
        0
    } else {
        params.fors_trees * (1usize << params.fors_height)
    };
    // With a top-subtree leaf cache the top layer evaluates only its `ell1` signing chains.
    let mpc_subtrees = params.num_layers.saturating_sub(usize::from(top_subtree_cached));
    let hypertree_chains = params.num_layers * params.ell1 + mpc_subtrees * sub_leaves * params.ell1;
    let (prf_perms, step_perms) = chain_template_permutations();
    let opt_domain = if params.stateful {
        build_stateful_det_opt_domain(0, &[0; 32])
    } else {
        build_stateless_det_opt_domain(&[0; 32])
    };
    let randomizer_perms = template_permutations(&build_prf_msg_template(&opt_domain, &[0; 32]));
    let total_perms = randomizer_perms + fors_leaves * (prf_perms + step_perms)
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
    Ok(DkgCachedSubtrees {
        top_layer,
        top_leaves,
        pk: PqPublicKey { pk_seed, pk_root },
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
                prf_tmpls.push(build_single_secret32_template(TAG_PRF, &pk.pk_seed, &prf_adrs));
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
        let mut prf_secs = vec![Vec::with_capacity(total_fors); m];
        for p in 0..m {
            let sw = key_seed_wires(key_shares[p]);
            for _ in 0..total_fors {
                prf_secs[p].push(sw);
            }
        }
        let sec_states = match eval_spdz_poseidon2_hash32_templates(
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
        };

        // Convert ALL `total_fors` secret states to canonical byte shares via A2B so unrevealed
        // FORS leaves NEVER open `sec_states`, and open ONLY the `fors_trees` selected `secret_val`s
        // plus the `total_fors` public leaf hashes at the cut boundary!
        let sec_bytes = match eval_spdz_canonical_a2b_state4_batch_to_bytes32(
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
        };

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
        let mut cut_states = leaf_states;
        for p in 0..m {
            for (j, &idx_j) in idxs.iter().enumerate().take(params.fors_trees) {
                cut_states[p].push(sec_states[p][j * fors_leaf_count + idx_j]);
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
    let mut prf_secs = vec![Vec::with_capacity(1); m];
    for p in 0..m {
        prf_secs[p].push(key_prf_wires(key_shares[p]));
    }
    let st4 = match eval_spdz_poseidon2_hash32_templates(
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
    };
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

/// Committee-wide latch gate of the stateful signers.
///
/// A one-time leaf may open for one message only, whichever `t` members sign. Local latches
/// enforce that among the members present; two signing sets that overlap only in corrupt members
/// could still each reserve the same epoch for a different message. So local latches are accepted
/// on their own only at full attendance (`signers == n`, where the set is itself a latch quorum:
/// `2n > n + (t - 1)`), and any smaller signing set must present a certificate that a quorum `q`
/// with `2q > n + (t - 1)` reserved exactly this `(key, epoch, mu)`.
///
/// Reads public values only and changes nothing.
fn check_committee_latch_authorisation(
    pk: &PqPublicKey,
    t: usize,
    n: usize,
    signers: usize,
    latch_cert: Option<&EpochLatchCertificate>,
    epoch: u64,
    mu: &[u8; 32],
) -> Result<(), Poseidon2MpcError> {
    match latch_cert {
        Some(cert) => {
            let binding = epoch_latch_binding(&pk.pk_seed, &pk.pk_root, epoch, mu);
            cert.verify_for(n, t, epoch, &binding)
                .map_err(Poseidon2MpcError::LatchCertificateRejected)
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
fn reserve_authorised_epoch<L: StatefulEpochLatch>(
    params: &PqHashParams,
    pk: &PqPublicKey,
    t: usize,
    n: usize,
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
    check_committee_latch_authorisation(pk, t, n, latches.len(), latch_cert, epoch, mu)?;
    if latch_cert.is_none() && latches.iter().any(|l| l.peek_next_epoch() != epoch) {
        return Err(Poseidon2MpcError::EpochLatch(EpochLatchError::LatchesDisagree));
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
    let (_, quorum_pts) = validate_quorum_slices(t, key_shares, vaults, party_rngs)?;
    let committee_size = key_shares[0].committee_size;
    let mu = th_pre_hash(Poseidon2Suite, &pk.pk_seed, &pk.pk_root, msg);

    let ep0 =
        reserve_authorised_epoch(params, pk, t, committee_size, latch_cert, latches, &mu)?;
    let leaf_global_idx =
        usize::try_from(ep0).map_err(|_| Poseidon2MpcError::EpochLatch(EpochLatchError::Exhausted))?;

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
    let (_, quorum_pts) = validate_quorum_slices(t, key_shares, vaults, party_rngs)?;
    let committee_size = key_shares[0].committee_size;
    let mu = th_pre_hash(Poseidon2Suite, &pk.pk_seed, &pk.pk_root, msg);

    check_committee_latch_authorisation(
        pk,
        t,
        committee_size,
        latches.len(),
        latch_cert,
        epoch,
        &mu,
    )?;
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
    for rng in party_rngs.iter_mut() { rng.hedge_transcript(&transcript); }
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
