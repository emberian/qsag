//! `Hem`-aggregatable `JortsPoseidon2` (`w = 4, chains = 128, target_sum = 192, height = 6`)
//! quorum-switching threshold custody, proactive share refresh (`Π_refresh`), and dynamic
//! `(t, n) -> (t', n')` roster/threshold resharing (`Π_reshare`).
//!
//! Bridges `qsag-quorum` (`"QS"`) directly to `qsag-agg` (`"AG"` / `Hem`): every protocol in
//! this module produces canonical 65-byte [`HemJortsPublicKey`]s and 4,328-byte
//! [`HemJortsSignature`]s accepted byte-for-byte by `qsag_agg::ValidatorPublicKey`,
//! `qsag_agg::ValidatorSignature`, `qsag_agg::verify_individual_signature`, and untrusted public
//! `Hem` WHIR multi-signature aggregation under `BciksJohnsonQrom128`.
//!
//! Three custody architectures are provided:
//! 1. **Mode QS-A ([`HemCommitteePartitionedQuorum`]):** Partitions active XMSS leaves across all
//!    `binom(n, t)` `t`-custodian committees with `t`-of-`t` additive `Goldilocks` shares,
//!    2-round pairwise echo MACs, and monotone per-committee latches.
//! 2. **Mode QS-B ([`HemDynamicShamirQuorum`]):** Global XMSS tree with `(t, n)` Shamir shares
//!    authenticated under a shared `GoldilocksExt2` SPDZ MAC key, BFT/honest-intersection
//!    [`EpochLatchCertificate`] gating (`2q > n + (t - 1)`), zero-constant proactive refresh
//!    (`Π_refresh`), and 2-round committed + HVZK degree-`< t'` + SPDZ `MacCheck` dynamic
//!    `(t, n) -> (t', n')` quorum-switching (`Π_reshare`) preserving the exact 65-byte validator
//!    public key and monotone leaf high-water mark.
//! 3. **Seed-Level SPDZ MPC ([`HemSpdzSeedQuorum`]):** 100% dealerless bit-shared Goldilocks DKG,
//!    refresh, and `(t, n) -> (t', n')` seed resharing backed by native `[Goldilocks; 4]` SPDZ
//!    MPC (`0` intermediate A2B conversions).

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use qsag_core::dkg::{
    DkgError, EpochLatchAuthorityPublic, EpochLatchCertificate, EpochLatchError,
    ShamirPoseidonSeedShare, epoch_latch_binding, run_dealerless_dkg_seed32_goldilocks,
    run_dealerless_refresh_seed32_goldilocks, run_dealerless_reshare_seed32_goldilocks,
};
use qsag_core::field::goldilocks::{Goldilocks, GoldilocksExt2, lagrange_weights_zero_goldilocks};
use qsag_core::poseidon2_mpc::{
    HEM_DOMAIN_SK_PRF_EXPAND, HEM_DOMAIN_SK_SEED_EXPAND, Poseidon2MpcError,
    authenticate_poseidon_dkg_shares_and_preprocess,
    build_distributed_hem_jorts_key_mpc_with_active_leaves, hem_compress_wots_endpoints_sponge,
    hem_compute_message_mu, hem_derive_r_rand_clear, hem_digest4_from_bytes_canonical,
    hem_digest4_to_bytes, hem_expand_secret_bytes32_clear, hem_grind_stateful_tsw_digits,
    hem_merkle_auth_path, hem_merkle_root_from_leaves, hem_pk_seed_from_bytes32,
    hem_poseidon2_compress12_ff, hem_prf_check_digest_clear, hem_unassigned_leaf_digest,
    hem_wots_base_secret_clear, hem_wots_step_hash_injective,
    required_hem_jorts_keygen_preprocessing_budget,
    required_hem_jorts_reshare_verify_preprocessing_budget,
    required_hem_jorts_sign_preprocessing_budget_cached, sign_hem_jorts_poseidon2_mpc_cached,
    verify_reshared_hem_jorts_key_mpc,
};
pub use qsag_core::poseidon2_mpc::{
    HEM_JORTS_MAX_LEAVES, HEM_JORTS_PK_BYTES, HEM_JORTS_SIG_BYTES, HEM_JORTS_XMSS_HEIGHT,
    HEM_WOTS_BASE_W, HEM_WOTS_CHAINS, HEM_WOTS_MAX_STEP, HEM_WOTS_TARGET_SUM, HemDigest4,
    HemDigest5, HemJortsCachedTree, HemJortsPublicKey, HemJortsSignature,
    verify_hem_jorts_signature,
};
use qsag_core::preprocessing::{
    OtMesh, PartyPrivateRng, commit_and_open_spdz_goldilocks_batch_quorum,
    open_and_check_degree_ext2, open_and_check_degree_goldilocks,
    validate_all_eval_points_goldilocks,
};
use qsag_core::sponge::keccak::{cshake256_32, encode_multi_frame};
use qsag_core::sponge::poseidon2::{POSEIDON2_CONST_IV, poseidon2_hash32};
use qsag_core::tsw_baggy::MonotonicEpochLatch;
use qsag_core::wipe::{
    SecretBuffer, ct_eq_bytes32, wipe_bytes, wipe_bytes32, wipe_ext2, wipe_goldilocks,
};

use crate::hash::{mac32, mac32_verify};

const HEM_QSA_ECHO_TAG: &[u8] = b"QSAG.HEM.QSA.ECHO/v1";
const HEM_QSB_SUBSHARE_COMMIT_TAG: &[u8] = b"QSAG.HEM.QSB.COMMIT/v1";
const HEM_QSB_CHALLENGE_TAG: &[u8] = b"QSAG.HEM.QSB.CHAL/v1";
const HEM_PUB_DIR_MAGIC: &[u8; 8] = b"QSAGHDIR";
const HEM_CUSTODIAN_SHARE_MAGIC: &[u8; 8] = b"QSAGHSHR";

/// Exclusive roster bound for `HemDynamicShamirQuorum`: accept at most 255 custodians.
/// Kept at 256 for API compatibility; `HemSpdzSeedQuorum` retains its stricter bound.
pub const MAX_HEM_QUORUM_PARTIES: usize = 256;

// A session identifier is public protocol context, never key material. Each
// custodian supplies its own evolving private RNG; deriving an operation stream
// consumes fresh private randomness even if a caller retries with the same session ID.
fn private_operation_rng(
    session_id: &[u8; 32],
    domain: &[u8],
    party: usize,
    private_rng: &mut PartyPrivateRng,
) -> PartyPrivateRng {
    let mut frame = [0u8; 72];
    frame[..32].copy_from_slice(session_id);
    frame[32..40].copy_from_slice(&(party as u64).to_le_bytes());
    private_rng.fill_bytes(&mut frame[40..]);
    let mut seed = cshake256_32(domain, &frame);
    wipe_bytes(&mut frame);
    let stream = PartyPrivateRng::from_seed(seed, domain);
    wipe_bytes32(&mut seed);
    stream
}

fn private_operation_rngs(
    session_id: &[u8; 32],
    domain: &[u8],
    private_rngs: &mut [PartyPrivateRng],
) -> Vec<PartyPrivateRng> {
    private_rngs
        .iter_mut()
        .enumerate()
        .map(|(party, rng)| private_operation_rng(session_id, domain, party, rng))
        .collect()
}

fn check_randomness_count(rngs: &[PartyPrivateRng], expected: usize) -> Result<(), HemQuorumError> {
    if rngs.len() != expected {
        return Err(HemQuorumError::InvalidRandomnessCount {
            expected,
            got: rngs.len(),
        });
    }
    Ok(())
}

/// Errors returned by `Hem`-compatible quorum signing, proactive refresh, or dynamic resharing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HemQuorumError {
    InvalidQuorum {
        t: usize,
        n: usize,
    },
    InvalidRandomnessCount {
        expected: usize,
        got: usize,
    },
    InvalidActiveLeaves {
        active_leaves: usize,
    },
    QuorumEpochMismatch {
        expected: u64,
        got: u64,
        party: usize,
    },
    ShareInvalidated {
        party: usize,
    },
    UnknownCommittee,
    NotEnoughSigners {
        have: usize,
        need: usize,
    },
    DuplicateParty {
        party: usize,
    },
    PartyOutOfRange {
        party: usize,
        n: usize,
    },
    EchoMacInvalid {
        from: usize,
        to: usize,
    },
    CommitmentMismatch {
        dealer: usize,
        recipient: usize,
    },
    DegreeCheckFailed {
        dealer: usize,
    },
    ReshareMacCheckFailed,
    EndpointVerificationFailed {
        chain: usize,
    },
    PrfCommitmentMismatch,
    LatchRefused,
    LeafExhausted,
    TswGrindExhausted,
    SignatureSelfCheckFailed,
    MalformedVaultBytes,
    Dkg(DkgError),
    Mpc(Poseidon2MpcError),
}

impl From<DkgError> for HemQuorumError {
    fn from(e: DkgError) -> Self {
        Self::Dkg(e)
    }
}

impl From<Poseidon2MpcError> for HemQuorumError {
    fn from(e: Poseidon2MpcError) -> Self {
        Self::Mpc(e)
    }
}

impl fmt::Display for HemQuorumError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

impl core::error::Error for HemQuorumError {}

const HEM_LATCH_ACK_TAG: &[u8] = b"QSAG.HEM.EPOCH.ACK/v1";

/// Pinned BFT custodian MAC authority (`2 * q > n + (t - 1)`) for `Hem` quorum leaf latching.
#[derive(Clone)]
pub struct HemEpochLatchAuthority {
    mac_keys: Vec<[u8; 32]>,
}

/// Equality of the pinned MAC keys without data-dependent timing. The number of custodians
/// is public; every key pair is compared, with no early exit on the first difference.
impl PartialEq for HemEpochLatchAuthority {
    fn eq(&self, other: &Self) -> bool {
        if self.mac_keys.len() != other.mac_keys.len() {
            return false;
        }
        let mut equal = true;
        for (a, b) in self.mac_keys.iter().zip(&other.mac_keys) {
            equal &= ct_eq_bytes32(a, b);
        }
        equal
    }
}

impl Eq for HemEpochLatchAuthority {}

impl fmt::Debug for HemEpochLatchAuthority {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("HemEpochLatchAuthority([REDACTED])")
    }
}

impl Drop for HemEpochLatchAuthority {
    fn drop(&mut self) {
        for key in &mut self.mac_keys {
            wipe_bytes32(key);
        }
    }
}

impl HemEpochLatchAuthority {
    fn tag(&self, party: usize, n: usize, t: usize, epoch: u64, binding: &[u8; 32]) -> [u8; 32] {
        cshake256_32(
            HEM_LATCH_ACK_TAG,
            &encode_multi_frame(&[
                &self.mac_keys[party],
                &(party as u64).to_be_bytes(),
                &(n as u64).to_be_bytes(),
                &(t as u64).to_be_bytes(),
                &epoch.to_be_bytes(),
                binding,
            ]),
        )
    }

    /// Authenticate `cert` for `(n, t, epoch, binding)` under BFT quorum intersection `2 * q > n + (t - 1)`.
    pub fn verify_certificate(
        &self,
        cert: &HemEpochLatchCertificate,
        n: usize,
        t: usize,
        epoch: u64,
        binding: &[u8; 32],
    ) -> Result<(), HemQuorumError> {
        if t < 1 || n < t || self.mac_keys.len() != n || cert.n != n || cert.t != t {
            return Err(HemQuorumError::LatchRefused);
        }
        if cert.epoch != epoch || !ct_eq_bytes32(&cert.binding, binding) {
            return Err(HemQuorumError::LatchRefused);
        }
        let required = ((n + (t - 1)) / 2) + 1;
        if cert.acks.len() < required || cert.tags.len() != cert.acks.len() {
            return Err(HemQuorumError::LatchRefused);
        }
        let distinct_sorted =
            cert.acks.windows(2).all(|w| w[0] < w[1]) && cert.acks.last().is_none_or(|&p| p < n);
        if !distinct_sorted {
            return Err(HemQuorumError::LatchRefused);
        }
        let mut valid_acks = 0usize;
        for (&party, tag) in cert.acks.iter().zip(&cert.tags) {
            let expected = self.tag(party, n, t, epoch, binding);
            valid_acks += usize::from(ct_eq_bytes32(tag, &expected));
        }
        if valid_acks != cert.acks.len() {
            return Err(HemQuorumError::LatchRefused);
        }
        Ok(())
    }
}

/// BFT latch certificate (`2 * q > n + (t - 1)`) binding one XMSS leaf `epoch` to one message digest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HemEpochLatchCertificate {
    n: usize,
    t: usize,
    epoch: u64,
    binding: [u8; 32],
    acks: Vec<usize>,
    tags: Vec<[u8; 32]>,
}

impl HemEpochLatchCertificate {
    #[inline]
    pub const fn epoch(&self) -> u64 {
        self.epoch
    }

    #[inline]
    pub fn verify_against(
        &self,
        authority: &HemEpochLatchAuthority,
        n: usize,
        t: usize,
        epoch: u64,
        binding: &[u8; 32],
    ) -> Result<(), HemQuorumError> {
        authority.verify_certificate(self, n, t, epoch, binding)
    }
}

/// Monotone `no_std`-compatible BFT custodian latch cluster (`2 * q > n + (t - 1)`),
/// preserving `initial_floor` across dynamic `(t, n) -> (t', n')` resharing.
pub struct HemEpochLatchCluster {
    n: usize,
    t: usize,
    latch_quorum: usize,
    per_party_state: Vec<Option<(u64, [u8; 32])>>,
    initial_floor: u64,
    authority: HemEpochLatchAuthority,
}

impl HemEpochLatchCluster {
    pub fn establish(
        n: usize,
        t: usize,
        initial_floor: u64,
        party_rngs: &mut [PartyPrivateRng],
    ) -> Result<Self, HemQuorumError> {
        if t < 1 || n < t || party_rngs.len() < n {
            return Err(HemQuorumError::InvalidQuorum { t, n });
        }
        let latch_quorum = ((n + (t - 1)) / 2) + 1;
        if latch_quorum > n {
            return Err(HemQuorumError::InvalidQuorum { t, n });
        }
        let mut mac_keys = Vec::with_capacity(n);
        for (p, rng) in party_rngs.iter_mut().enumerate().take(n) {
            let mut key = cshake256_32(
                b"QSAG.HEM.LATCH.KEY/v1",
                &encode_multi_frame(&[&rng.next_bytes32(), &(p as u64).to_be_bytes()]),
            );
            if ct_eq_bytes32(&key, &[0u8; 32]) {
                key[0] = 1;
            }
            mac_keys.push(key);
        }
        Ok(Self {
            n,
            t,
            latch_quorum,
            per_party_state: vec![None; n],
            initial_floor,
            authority: HemEpochLatchAuthority { mac_keys },
        })
    }

    #[inline]
    pub fn authority_public(&self) -> &HemEpochLatchAuthority {
        &self.authority
    }

    /// Skip every epoch below `floor`. The floor only moves up, so no certified or
    /// skipped epoch is handed out again.
    fn raise_floor(&mut self, floor: u64) {
        self.initial_floor = self.initial_floor.max(floor);
    }

    fn next_unreserved_epoch(&self) -> u64 {
        let mut next = self.initial_floor;
        for (ep, _) in self.per_party_state.iter().flatten() {
            next = next.max(ep.saturating_add(1));
        }
        next
    }

    /// Certify the next monotone leaf epoch across `participating_ackers` (`>= latch_quorum`).
    pub fn certify_epoch(
        &mut self,
        participating_ackers: &[usize],
        latch_pk: &qsag_core::tsw_baggy::PqPublicKey,
        max_sigs_log2: u32,
        mu_bytes: &[u8; 32],
    ) -> Result<HemEpochLatchCertificate, HemQuorumError> {
        validate_party_subset(participating_ackers, self.latch_quorum, self.n)?;
        let epoch = self.next_unreserved_epoch();
        let max_epochs = 1u64.checked_shl(max_sigs_log2).unwrap_or(u64::MAX);
        if epoch >= max_epochs {
            return Err(HemQuorumError::LeafExhausted);
        }
        let binding = epoch_latch_binding(&latch_pk.pk_seed, &latch_pk.pk_root, epoch, mu_bytes);

        let mut accepted = Vec::with_capacity(participating_ackers.len());
        for &p in participating_ackers {
            let ok = match self.per_party_state[p] {
                None => epoch >= self.initial_floor,
                Some((hw, prev_bind)) => {
                    epoch > hw || (epoch == hw && ct_eq_bytes32(&prev_bind, &binding))
                }
            };
            if ok {
                accepted.push(p);
            }
        }
        if accepted.len() < self.latch_quorum {
            return Err(HemQuorumError::LatchRefused);
        }
        accepted.sort_unstable();
        for &p in &accepted {
            self.per_party_state[p] = Some((epoch, binding));
        }
        let tags = accepted
            .iter()
            .map(|&p| self.authority.tag(p, self.n, self.t, epoch, &binding))
            .collect();
        let cert = HemEpochLatchCertificate {
            n: self.n,
            t: self.t,
            epoch,
            binding,
            acks: accepted,
            tags,
        };
        cert.verify_against(&self.authority, self.n, self.t, epoch, &binding)?;
        Ok(cert)
    }
}

fn canonical_eval_points(n: usize) -> Vec<Goldilocks> {
    (1..=n as u64).map(Goldilocks::from_u64_reduced).collect()
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
        .map(|&x| {
            let mut acc = Goldilocks::ZERO;
            for &c in coeffs.iter().rev() {
                acc = acc * x + c;
            }
            acc
        })
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
        .map(|&x| {
            let mut acc = GoldilocksExt2::ZERO;
            for &c in coeffs.iter().rev() {
                acc = acc.mul_base(x) + c;
            }
            acc
        })
        .collect();
    wipe_ext2(&mut coeffs);
    out
}

fn validate_party_subset(
    indices: &[usize],
    min_len: usize,
    n: usize,
) -> Result<(), HemQuorumError> {
    if indices.len() < min_len {
        return Err(HemQuorumError::NotEnoughSigners {
            have: indices.len(),
            need: min_len,
        });
    }
    for (pos, &p) in indices.iter().enumerate() {
        if p >= n {
            return Err(HemQuorumError::PartyOutOfRange { party: p, n });
        }
        if indices[..pos].contains(&p) {
            return Err(HemQuorumError::DuplicateParty { party: p });
        }
    }
    Ok(())
}

fn derive_leaf_prf_secret_clear(
    sk_prf: HemDigest4,
    pk_seed: HemDigest4,
    kp_idx: u32,
) -> HemDigest4 {
    let tweak = [
        Goldilocks::from_u64_reduced(0x5153_4147_484C_5052), // "QSAGHLPR"
        Goldilocks::from_u64_reduced(kp_idx as u64),
        Goldilocks::ZERO,
        Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV),
    ];
    hem_poseidon2_compress12_ff(sk_prf, pk_seed, tweak)
}

// ============================================================================
// 1. Mode QS-A: `HemCommitteePartitionedQuorum` (`binom(n, t)` Subtrees)
// ============================================================================

#[derive(Clone, Debug, PartialEq, Eq)]
struct CommitteeRange {
    members: Vec<usize>,
    leaf_start: usize,
    leaf_end: usize,
}

struct HemQsaCustodian {
    party_id: usize,
    pair_keys: Vec<[u8; 32]>,
    committee_next_leaf: Vec<usize>,
    committee_in_flight: Vec<Option<(usize, [u8; 32])>>,
    /// Indexed by `[leaf_idx]`: `Some` iff `party_id` belongs to the committee owning `leaf_idx`.
    leaf_prf_shares: Vec<Option<HemDigest4>>,
    leaf_chain_shares: Vec<Option<Vec<[HemDigest4; HEM_WOTS_MAX_STEP]>>>,
}

impl fmt::Debug for HemQsaCustodian {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("HemQsaCustodian")
            .field("party_id", &self.party_id)
            .finish_non_exhaustive()
    }
}

impl Drop for HemQsaCustodian {
    fn drop(&mut self) {
        for k in &mut self.pair_keys {
            wipe_bytes32(k);
        }
        for prf in self.leaf_prf_shares.iter_mut().flatten() {
            wipe_goldilocks(prf);
        }
        for chains in self.leaf_chain_shares.iter_mut().flatten() {
            for steps in chains.iter_mut() {
                for st in steps.iter_mut() {
                    wipe_goldilocks(st);
                }
            }
        }
    }
}

/// Mode `QS-A` (`CommitteePartitionedJorts` over `Hem` `JortsPoseidon2` `w=4, chains=128, sum=192`):
/// partitions the XMSS leaves into disjoint committee ranges, shared `t`-of-`t` additively over
/// `Goldilocks` with pairwise echo-MAC confirmation before any chain share opens.
pub struct HemCommitteePartitionedQuorum {
    t: usize,
    n: usize,
    pk: HemJortsPublicKey,
    leaves: Vec<HemDigest4>,
    endpoints: Vec<[HemDigest4; HEM_WOTS_CHAINS]>,
    prf_commits: Vec<HemDigest4>,
    committees: Vec<CommitteeRange>,
    custodians: Vec<HemQsaCustodian>,
}

impl fmt::Debug for HemCommitteePartitionedQuorum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("HemCommitteePartitionedQuorum")
            .field("t", &self.t)
            .field("n", &self.n)
            .field("pk", &self.pk)
            .finish_non_exhaustive()
    }
}

fn enumerate_combinations(n: usize, t: usize) -> Vec<Vec<usize>> {
    let mut out = Vec::new();
    let mut cur = Vec::with_capacity(t);
    fn rec(start: usize, n: usize, t: usize, cur: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
        if cur.len() == t {
            out.push(cur.clone());
            return;
        }
        let rem = t - cur.len();
        if start + rem > n {
            return;
        }
        for i in start..=(n - rem) {
            cur.push(i);
            rec(i + 1, n, t, cur, out);
            cur.pop();
        }
    }
    rec(0, n, t, &mut cur, &mut out);
    out
}

impl HemCommitteePartitionedQuorum {
    /// Stage a `t`-of-`n` committee-partitioned `Hem` `JortsPoseidon2` quorum from ceremony entropy.
    pub fn stage(
        ceremony_seed: [u8; 32],
        t: usize,
        n: usize,
        leaves_per_committee: usize,
    ) -> Result<Self, HemQuorumError> {
        if t < 2 || t > n || n > 12 {
            return Err(HemQuorumError::InvalidQuorum { t, n });
        }
        let combos = enumerate_combinations(n, t);
        let active_leaves = combos
            .len()
            .checked_mul(leaves_per_committee)
            .ok_or(HemQuorumError::InvalidActiveLeaves { active_leaves: 0 })?;
        if leaves_per_committee == 0 || active_leaves > HEM_JORTS_MAX_LEAVES {
            return Err(HemQuorumError::InvalidActiveLeaves { active_leaves });
        }

        let mut rng = PartyPrivateRng::from_seed(
            cshake256_32(b"QSAG.HEM.QSA.RNG/v1", &ceremony_seed),
            b"QSAG.HEM.QSA.RNG.STREAM/v1",
        );
        let dkg_pk_seed = cshake256_32(b"QSAG.HEM.QSA.PKSEED/v1", &ceremony_seed);
        let mut sk_seed_bytes = cshake256_32(b"QSAG.HEM.QSA.SKSEED/v1", &ceremony_seed);
        let mut sk_prf_bytes = cshake256_32(b"QSAG.HEM.QSA.SKPRF/v1", &ceremony_seed);

        let pk_seed = hem_pk_seed_from_bytes32(&dkg_pk_seed);
        let mut sk_seed =
            hem_expand_secret_bytes32_clear(&sk_seed_bytes, pk_seed, HEM_DOMAIN_SK_SEED_EXPAND);
        let mut sk_prf =
            hem_expand_secret_bytes32_clear(&sk_prf_bytes, pk_seed, HEM_DOMAIN_SK_PRF_EXPAND);
        wipe_bytes32(&mut sk_seed_bytes);
        wipe_bytes32(&mut sk_prf_bytes);

        let mut pair_matrix = vec![vec![[0u8; 32]; n]; n];
        for i in 0..n {
            let (upper, lower) = pair_matrix.split_at_mut(i + 1);
            let row_i = &mut upper[i];
            for (offset, row_j) in lower.iter_mut().enumerate() {
                let k = rng.next_bytes32();
                row_i[i + 1 + offset] = k;
                row_j[i] = k;
            }
        }

        let mut committees = Vec::with_capacity(combos.len());
        for (c_idx, members) in combos.into_iter().enumerate() {
            committees.push(CommitteeRange {
                members,
                leaf_start: c_idx * leaves_per_committee,
                leaf_end: (c_idx + 1) * leaves_per_committee,
            });
        }

        let mut custodians: Vec<HemQsaCustodian> = (0..n)
            .map(|p| HemQsaCustodian {
                party_id: p,
                pair_keys: pair_matrix[p].clone(),
                committee_next_leaf: committees.iter().map(|c| c.leaf_start).collect(),
                committee_in_flight: vec![None; committees.len()],
                leaf_prf_shares: vec![None; active_leaves],
                leaf_chain_shares: vec![None; active_leaves],
            })
            .collect();
        for row in &mut pair_matrix {
            for k in row {
                wipe_bytes32(k);
            }
        }

        let mut leaves = Vec::with_capacity(HEM_JORTS_MAX_LEAVES);
        let mut endpoints = Vec::with_capacity(active_leaves);
        let mut prf_commits = Vec::with_capacity(active_leaves);

        for (c_idx, comm) in committees.iter().enumerate() {
            let _ = c_idx;
            for kp in comm.leaf_start..comm.leaf_end {
                let mut prf_secret = derive_leaf_prf_secret_clear(sk_prf, pk_seed, kp as u32);
                prf_commits.push(hem_prf_check_digest_clear(prf_secret, pk_seed));

                // Split `prf_secret` into `t` additive `Goldilocks` shares
                let mut prf_rem = SecretBuffer(prf_secret);
                for &member in &comm.members[..t - 1] {
                    let sh = SecretBuffer(core::array::from_fn(|_| rng.next_goldilocks()));
                    for l in 0..4 {
                        prf_rem[l] -= sh[l];
                    }
                    custodians[member].leaf_prf_shares[kp] = Some(*sh);
                }
                custodians[comm.members[t - 1]].leaf_prf_shares[kp] = Some(*prf_rem);
                drop(prf_rem);
                wipe_goldilocks(&mut prf_secret);

                let mut kp_endpoints = [[Goldilocks::ZERO; 4]; HEM_WOTS_CHAINS];
                let mut per_member_chains: Vec<Vec<[HemDigest4; HEM_WOTS_MAX_STEP]>> = (0..t)
                    .map(|_| Vec::with_capacity(HEM_WOTS_CHAINS))
                    .collect();

                for (r, ep_slot) in kp_endpoints.iter_mut().enumerate().take(HEM_WOTS_CHAINS) {
                    let y0 = SecretBuffer(hem_wots_base_secret_clear(
                        sk_seed, pk_seed, 0, 0, kp as u32, r as u32,
                    ));
                    let y1 = SecretBuffer(hem_wots_step_hash_injective(
                        pk_seed, *y0, 0, 0, kp as u32, r as u32, 0,
                    ));
                    let y2 = SecretBuffer(hem_wots_step_hash_injective(
                        pk_seed, *y1, 0, 0, kp as u32, r as u32, 1,
                    ));
                    let y3 =
                        hem_wots_step_hash_injective(pk_seed, *y2, 0, 0, kp as u32, r as u32, 2);
                    *ep_slot = y3;
                    let secret_states = SecretBuffer([*y0, *y1, *y2]);
                    drop((y0, y1, y2));

                    let mut member_steps =
                        SecretBuffer(vec![[[Goldilocks::ZERO; 4]; HEM_WOTS_MAX_STEP]; t]);
                    for step in 0..HEM_WOTS_MAX_STEP {
                        let mut rem = SecretBuffer(secret_states[step]);
                        for m_slot in member_steps.iter_mut().take(t - 1) {
                            let sh = SecretBuffer(core::array::from_fn(|_| rng.next_goldilocks()));
                            for l in 0..4 {
                                rem[l] -= sh[l];
                            }
                            m_slot[step] = *sh;
                        }
                        member_steps[t - 1][step] = *rem;
                    }
                    for m_idx in 0..t {
                        per_member_chains[m_idx].push(member_steps[m_idx]);
                    }
                }

                for (m_idx, &party) in comm.members.iter().enumerate() {
                    custodians[party].leaf_chain_shares[kp] =
                        Some(core::mem::take(&mut per_member_chains[m_idx]));
                }
                leaves.push(hem_compress_wots_endpoints_sponge(
                    pk_seed,
                    0,
                    0,
                    kp as u32,
                    &kp_endpoints,
                ));
                endpoints.push(kp_endpoints);
            }
        }
        wipe_goldilocks(&mut sk_seed);
        wipe_goldilocks(&mut sk_prf);

        for kp in active_leaves..HEM_JORTS_MAX_LEAVES {
            leaves.push(hem_unassigned_leaf_digest(pk_seed, kp as u32));
        }
        let pk_root = hem_merkle_root_from_leaves(pk_seed, &leaves)
            .ok_or(HemQuorumError::InvalidActiveLeaves { active_leaves })?;

        Ok(Self {
            t,
            n,
            pk: HemJortsPublicKey { pk_seed, pk_root },
            leaves,
            endpoints,
            prf_commits,
            committees,
            custodians,
        })
    }

    #[inline]
    pub fn public_key(&self) -> HemJortsPublicKey {
        self.pk
    }

    /// Sign `msg` using the unique `t`-member committee matching `signers`, emitting an exact
    /// 4,328-byte [`HemJortsSignature`].
    pub fn sign_with_committee(
        &mut self,
        signers: &[usize],
        msg: &[u8],
    ) -> Result<(u64, HemJortsSignature), HemQuorumError> {
        validate_party_subset(signers, self.t, self.n)?;
        if signers.len() != self.t {
            return Err(HemQuorumError::UnknownCommittee);
        }
        let mut sorted = signers.to_vec();
        sorted.sort_unstable();
        let comm_idx = self
            .committees
            .iter()
            .position(|c| c.members == sorted)
            .ok_or(HemQuorumError::UnknownCommittee)?;
        let comm = &self.committees[comm_idx];

        let leaf_idx = self.custodians[sorted[0]].committee_next_leaf[comm_idx];
        if leaf_idx >= comm.leaf_end {
            return Err(HemQuorumError::LeafExhausted);
        }
        for &p in &sorted[1..] {
            if self.custodians[p].committee_next_leaf[comm_idx] != leaf_idx {
                return Err(HemQuorumError::LatchRefused);
            }
        }

        let (mu_bytes, mu) = hem_compute_message_mu(&self.pk, msg);
        let leaf_le = (leaf_idx as u64).to_le_bytes();
        let binding = encode_multi_frame(&[&self.pk.to_bytes(), &leaf_le, &mu_bytes]);

        // 2-round pairwise echo MAC verification across all `t` committee members before latching
        let mut echoes = Vec::with_capacity(self.t * self.t);
        for &from in &sorted {
            for &to in &sorted {
                if from != to {
                    let tag = mac32(
                        &self.custodians[from].pair_keys[to],
                        HEM_QSA_ECHO_TAG,
                        &[&binding],
                    );
                    echoes.push((from, to, tag));
                }
            }
        }
        for (from, to, tag) in &echoes {
            if !mac32_verify(
                &self.custodians[*to].pair_keys[*from],
                HEM_QSA_ECHO_TAG,
                &[&binding],
                tag,
            ) {
                return Err(HemQuorumError::EchoMacInvalid {
                    from: *from,
                    to: *to,
                });
            }
        }

        // Advance every committee member's monotone latch strictly before opening any secret share
        for &p in &sorted {
            self.custodians[p].committee_in_flight[comm_idx] = Some((leaf_idx, mu_bytes));
            self.custodians[p].committee_next_leaf[comm_idx] = leaf_idx + 1;
        }

        let mut prf_leaf = [Goldilocks::ZERO; 4];
        for &p in &sorted {
            let sh = self.custodians[p].leaf_prf_shares[leaf_idx]
                .ok_or(HemQuorumError::ShareInvalidated { party: p })?;
            for l in 0..4 {
                prf_leaf[l] += sh[l];
            }
        }
        if hem_prf_check_digest_clear(prf_leaf, self.pk.pk_seed) != self.prf_commits[leaf_idx] {
            wipe_goldilocks(&mut prf_leaf);
            return Err(HemQuorumError::PrfCommitmentMismatch);
        }

        let r_rand = hem_derive_r_rand_clear(prf_leaf, self.pk.pk_seed, mu, leaf_idx as u64);
        wipe_goldilocks(&mut prf_leaf);

        let (tsw_ctr, digits) = hem_grind_stateful_tsw_digits(
            self.pk.pk_seed,
            self.pk.pk_root,
            r_rand,
            mu,
            leaf_idx as u32,
            100_000,
        )
        .ok_or(HemQuorumError::TswGrindExhausted)?;

        let mut wots_chains = Vec::with_capacity(HEM_WOTS_CHAINS);
        for (r, &d) in digits.iter().enumerate().take(HEM_WOTS_CHAINS) {
            let d_usize = d as usize;
            if d_usize == HEM_WOTS_MAX_STEP {
                wots_chains.push(self.endpoints[leaf_idx][r]);
            } else {
                let mut acc = [Goldilocks::ZERO; 4];
                for &p in &sorted {
                    let chains = self.custodians[p].leaf_chain_shares[leaf_idx]
                        .as_ref()
                        .ok_or(HemQuorumError::ShareInvalidated { party: p })?;
                    for l in 0..4 {
                        acc[l] += chains[r][d_usize][l];
                    }
                }
                let mut cur = acc;
                for step in (d as u32)..(HEM_WOTS_MAX_STEP as u32) {
                    cur = hem_wots_step_hash_injective(
                        self.pk.pk_seed,
                        cur,
                        0,
                        0,
                        leaf_idx as u32,
                        r as u32,
                        step,
                    );
                }
                if cur != self.endpoints[leaf_idx][r] {
                    return Err(HemQuorumError::EndpointVerificationFailed { chain: r });
                }
                wots_chains.push(acc);
            }
        }

        // Burn spent leaf shares in RAM immediately after opening
        for &p in &sorted {
            if let Some(mut prf_sh) = self.custodians[p].leaf_prf_shares[leaf_idx].take() {
                wipe_goldilocks(&mut prf_sh);
            }
            if let Some(mut ch_sh) = self.custodians[p].leaf_chain_shares[leaf_idx].take() {
                for steps in &mut ch_sh {
                    for st in steps {
                        wipe_goldilocks(st);
                    }
                }
            }
        }

        let (merkle_path, _) = hem_merkle_auth_path(self.pk.pk_seed, &self.leaves, leaf_idx)
            .ok_or(HemQuorumError::SignatureSelfCheckFailed)?;
        let sig = HemJortsSignature {
            r_rand,
            stateful_leaf_idx: leaf_idx as u32,
            tsw_ctr,
            wots_chains,
            merkle_path,
        };
        if !verify_hem_jorts_signature(&self.pk, msg, &sig) {
            return Err(HemQuorumError::SignatureSelfCheckFailed);
        }
        Ok((leaf_idx as u64, sig))
    }
}

// ============================================================================
// 2. Mode QS-B: `HemDynamicShamirQuorum` (`Π_refresh` & `(t, n) -> (t', n')` `Π_reshare`)
// ============================================================================

/// Public directory of a [`HemDynamicShamirQuorum`] validator: immutable across unlimited
/// proactive refreshes (`Π_refresh`) and `(t, n) -> (t', n')` threshold/roster switches (`Π_reshare`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HemQuorumPublicDirectory {
    pub dkg_pk_seed: [u8; 32],
    pub pk: HemJortsPublicKey,
    pub active_leaves: usize,
    pub leaves: Vec<HemDigest4>,
    pub endpoints: Vec<[HemDigest4; HEM_WOTS_CHAINS]>,
    pub prf_commits: Vec<HemDigest4>,
}

impl HemQuorumPublicDirectory {
    /// Verify that all public `endpoints` compress to `leaves[0..active_leaves]`, unassigned
    /// leaves match `hem_unassigned_leaf_digest`, and the 64 leaves Merkle-hash to `pk.pk_root`.
    pub fn verify_consistency(&self) -> bool {
        if self.active_leaves == 0
            || self.active_leaves > HEM_JORTS_MAX_LEAVES
            || self.leaves.len() != HEM_JORTS_MAX_LEAVES
            || self.endpoints.len() != self.active_leaves
            || self.prf_commits.len() != self.active_leaves
        {
            return false;
        }
        if self.pk.pk_seed != hem_pk_seed_from_bytes32(&self.dkg_pk_seed) {
            return false;
        }
        for kp in 0..self.active_leaves {
            let expected = hem_compress_wots_endpoints_sponge(
                self.pk.pk_seed,
                0,
                0,
                kp as u32,
                &self.endpoints[kp],
            );
            if self.leaves[kp] != expected {
                return false;
            }
        }
        for kp in self.active_leaves..HEM_JORTS_MAX_LEAVES {
            if self.leaves[kp] != hem_unassigned_leaf_digest(self.pk.pk_seed, kp as u32) {
                return false;
            }
        }
        hem_merkle_root_from_leaves(self.pk.pk_seed, &self.leaves) == Some(self.pk.pk_root)
    }

    /// Canonical binary serialization for CLI/vault persistence.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(HEM_PUB_DIR_MAGIC);
        out.extend_from_slice(&self.dkg_pk_seed);
        out.extend_from_slice(&self.pk.to_bytes());
        out.extend_from_slice(&(self.active_leaves as u32).to_le_bytes());
        for leaf in &self.leaves {
            out.extend_from_slice(&hem_digest4_to_bytes(leaf));
        }
        for ep_arr in &self.endpoints {
            for ep in ep_arr {
                out.extend_from_slice(&hem_digest4_to_bytes(ep));
            }
        }
        for pc in &self.prf_commits {
            out.extend_from_slice(&hem_digest4_to_bytes(pc));
        }
        out
    }

    /// Canonical binary deserialization with full structural Merkle & endpoint verification.
    pub fn from_bytes_canonical(bytes: &[u8]) -> Result<Self, HemQuorumError> {
        let mut pos = 0usize;
        if bytes.get(0..8) != Some(HEM_PUB_DIR_MAGIC.as_slice()) {
            return Err(HemQuorumError::MalformedVaultBytes);
        }
        pos += 8;
        let dkg_pk_seed: [u8; 32] = bytes
            .get(pos..pos + 32)
            .and_then(|s| s.try_into().ok())
            .ok_or(HemQuorumError::MalformedVaultBytes)?;
        pos += 32;
        let pk_raw: [u8; HEM_JORTS_PK_BYTES] = bytes
            .get(pos..pos + HEM_JORTS_PK_BYTES)
            .and_then(|s| s.try_into().ok())
            .ok_or(HemQuorumError::MalformedVaultBytes)?;
        pos += HEM_JORTS_PK_BYTES;
        let pk = HemJortsPublicKey::from_bytes_canonical(&pk_raw)
            .ok_or(HemQuorumError::MalformedVaultBytes)?;
        let active_u32 = u32::from_le_bytes(
            bytes
                .get(pos..pos + 4)
                .and_then(|s| s.try_into().ok())
                .ok_or(HemQuorumError::MalformedVaultBytes)?,
        );
        pos += 4;
        let active_leaves = active_u32 as usize;
        if active_leaves == 0 || active_leaves > HEM_JORTS_MAX_LEAVES {
            return Err(HemQuorumError::MalformedVaultBytes);
        }

        let read_d4 = |buf: &[u8], p: &mut usize| -> Result<HemDigest4, HemQuorumError> {
            let raw: [u8; 32] = buf
                .get(*p..*p + 32)
                .and_then(|s| s.try_into().ok())
                .ok_or(HemQuorumError::MalformedVaultBytes)?;
            *p += 32;
            hem_digest4_from_bytes_canonical(&raw).ok_or(HemQuorumError::MalformedVaultBytes)
        };

        let mut leaves = Vec::with_capacity(HEM_JORTS_MAX_LEAVES);
        for _ in 0..HEM_JORTS_MAX_LEAVES {
            leaves.push(read_d4(bytes, &mut pos)?);
        }
        let mut endpoints = Vec::with_capacity(active_leaves);
        for _ in 0..active_leaves {
            let mut arr = [[Goldilocks::ZERO; 4]; HEM_WOTS_CHAINS];
            for slot in &mut arr {
                *slot = read_d4(bytes, &mut pos)?;
            }
            endpoints.push(arr);
        }
        let mut prf_commits = Vec::with_capacity(active_leaves);
        for _ in 0..active_leaves {
            prf_commits.push(read_d4(bytes, &mut pos)?);
        }
        if pos != bytes.len() {
            return Err(HemQuorumError::MalformedVaultBytes);
        }
        let dir = Self {
            dkg_pk_seed,
            pk,
            active_leaves,
            leaves,
            endpoints,
            prf_commits,
        };
        if !dir.verify_consistency() {
            return Err(HemQuorumError::MalformedVaultBytes);
        }
        Ok(dir)
    }
}

/// Number of `Goldilocks` scalars stored per unspent leaf (`4` PRF + `128 * 3 * 4` WOTS = `1,540`).
pub const HEM_LEAF_SCALARS: usize = 4 + HEM_WOTS_CHAINS * HEM_WOTS_MAX_STEP * 4;

/// Single custodian's isolated `(t, n)` Shamir share + `GoldilocksExt2` SPDZ MAC share for
/// [`HemDynamicShamirQuorum`].
pub struct HemShamirCustodianShare {
    pub party_id: usize,
    pub quorum_epoch: u64,
    pub t: usize,
    pub n: usize,
    pub eval_point: Goldilocks,
    pub high_water_leaf: usize,
    pub active_leaves: usize,
    pub invalidated: bool,
    alpha_share: GoldilocksExt2,
    /// Unspent leaves `high_water_leaf..active_leaves`, each holding `HEM_LEAF_SCALARS` values.
    leaf_vals: Vec<Vec<Goldilocks>>,
    leaf_macs: Vec<Vec<GoldilocksExt2>>,
}

impl fmt::Debug for HemShamirCustodianShare {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("HemShamirCustodianShare")
            .field("party_id", &self.party_id)
            .field("quorum_epoch", &self.quorum_epoch)
            .field("t", &self.t)
            .field("n", &self.n)
            .field("high_water_leaf", &self.high_water_leaf)
            .field("invalidated", &self.invalidated)
            .finish_non_exhaustive()
    }
}

impl HemShamirCustodianShare {
    /// Permanently invalidate this custodian share and volatile-wipe all secret field/MAC storage.
    pub fn invalidate_and_wipe(&mut self) {
        self.invalidated = true;
        wipe_ext2(core::slice::from_mut(&mut self.alpha_share));
        for v in &mut self.leaf_vals {
            wipe_goldilocks(v);
            v.clear();
        }
        for m in &mut self.leaf_macs {
            wipe_ext2(m);
            m.clear();
        }
    }

    /// Wipe every unspent leaf below `new_high_water` and move this share's high-water
    /// mark up to it. Never moves the mark down. Used when a leaf is reserved, and to bring
    /// shares that a crashed writer left behind up to the highest mark any share recorded.
    pub fn burn_leaves_below(&mut self, new_high_water: usize) {
        let cap = new_high_water.min(self.active_leaves);
        while self.high_water_leaf < cap {
            let idx = self.high_water_leaf;
            wipe_goldilocks(&mut self.leaf_vals[idx]);
            self.leaf_vals[idx].clear();
            wipe_ext2(&mut self.leaf_macs[idx]);
            self.leaf_macs[idx].clear();
            self.high_water_leaf += 1;
        }
    }

    /// Export a detached snapshot of this custodian share for persistence or adversarial testing.
    pub fn to_vault_bytes(&self) -> Result<Vec<u8>, HemQuorumError> {
        if self.invalidated {
            return Err(HemQuorumError::ShareInvalidated {
                party: self.party_id,
            });
        }
        let mut out = Vec::new();
        out.extend_from_slice(HEM_CUSTODIAN_SHARE_MAGIC);
        out.extend_from_slice(&(self.party_id as u32).to_le_bytes());
        out.extend_from_slice(&self.quorum_epoch.to_le_bytes());
        out.extend_from_slice(&(self.t as u32).to_le_bytes());
        out.extend_from_slice(&(self.n as u32).to_le_bytes());
        out.extend_from_slice(&self.eval_point.to_le_bytes());
        out.extend_from_slice(&(self.high_water_leaf as u32).to_le_bytes());
        out.extend_from_slice(&(self.active_leaves as u32).to_le_bytes());
        out.extend_from_slice(&self.alpha_share.c0.to_le_bytes());
        out.extend_from_slice(&self.alpha_share.c1.to_le_bytes());
        for kp in self.high_water_leaf..self.active_leaves {
            if self.leaf_vals[kp].len() != HEM_LEAF_SCALARS
                || self.leaf_macs[kp].len() != HEM_LEAF_SCALARS
            {
                return Err(HemQuorumError::MalformedVaultBytes);
            }
            for &g in &self.leaf_vals[kp] {
                out.extend_from_slice(&g.to_le_bytes());
            }
            for &m in &self.leaf_macs[kp] {
                out.extend_from_slice(&m.c0.to_le_bytes());
                out.extend_from_slice(&m.c1.to_le_bytes());
            }
        }
        Ok(out)
    }

    /// Restore an isolated custodian share from canonical vault bytes.
    pub fn from_vault_bytes(bytes: &[u8]) -> Result<Self, HemQuorumError> {
        if bytes.get(0..8) != Some(HEM_CUSTODIAN_SHARE_MAGIC.as_slice()) {
            return Err(HemQuorumError::MalformedVaultBytes);
        }
        let mut pos = 8usize;
        let read_u32 = |buf: &[u8], p: &mut usize| -> Result<u32, HemQuorumError> {
            let raw: [u8; 4] = buf
                .get(*p..*p + 4)
                .and_then(|s| s.try_into().ok())
                .ok_or(HemQuorumError::MalformedVaultBytes)?;
            *p += 4;
            Ok(u32::from_le_bytes(raw))
        };
        let read_u64 = |buf: &[u8], p: &mut usize| -> Result<u64, HemQuorumError> {
            let raw: [u8; 8] = buf
                .get(*p..*p + 8)
                .and_then(|s| s.try_into().ok())
                .ok_or(HemQuorumError::MalformedVaultBytes)?;
            *p += 8;
            Ok(u64::from_le_bytes(raw))
        };
        let read_gl = |buf: &[u8], p: &mut usize| -> Result<Goldilocks, HemQuorumError> {
            let raw: [u8; 8] = buf
                .get(*p..*p + 8)
                .and_then(|s| s.try_into().ok())
                .ok_or(HemQuorumError::MalformedVaultBytes)?;
            *p += 8;
            Goldilocks::from_le_bytes_canonical(raw)
                .map_err(|_| HemQuorumError::MalformedVaultBytes)
        };

        let party_id = read_u32(bytes, &mut pos)? as usize;
        let quorum_epoch = read_u64(bytes, &mut pos)?;
        let t = read_u32(bytes, &mut pos)? as usize;
        let n = read_u32(bytes, &mut pos)? as usize;
        if t < 2 || t > n || n >= MAX_HEM_QUORUM_PARTIES || party_id >= n {
            return Err(HemQuorumError::MalformedVaultBytes);
        }
        let eval_point = read_gl(bytes, &mut pos)?;
        let high_water_leaf = read_u32(bytes, &mut pos)? as usize;
        let active_leaves = read_u32(bytes, &mut pos)? as usize;
        if active_leaves == 0
            || active_leaves > HEM_JORTS_MAX_LEAVES
            || high_water_leaf > active_leaves
        {
            return Err(HemQuorumError::MalformedVaultBytes);
        }
        let alpha_c0 = read_gl(bytes, &mut pos)?;
        let alpha_c1 = read_gl(bytes, &mut pos)?;
        let alpha_share = GoldilocksExt2::new(alpha_c0, alpha_c1);

        let mut leaf_vals = vec![Vec::new(); active_leaves];
        let mut leaf_macs = vec![Vec::new(); active_leaves];
        for kp in high_water_leaf..active_leaves {
            let mut vals = Vec::with_capacity(HEM_LEAF_SCALARS);
            for _ in 0..HEM_LEAF_SCALARS {
                vals.push(read_gl(bytes, &mut pos)?);
            }
            let mut macs = Vec::with_capacity(HEM_LEAF_SCALARS);
            for _ in 0..HEM_LEAF_SCALARS {
                let c0 = read_gl(bytes, &mut pos)?;
                let c1 = read_gl(bytes, &mut pos)?;
                macs.push(GoldilocksExt2::new(c0, c1));
            }
            leaf_vals[kp] = vals;
            leaf_macs[kp] = macs;
        }
        if pos != bytes.len() {
            return Err(HemQuorumError::MalformedVaultBytes);
        }

        Ok(Self {
            party_id,
            quorum_epoch,
            t,
            n,
            eval_point,
            high_water_leaf,
            active_leaves,
            invalidated: false,
            alpha_share,
            leaf_vals,
            leaf_macs,
        })
    }
}

impl Drop for HemShamirCustodianShare {
    fn drop(&mut self) {
        self.invalidate_and_wipe();
    }
}

/// Fault-injection hook for testing `Π_reshare` / `Π_refresh` adversarial detection.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReshareFaultInjection {
    None,
    /// Flip a scalar inside dealer `dealer`'s sub-packet to `recipient` AFTER Round-1 commitment.
    TamperInTransit {
        dealer: usize,
        recipient: usize,
    },
    /// Dealer `dealer` commits consistently in Round 1 to shares that have degree `>= new_t`.
    CorruptPolynomialDegree {
        dealer: usize,
    },
    /// Dealer `dealer` commits to a valid degree-`< new_t` polynomial with shifted constant term.
    ShiftConstantTerm {
        dealer: usize,
    },
}

fn hash_subshare_packet_commitment(
    session_id: &[u8; 32],
    dealer: usize,
    recipient: usize,
    alpha_sub: GoldilocksExt2,
    mask_eval: GoldilocksExt2,
    vals: &[Goldilocks],
    macs: &[GoldilocksExt2],
) -> [u8; 32] {
    let mut buf = Vec::with_capacity(64 + vals.len() * 24);
    buf.extend_from_slice(HEM_QSB_SUBSHARE_COMMIT_TAG);
    buf.extend_from_slice(session_id);
    buf.extend_from_slice(&(dealer as u32).to_le_bytes());
    buf.extend_from_slice(&(recipient as u32).to_le_bytes());
    buf.extend_from_slice(&alpha_sub.c0.to_le_bytes());
    buf.extend_from_slice(&alpha_sub.c1.to_le_bytes());
    buf.extend_from_slice(&mask_eval.c0.to_le_bytes());
    buf.extend_from_slice(&mask_eval.c1.to_le_bytes());
    for &v in vals {
        buf.extend_from_slice(&v.to_le_bytes());
    }
    for &m in macs {
        buf.extend_from_slice(&m.c0.to_le_bytes());
        buf.extend_from_slice(&m.c1.to_le_bytes());
    }
    let digest = poseidon2_hash32(&buf);
    qsag_asm::volatile_fill(&mut buf, 0);
    digest
}

/// One leaf taken out of a [`HemDynamicShamirQuorum`] by
/// [`HemDynamicShamirQuorum::reserve_leaf`]: the latch certificate that binds the leaf to its
/// message, and the signers' shares of that leaf only. The quorum itself no longer holds the
/// leaf. Not `Clone`; the leaf material is wiped on drop.
pub struct HemReservedLeaf {
    cert: HemEpochLatchCertificate,
    signer_shares: Vec<HemShamirCustodianShare>,
}

impl fmt::Debug for HemReservedLeaf {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("HemReservedLeaf")
            .field("leaf_epoch", &self.cert.epoch())
            .finish_non_exhaustive()
    }
}

impl HemReservedLeaf {
    /// The reserved leaf index.
    #[inline]
    pub const fn leaf_epoch(&self) -> u64 {
        self.cert.epoch()
    }
}

/// Mode `QS-B` Dynamic `(t, n)` Shamir Quorum for `Hem` `JortsPoseidon2` supporting:
/// - Threshold signing (`sign_quorum`) emitting canonical 4,328-byte [`HemJortsSignature`]s,
/// - Zero-constant proactive share refresh (`proactive_refresh` / `Π_refresh`),
/// - Dynamic `(t, n) -> (t', n')` threshold & roster switching (`reshare_quorum` / `Π_reshare`)
///   preserving the exact 65-byte validator public key and monotone leaf high-water mark.
pub struct HemDynamicShamirQuorum {
    quorum_epoch: u64,
    t: usize,
    n: usize,
    high_water_leaf: usize,
    public_dir: HemQuorumPublicDirectory,
    latch_cluster: HemEpochLatchCluster,
    shares: Vec<HemShamirCustodianShare>,
}

impl fmt::Debug for HemDynamicShamirQuorum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("HemDynamicShamirQuorum")
            .field("quorum_epoch", &self.quorum_epoch)
            .field("t", &self.t)
            .field("n", &self.n)
            .field("high_water_leaf", &self.high_water_leaf)
            .field("pk", &self.public_dir.pk)
            .finish_non_exhaustive()
    }
}

impl HemDynamicShamirQuorum {
    /// Stage an initial `(t, n)` quorum with `active_leaves in 1..=64` active XMSS leaves.
    pub fn stage(
        ceremony_seed: [u8; 32],
        t: usize,
        n: usize,
        active_leaves: usize,
    ) -> Result<Self, HemQuorumError> {
        if t < 2 || t > n || n >= MAX_HEM_QUORUM_PARTIES {
            return Err(HemQuorumError::InvalidQuorum { t, n });
        }
        if active_leaves == 0 || active_leaves > HEM_JORTS_MAX_LEAVES {
            return Err(HemQuorumError::InvalidActiveLeaves { active_leaves });
        }

        let eval_points = canonical_eval_points(n);
        validate_all_eval_points_goldilocks(&eval_points).map_err(Poseidon2MpcError::Preprocess)?;

        let mut rng = PartyPrivateRng::from_seed(
            cshake256_32(b"QSAG.HEM.QSB.RNG/v1", &ceremony_seed),
            b"QSAG.HEM.QSB.RNG.STREAM/v1",
        );
        let dkg_pk_seed = cshake256_32(b"QSAG.HEM.QSB.PKSEED/v1", &ceremony_seed);
        let mut sk_seed_bytes = cshake256_32(b"QSAG.HEM.QSB.SKSEED/v1", &ceremony_seed);
        let mut sk_prf_bytes = cshake256_32(b"QSAG.HEM.QSB.SKPRF/v1", &ceremony_seed);

        let pk_seed = hem_pk_seed_from_bytes32(&dkg_pk_seed);
        let mut sk_seed =
            hem_expand_secret_bytes32_clear(&sk_seed_bytes, pk_seed, HEM_DOMAIN_SK_SEED_EXPAND);
        let mut sk_prf =
            hem_expand_secret_bytes32_clear(&sk_prf_bytes, pk_seed, HEM_DOMAIN_SK_PRF_EXPAND);
        wipe_bytes32(&mut sk_seed_bytes);
        wipe_bytes32(&mut sk_prf_bytes);

        let mut alpha = rng.next_ext2();
        if alpha == GoldilocksExt2::ZERO {
            alpha = GoldilocksExt2::new(Goldilocks::ONE, Goldilocks::TWO);
        }
        let alpha_shares = shamir_share_ext2(t, &eval_points, alpha, &mut rng);

        let mut leaves = Vec::with_capacity(HEM_JORTS_MAX_LEAVES);
        let mut endpoints = Vec::with_capacity(active_leaves);
        let mut prf_commits = Vec::with_capacity(active_leaves);
        let mut per_party_vals: Vec<Vec<Vec<Goldilocks>>> =
            (0..n).map(|_| Vec::with_capacity(active_leaves)).collect();
        let mut per_party_macs: Vec<Vec<Vec<GoldilocksExt2>>> =
            (0..n).map(|_| Vec::with_capacity(active_leaves)).collect();

        for kp in 0..active_leaves {
            let mut clear_scalars = Vec::with_capacity(HEM_LEAF_SCALARS);
            let mut prf_sec = derive_leaf_prf_secret_clear(sk_prf, pk_seed, kp as u32);
            prf_commits.push(hem_prf_check_digest_clear(prf_sec, pk_seed));
            clear_scalars.extend_from_slice(&prf_sec);
            wipe_goldilocks(&mut prf_sec);

            let mut kp_endpoints = [[Goldilocks::ZERO; 4]; HEM_WOTS_CHAINS];
            for (r, ep_slot) in kp_endpoints.iter_mut().enumerate().take(HEM_WOTS_CHAINS) {
                let y0 = hem_wots_base_secret_clear(sk_seed, pk_seed, 0, 0, kp as u32, r as u32);
                let y1 = hem_wots_step_hash_injective(pk_seed, y0, 0, 0, kp as u32, r as u32, 0);
                let y2 = hem_wots_step_hash_injective(pk_seed, y1, 0, 0, kp as u32, r as u32, 1);
                let y3 = hem_wots_step_hash_injective(pk_seed, y2, 0, 0, kp as u32, r as u32, 2);
                *ep_slot = y3;
                clear_scalars.extend_from_slice(&y0);
                clear_scalars.extend_from_slice(&y1);
                clear_scalars.extend_from_slice(&y2);
            }

            let mut kp_vals_p = vec![Vec::with_capacity(HEM_LEAF_SCALARS); n];
            let mut kp_macs_p = vec![Vec::with_capacity(HEM_LEAF_SCALARS); n];
            for &s in &clear_scalars {
                let v_sh = shamir_share_goldilocks(t, &eval_points, s, &mut rng);
                let m_sh = shamir_share_ext2(t, &eval_points, alpha.mul_base(s), &mut rng);
                for p in 0..n {
                    kp_vals_p[p].push(v_sh[p]);
                    kp_macs_p[p].push(m_sh[p]);
                }
            }
            wipe_goldilocks(&mut clear_scalars);
            for p in 0..n {
                per_party_vals[p].push(core::mem::take(&mut kp_vals_p[p]));
                per_party_macs[p].push(core::mem::take(&mut kp_macs_p[p]));
            }

            leaves.push(hem_compress_wots_endpoints_sponge(
                pk_seed,
                0,
                0,
                kp as u32,
                &kp_endpoints,
            ));
            endpoints.push(kp_endpoints);
        }
        wipe_goldilocks(&mut sk_seed);
        wipe_goldilocks(&mut sk_prf);
        wipe_ext2(core::slice::from_mut(&mut alpha));

        for kp in active_leaves..HEM_JORTS_MAX_LEAVES {
            leaves.push(hem_unassigned_leaf_digest(pk_seed, kp as u32));
        }
        let pk_root = hem_merkle_root_from_leaves(pk_seed, &leaves)
            .ok_or(HemQuorumError::InvalidActiveLeaves { active_leaves })?;

        let mut latch_rngs: Vec<PartyPrivateRng> = (0..n)
            .map(|p| PartyPrivateRng::from_seed(rng.next_bytes32(), &(p as u32).to_le_bytes()))
            .collect();
        let latch_cluster = HemEpochLatchCluster::establish(n, t, 0, &mut latch_rngs)?;

        let shares = (0..n)
            .map(|p| HemShamirCustodianShare {
                party_id: p,
                quorum_epoch: 0,
                t,
                n,
                eval_point: eval_points[p],
                high_water_leaf: 0,
                active_leaves,
                invalidated: false,
                alpha_share: alpha_shares[p],
                leaf_vals: core::mem::take(&mut per_party_vals[p]),
                leaf_macs: core::mem::take(&mut per_party_macs[p]),
            })
            .collect();

        let public_dir = HemQuorumPublicDirectory {
            dkg_pk_seed,
            pk: HemJortsPublicKey { pk_seed, pk_root },
            active_leaves,
            leaves,
            endpoints,
            prf_commits,
        };

        Ok(Self {
            quorum_epoch: 0,
            t,
            n,
            high_water_leaf: 0,
            public_dir,
            latch_cluster,
            shares,
        })
    }

    #[inline]
    pub fn quorum_epoch(&self) -> u64 {
        self.quorum_epoch
    }

    #[inline]
    pub fn threshold_and_size(&self) -> (usize, usize) {
        (self.t, self.n)
    }

    #[inline]
    pub fn high_water_leaf(&self) -> usize {
        self.high_water_leaf
    }

    #[inline]
    pub fn public_key(&self) -> HemJortsPublicKey {
        self.public_dir.pk
    }

    #[inline]
    pub fn public_directory(&self) -> &HemQuorumPublicDirectory {
        &self.public_dir
    }

    #[inline]
    pub fn custodian_shares(&self) -> &[HemShamirCustodianShare] {
        &self.shares
    }

    #[inline]
    pub fn latch_authority(&self) -> &HemEpochLatchAuthority {
        self.latch_cluster.authority_public()
    }

    /// Reconstruct a `HemDynamicShamirQuorum` from persisted [`HemQuorumPublicDirectory`] and
    /// `n` [`HemShamirCustodianShare`]s (used by CLI vault subcommands).
    pub fn from_persisted_shares(
        public_dir: HemQuorumPublicDirectory,
        shares: Vec<HemShamirCustodianShare>,
        latch_seed: [u8; 32],
    ) -> Result<Self, HemQuorumError> {
        if !public_dir.verify_consistency() || shares.is_empty() {
            return Err(HemQuorumError::MalformedVaultBytes);
        }
        let t = shares[0].t;
        let n = shares[0].n;
        let quorum_epoch = shares[0].quorum_epoch;
        let high_water_leaf = shares[0].high_water_leaf;
        if shares.len() != n || t < 2 || t > n {
            return Err(HemQuorumError::InvalidQuorum { t, n });
        }
        let eval_points = canonical_eval_points(n);
        for (p, sh) in shares.iter().enumerate() {
            if sh.invalidated {
                return Err(HemQuorumError::ShareInvalidated { party: p });
            }
            if sh.party_id != p
                || sh.t != t
                || sh.n != n
                || sh.eval_point != eval_points[p]
                || sh.active_leaves != public_dir.active_leaves
                || sh.high_water_leaf != high_water_leaf
            {
                return Err(HemQuorumError::MalformedVaultBytes);
            }
            if sh.quorum_epoch != quorum_epoch {
                return Err(HemQuorumError::QuorumEpochMismatch {
                    expected: quorum_epoch,
                    got: sh.quorum_epoch,
                    party: p,
                });
            }
        }
        let mut latch_rngs: Vec<PartyPrivateRng> = (0..n)
            .map(|p| {
                PartyPrivateRng::from_seed(
                    cshake256_32(
                        b"QSAG.HEM.QSB.LATCH.RESTORE/v1",
                        &encode_multi_frame(&[
                            &latch_seed,
                            &quorum_epoch.to_le_bytes(),
                            &(p as u32).to_le_bytes(),
                        ]),
                    ),
                    b"QSAG.HEM.QSB.LATCH.RESTORE.STREAM/v1",
                )
            })
            .collect();
        let latch_cluster =
            HemEpochLatchCluster::establish(n, t, high_water_leaf as u64, &mut latch_rngs)?;
        Ok(Self {
            quorum_epoch,
            t,
            n,
            high_water_leaf,
            public_dir,
            latch_cluster,
            shares,
        })
    }

    /// Certify the next monotone leaf in the `QuorumEpochLatchCluster` and sign `msg` using
    /// `signer_indices` (`>= t` custodians), returning `(leaf_epoch, HemJortsSignature)`.
    ///
    /// This is [`Self::reserve_leaf`] followed by [`Self::sign_reserved`] with nothing
    /// persisted in between: the burn is in memory only. A caller that keeps the quorum on
    /// disk should call the two halves itself and persist the quorum between them.
    ///
    /// Errors returned before the latch certifies (bad signer or acker sets, exhausted key,
    /// too few ackers) change nothing. Once the latch has certified a leaf, that leaf is
    /// burned in every custodian share even if signing then fails; compare
    /// [`Self::high_water_leaf`] before and after to see whether an error consumed one.
    pub fn sign_quorum(
        &mut self,
        signer_indices: &[usize],
        latch_ackers: &[usize],
        msg: &[u8],
    ) -> Result<(u64, HemJortsSignature), HemQuorumError> {
        let reserved = self.reserve_leaf(signer_indices, latch_ackers, msg)?;
        self.sign_reserved(reserved, msg)
    }

    /// First half of signing: certify the next leaf for `msg` and take it out of the quorum.
    ///
    /// On success the leaf is burned in every custodian share (so [`Self::custodian_shares`]
    /// and their vault bytes no longer contain it) and the high-water mark is past it. The
    /// signers' material for that one leaf lives only in the returned [`HemReservedLeaf`].
    /// Persist the quorum now, then call [`Self::sign_reserved`]: a crash in between loses
    /// the leaf but can never leave it available for a second message.
    ///
    /// Errors change nothing, except [`HemQuorumError::LeafExhausted`] after the latch has
    /// certified a leaf beyond the active range, which burns the remaining leaves.
    pub fn reserve_leaf(
        &mut self,
        signer_indices: &[usize],
        latch_ackers: &[usize],
        msg: &[u8],
    ) -> Result<HemReservedLeaf, HemQuorumError> {
        validate_party_subset(signer_indices, self.t, self.n)?;
        validate_party_subset(latch_ackers, 1, self.n)?;
        let active_leaves = self.public_dir.active_leaves;
        if self.high_water_leaf >= active_leaves {
            return Err(HemQuorumError::LeafExhausted);
        }
        for &p in signer_indices {
            if self.shares[p].invalidated {
                return Err(HemQuorumError::ShareInvalidated { party: p });
            }
            if self.shares[p].quorum_epoch != self.quorum_epoch {
                return Err(HemQuorumError::QuorumEpochMismatch {
                    expected: self.quorum_epoch,
                    got: self.shares[p].quorum_epoch,
                    party: p,
                });
            }
        }

        let (mu_bytes, _) = hem_compute_message_mu(&self.public_dir.pk, msg);
        let latch_pk = self
            .public_dir
            .pk
            .latch_pq_public_key(self.public_dir.dkg_pk_seed);
        self.latch_cluster.raise_floor(self.high_water_leaf as u64);
        let cert = self
            .latch_cluster
            .certify_epoch(
                latch_ackers,
                &latch_pk,
                HEM_JORTS_XMSS_HEIGHT as u32,
                &mu_bytes,
            )
            .map_err(|_| HemQuorumError::LatchRefused)?;

        // The latch quorum has now bound this leaf to `msg`. From here the leaf is spent
        // whether or not a signature ever comes out.
        let leaf = usize::try_from(cert.epoch())
            .ok()
            .filter(|&kp| kp < active_leaves);
        let Some(kp) = leaf else {
            self.high_water_leaf = active_leaves;
            for sh in &mut self.shares {
                sh.burn_leaves_below(active_leaves);
            }
            return Err(HemQuorumError::LeafExhausted);
        };

        let mut signer_shares = Vec::with_capacity(signer_indices.len());
        for &p in signer_indices {
            let sh = &mut self.shares[p];
            let mut leaf_vals = vec![Vec::new(); active_leaves];
            let mut leaf_macs = vec![Vec::new(); active_leaves];
            leaf_vals[kp] = core::mem::take(&mut sh.leaf_vals[kp]);
            leaf_macs[kp] = core::mem::take(&mut sh.leaf_macs[kp]);
            signer_shares.push(HemShamirCustodianShare {
                party_id: sh.party_id,
                quorum_epoch: sh.quorum_epoch,
                t: sh.t,
                n: sh.n,
                eval_point: sh.eval_point,
                high_water_leaf: kp,
                active_leaves,
                invalidated: false,
                alpha_share: GoldilocksExt2::ZERO,
                leaf_vals,
                leaf_macs,
            });
        }
        self.high_water_leaf = kp + 1;
        for sh in &mut self.shares {
            sh.burn_leaves_below(self.high_water_leaf);
        }
        Ok(HemReservedLeaf {
            cert,
            signer_shares,
        })
    }

    /// Second half of signing: produce the signature for the leaf taken by
    /// [`Self::reserve_leaf`]. `msg` must be the reserved message; the latch certificate binds
    /// it, so any other message is refused with [`HemQuorumError::LatchRefused`]. The
    /// reservation is consumed and wiped whether or not signing succeeds.
    pub fn sign_reserved(
        &self,
        reserved: HemReservedLeaf,
        msg: &[u8],
    ) -> Result<(u64, HemJortsSignature), HemQuorumError> {
        let signer_refs: Vec<&HemShamirCustodianShare> = reserved.signer_shares.iter().collect();
        let sig = sign_from_shamir_share_slice(
            &self.public_dir,
            self.latch_cluster.authority_public(),
            self.quorum_epoch,
            self.t,
            self.n,
            &reserved.cert,
            msg,
            &signer_refs,
        )?;
        Ok((reserved.cert.epoch(), sig))
    }

    /// Proactive share refresh (`Π_refresh`): adds fresh zero-constant degree-`< t` polynomials to
    /// all unspent leaf shares, MAC shares, and `alpha_share`, verifies Round-1 commitments,
    /// HVZK degree `< t`, and SPDZ `MacCheck`, bumps `quorum_epoch`, and preserves the exact
    /// 65-byte validator public key.
    /// `party_rngs` contains one independently seeded, private, evolving RNG per current
    /// custodian, in roster order. Session IDs alone provide no secret entropy.
    /// After a custodian compromise, reseed its RNG from fresh private entropy before refresh.
    pub fn proactive_refresh(
        &mut self,
        session_id: [u8; 32],
        party_rngs: &mut [PartyPrivateRng],
    ) -> Result<(), HemQuorumError> {
        check_randomness_count(party_rngs, self.n)?;
        let all_parties: Vec<usize> = (0..self.n).collect();
        let mut old_rngs =
            private_operation_rngs(&session_id, b"QSAG.HEM.QSB.REFRESH.OLD/v2", party_rngs);
        let mut new_rngs =
            private_operation_rngs(&session_id, b"QSAG.HEM.QSB.REFRESH.NEW/v2", party_rngs);
        self.reshare_quorum_with_fault(
            session_id,
            &all_parties[..self.t],
            self.t,
            self.n,
            &mut old_rngs,
            &mut new_rngs,
            ReshareFaultInjection::None,
        )
    }

    /// Dynamic `(t, n) -> (t', n')` quorum-switching (`Π_reshare`): transitions custody from
    /// `old_quorum_indices` (`>= t` custodians) to a fresh `(new_t, new_n)` threshold and roster
    /// WITHOUT changing the validator's 65-byte [`HemJortsPublicKey`].
    /// Supply independently seeded private RNGs for every old and new custodian in roster
    /// order (lengths `self.n` and `new_n`); no public or common reconstruction seed.
    pub fn reshare_quorum(
        &mut self,
        session_id: [u8; 32],
        old_quorum_indices: &[usize],
        new_t: usize,
        new_n: usize,
        old_party_rngs: &mut [PartyPrivateRng],
        new_party_rngs: &mut [PartyPrivateRng],
    ) -> Result<(), HemQuorumError> {
        self.reshare_quorum_with_fault(
            session_id,
            old_quorum_indices,
            new_t,
            new_n,
            old_party_rngs,
            new_party_rngs,
            ReshareFaultInjection::None,
        )
    }

    /// Fault-injectable entry point for adversarial verification of `Π_reshare` / `Π_refresh`.
    #[expect(
        clippy::too_many_arguments,
        reason = "explicit private custodian randomness and protocol inputs"
    )]
    pub fn reshare_quorum_with_fault(
        &mut self,
        session_id: [u8; 32],
        old_quorum_indices: &[usize],
        new_t: usize,
        new_n: usize,
        old_party_rngs: &mut [PartyPrivateRng],
        new_party_rngs: &mut [PartyPrivateRng],
        fault: ReshareFaultInjection,
    ) -> Result<(), HemQuorumError> {
        if new_t < 2 || new_t > new_n || new_n >= MAX_HEM_QUORUM_PARTIES {
            return Err(HemQuorumError::InvalidQuorum { t: new_t, n: new_n });
        }
        check_randomness_count(old_party_rngs, self.n)?;
        check_randomness_count(new_party_rngs, new_n)?;
        validate_party_subset(old_quorum_indices, self.t, self.n)?;
        let active_old = &old_quorum_indices[..self.t];
        for &p in active_old {
            if self.shares[p].invalidated {
                return Err(HemQuorumError::ShareInvalidated { party: p });
            }
            if self.shares[p].quorum_epoch != self.quorum_epoch {
                return Err(HemQuorumError::QuorumEpochMismatch {
                    expected: self.quorum_epoch,
                    got: self.shares[p].quorum_epoch,
                    party: p,
                });
            }
        }

        let old_pts: Vec<Goldilocks> = active_old
            .iter()
            .map(|&p| self.shares[p].eval_point)
            .collect();
        let lambdas =
            lagrange_weights_zero_goldilocks(&old_pts).ok_or(HemQuorumError::InvalidQuorum {
                t: self.t,
                n: self.n,
            })?;
        let new_pts = canonical_eval_points(new_n);
        validate_all_eval_points_goldilocks(&new_pts).map_err(Poseidon2MpcError::Preprocess)?;

        let unspent_leaves = self
            .public_dir
            .active_leaves
            .saturating_sub(self.high_water_leaf);
        let total_scalars = unspent_leaves * HEM_LEAF_SCALARS;

        // Round 1: Each old custodian `d_slot` deals weighted degree-`< new_t` sub-shares + HVZK
        // blinding evaluations `mask_eval` to `0..new_n` and broadcasts Poseidon2 commitments.
        let mut sub_alpha = SecretBuffer(vec![vec![GoldilocksExt2::ZERO; new_n]; self.t]);
        let mut sub_mask = SecretBuffer(vec![vec![GoldilocksExt2::ZERO; new_n]; self.t]);
        let mut sub_vals = SecretBuffer(vec![
            vec![vec![Goldilocks::ZERO; total_scalars]; new_n];
            self.t
        ]);
        let mut sub_macs = SecretBuffer(vec![
            vec![vec![GoldilocksExt2::ZERO; total_scalars]; new_n];
            self.t
        ]);
        let mut round1_commits = vec![vec![[0u8; 32]; new_n]; self.t];

        for (d_slot, &old_p) in active_old.iter().enumerate() {
            let lam = lambdas[d_slot];
            let mut d_rng = private_operation_rng(
                &session_id,
                b"QSAG.HEM.QSB.DEALER/v2",
                old_p,
                &mut old_party_rngs[old_p],
            );

            // Preserve `alpha` across reshare (`sum_i lam_i * alpha_share_i == alpha`) with fresh polynomial
            let weighted_alpha = SecretBuffer(self.shares[old_p].alpha_share.mul_base(lam));
            sub_alpha[d_slot] = shamir_share_ext2(new_t, &new_pts, *weighted_alpha, &mut d_rng);

            let mask_secret = SecretBuffer(d_rng.next_ext2());
            sub_mask[d_slot] = shamir_share_ext2(new_t, &new_pts, *mask_secret, &mut d_rng);

            let mut flat_idx = 0usize;
            for kp in self.high_water_leaf..self.public_dir.active_leaves {
                for s_idx in 0..HEM_LEAF_SCALARS {
                    let mut w_val = SecretBuffer(lam * self.shares[old_p].leaf_vals[kp][s_idx]);
                    if matches!(fault, ReshareFaultInjection::ShiftConstantTerm { dealer } if dealer == d_slot)
                        && flat_idx == 0
                    {
                        *w_val += Goldilocks::ONE;
                    }
                    let w_mac = SecretBuffer(self.shares[old_p].leaf_macs[kp][s_idx].mul_base(lam));
                    let v_poly =
                        SecretBuffer(shamir_share_goldilocks(new_t, &new_pts, *w_val, &mut d_rng));
                    let m_poly =
                        SecretBuffer(shamir_share_ext2(new_t, &new_pts, *w_mac, &mut d_rng));
                    for j in 0..new_n {
                        sub_vals[d_slot][j][flat_idx] = v_poly[j];
                        sub_macs[d_slot][j][flat_idx] = m_poly[j];
                    }
                    flat_idx += 1;
                }
            }

            if matches!(fault, ReshareFaultInjection::CorruptPolynomialDegree { dealer } if dealer == d_slot)
                && new_n > new_t
                && total_scalars > 0
            {
                sub_vals[d_slot][new_n - 1][0] += Goldilocks::from_u64_reduced(7);
            }

            for j in 0..new_n {
                round1_commits[d_slot][j] = hash_subshare_packet_commitment(
                    &session_id,
                    old_p,
                    j,
                    sub_alpha[d_slot][j],
                    sub_mask[d_slot][j],
                    &sub_vals[d_slot][j],
                    &sub_macs[d_slot][j],
                );
            }

            if let ReshareFaultInjection::TamperInTransit { dealer, recipient } = fault
                && dealer == d_slot
                && recipient < new_n
                && total_scalars > 0
            {
                sub_vals[d_slot][recipient][0] += Goldilocks::ONE;
            }
        }

        // Round 2A: Every new custodian `j` verifies all Round-1 Poseidon2 sub-share commitments.
        let mut transcript_commit_bytes = Vec::with_capacity(32 + self.t * new_n * 32);
        transcript_commit_bytes.extend_from_slice(&session_id);
        for (d_slot, &old_p) in active_old.iter().enumerate() {
            for j in 0..new_n {
                let recomputed = hash_subshare_packet_commitment(
                    &session_id,
                    old_p,
                    j,
                    sub_alpha[d_slot][j],
                    sub_mask[d_slot][j],
                    &sub_vals[d_slot][j],
                    &sub_macs[d_slot][j],
                );
                if !ct_eq_bytes32(&recomputed, &round1_commits[d_slot][j]) {
                    return Err(HemQuorumError::CommitmentMismatch {
                        dealer: old_p,
                        recipient: j,
                    });
                }
                transcript_commit_bytes.extend_from_slice(&round1_commits[d_slot][j]);
            }
        }

        // Round 2B: HVZK Linear Degree-`< new_t` Verification over `GoldilocksExt2`
        let chal_seed = cshake256_32(HEM_QSB_CHALLENGE_TAG, &transcript_commit_bytes);
        let mut chal_rng = PartyPrivateRng::from_seed(chal_seed, b"QSAG.HEM.QSB.CHAL.STREAM/v1");
        let chi_alpha = chal_rng.next_ext2();
        let mut chi_vals = Vec::with_capacity(total_scalars);
        let mut chi_macs = Vec::with_capacity(total_scalars);
        for _ in 0..total_scalars {
            chi_vals.push(chal_rng.next_ext2());
            chi_macs.push(chal_rng.next_ext2());
        }

        for (d_slot, &old_p) in active_old.iter().enumerate() {
            let mut z_evals = SecretBuffer(Vec::with_capacity(new_n));
            for j in 0..new_n {
                let mut acc = sub_mask[d_slot][j] + chi_alpha * sub_alpha[d_slot][j];
                for k in 0..total_scalars {
                    acc += chi_vals[k].mul_base(sub_vals[d_slot][j][k]);
                    acc += chi_macs[k] * sub_macs[d_slot][j][k];
                }
                z_evals.push(acc);
            }
            if open_and_check_degree_ext2(new_t, &new_pts, &z_evals, "hem_qsb_reshare_deg").is_err()
            {
                return Err(HemQuorumError::DegreeCheckFailed { dealer: old_p });
            }
        }

        // Assemble candidate `(new_t, new_n)` shares across `0..new_n`
        let mut new_alpha_shares = SecretBuffer(vec![GoldilocksExt2::ZERO; new_n]);
        let mut new_flat_vals = SecretBuffer(vec![vec![Goldilocks::ZERO; total_scalars]; new_n]);
        let mut new_flat_macs =
            SecretBuffer(vec![vec![GoldilocksExt2::ZERO; total_scalars]; new_n]);
        for d_slot in 0..self.t {
            for j in 0..new_n {
                new_alpha_shares[j] += sub_alpha[d_slot][j];
                for k in 0..total_scalars {
                    new_flat_vals[j][k] += sub_vals[d_slot][j][k];
                    new_flat_macs[j][k] += sub_macs[d_slot][j][k];
                }
                wipe_goldilocks(&mut sub_vals[d_slot][j]);
                wipe_ext2(&mut sub_macs[d_slot][j]);
            }
            wipe_ext2(&mut sub_alpha[d_slot]);
            wipe_ext2(&mut sub_mask[d_slot]);
        }

        // Round 2C: SPDZ Constant-Term Preservation `MacCheck` over `GoldilocksExt2`!
        // Checks `\sum_k gamma_k * (alpha * val'_k - mac'_k) == 0` via zero-masked Shamir opening.
        // Round 2B already proved all `0..new_n` shares lie on unique degree-`< new_t` polynomials,
        // so `check_quorum = (2 * new_t).min(new_n)` contains at least one honest custodian under any
        // `< new_t` corruption while keeping Ring-LWE Base-OT setup `O(new_t^2)` up to `new_n = 256`.
        if total_scalars > 0 {
            let check_quorum = (2 * new_t).min(new_n);
            let check_pts = &new_pts[..check_quorum];
            let check_lambdas = lagrange_weights_zero_goldilocks(&check_pts[..new_t])
                .ok_or(HemQuorumError::InvalidQuorum { t: new_t, n: new_n })?;
            let alpha_contribs = SecretBuffer(
                (0..check_quorum)
                    .map(|j| {
                        if j < new_t {
                            new_alpha_shares[j].mul_base(check_lambdas[j])
                        } else {
                            GoldilocksExt2::ZERO
                        }
                    })
                    .collect::<Vec<GoldilocksExt2>>(),
            );

            let mut check_rngs = private_operation_rngs(
                &session_id,
                b"QSAG.HEM.QSB.MACCHK/v2",
                &mut new_party_rngs[..check_quorum],
            );
            let mut mesh = OtMesh::establish(
                cshake256_32(b"QSAG.HEM.QSB.MACCHK.OT/v1", &session_id),
                &mut check_rngs,
            )
            .map_err(Poseidon2MpcError::Preprocess)?;
            // Generate 1 random scalar `r = sum_j r_j` and authenticate it under `alpha` via Gilboa OLE!
            let r_inputs = SecretBuffer(
                (0..check_quorum)
                    .map(|j| {
                        let rj = check_rngs[j].next_goldilocks();
                        shamir_share_goldilocks(new_t, check_pts, rj, &mut check_rngs[j])
                    })
                    .collect::<Vec<Vec<Goldilocks>>>(),
            );
            let mut r_sh = SecretBuffer(vec![Goldilocks::ZERO; check_quorum]);
            for r_row in r_inputs.iter() {
                for j in 0..check_quorum {
                    r_sh[j] += r_row[j];
                }
            }
            let r_batch = SecretBuffer(r_sh.iter().map(|&x| vec![x]).collect::<Vec<Vec<_>>>());
            let r_macs = SecretBuffer(
                qsag_core::preprocessing::spdz_authenticate_goldilocks_batch_ext2(
                    &cshake256_32(b"QSAG.HEM.QSB.MACCHK.AUTH/v1", &session_id),
                    new_t,
                    check_pts,
                    &mut mesh,
                    &alpha_contribs,
                    &new_alpha_shares[..check_quorum],
                    &r_batch,
                    &mut check_rngs,
                )
                .map_err(|_| HemQuorumError::ReshareMacCheckFailed)?,
            );

            // Squeeze `total_scalars` base-field weights `beta_k` and open ONLY the single masked
            // scalar `U = r + sum_k beta_k * val'_k` behind `commit_and_open_spdz_goldilocks_batch_quorum`!
            let mut betas = Vec::with_capacity(total_scalars);
            for _ in 0..total_scalars {
                betas.push(chal_rng.next_goldilocks());
            }
            let mut masked_sh = SecretBuffer(vec![vec![Goldilocks::ZERO; 1]; check_quorum]);
            let mut masked_mac = SecretBuffer(vec![vec![GoldilocksExt2::ZERO; 1]; check_quorum]);
            for j in 0..check_quorum {
                let mut v_acc = r_sh[j];
                let mut m_acc = r_macs[j][0];
                for k in 0..total_scalars {
                    v_acc += betas[k] * new_flat_vals[j][k];
                    m_acc += new_flat_macs[j][k].mul_base(betas[k]);
                }
                masked_sh[j][0] = v_acc;
                masked_mac[j][0] = m_acc;
            }
            let opened_res = commit_and_open_spdz_goldilocks_batch_quorum(
                &session_id,
                "hem_qsb_reshare_const_mac_check",
                new_t,
                check_pts,
                &masked_sh,
                &masked_mac,
                &new_alpha_shares[..check_quorum],
                &mut check_rngs,
            );
            match opened_res {
                Ok(mut u_vec) => wipe_goldilocks(&mut u_vec),
                Err(_) => return Err(HemQuorumError::ReshareMacCheckFailed),
            }
        }

        // Every check passed. Build the complete new custody first; nothing below can
        // fail once the old shares start being retired.
        let next_quorum_epoch = self.quorum_epoch + 1;
        let hw = self.high_water_leaf;
        let active_leaves = self.public_dir.active_leaves;

        let mut new_shares = Vec::with_capacity(new_n);
        for j in 0..new_n {
            let mut leaf_vals = vec![Vec::new(); active_leaves];
            let mut leaf_macs = vec![Vec::new(); active_leaves];
            let mut flat_idx = 0usize;
            for kp in hw..active_leaves {
                leaf_vals[kp] = new_flat_vals[j][flat_idx..flat_idx + HEM_LEAF_SCALARS].to_vec();
                leaf_macs[kp] = new_flat_macs[j][flat_idx..flat_idx + HEM_LEAF_SCALARS].to_vec();
                flat_idx += HEM_LEAF_SCALARS;
            }
            wipe_goldilocks(&mut new_flat_vals[j]);
            wipe_ext2(&mut new_flat_macs[j]);

            new_shares.push(HemShamirCustodianShare {
                party_id: j,
                quorum_epoch: next_quorum_epoch,
                t: new_t,
                n: new_n,
                eval_point: new_pts[j],
                high_water_leaf: hw,
                active_leaves,
                invalidated: false,
                alpha_share: new_alpha_shares[j],
                leaf_vals,
                leaf_macs,
            });
        }
        wipe_ext2(&mut new_alpha_shares);

        let mut latch_rngs =
            private_operation_rngs(&session_id, b"QSAG.HEM.QSB.NEW.LATCH/v2", new_party_rngs);
        // On error `new_shares` is dropped (and wiped) with the old custody untouched.
        let new_cluster =
            HemEpochLatchCluster::establish(new_n, new_t, hw as u64, &mut latch_rngs)?;

        // Commit: retire the old `(t, n)` custody and install the new one.
        for old_sh in &mut self.shares {
            old_sh.invalidate_and_wipe();
        }
        self.quorum_epoch = next_quorum_epoch;
        self.t = new_t;
        self.n = new_n;
        self.latch_cluster = new_cluster;
        self.shares = new_shares;
        Ok(())
    }
}

/// Sign `msg` directly from a slice of detached [`HemShamirCustodianShare`]s and an
/// [`EpochLatchCertificate`] (used both internally and by adversarial negative tests).
#[expect(
    clippy::too_many_arguments,
    reason = "Detached signing binds directory, latch authority, quorum epoch, threshold, committee size, certificate, message and share slice"
)]
pub fn sign_from_shamir_share_slice(
    public_dir: &HemQuorumPublicDirectory,
    latch_authority: &HemEpochLatchAuthority,
    expected_quorum_epoch: u64,
    t: usize,
    n: usize,
    latch_cert: &HemEpochLatchCertificate,
    msg: &[u8],
    signer_shares: &[&HemShamirCustodianShare],
) -> Result<HemJortsSignature, HemQuorumError> {
    if t < 2 || t > n {
        return Err(HemQuorumError::InvalidQuorum { t, n });
    }
    if signer_shares.len() < t {
        return Err(HemQuorumError::NotEnoughSigners {
            have: signer_shares.len(),
            need: t,
        });
    }
    let mut seen = Vec::with_capacity(signer_shares.len());
    let mut pts = Vec::with_capacity(signer_shares.len());
    for sh in signer_shares {
        if sh.invalidated {
            return Err(HemQuorumError::ShareInvalidated { party: sh.party_id });
        }
        if sh.quorum_epoch != expected_quorum_epoch {
            return Err(HemQuorumError::QuorumEpochMismatch {
                expected: expected_quorum_epoch,
                got: sh.quorum_epoch,
                party: sh.party_id,
            });
        }
        if sh.t != t || sh.n != n || sh.party_id >= n {
            return Err(HemQuorumError::InvalidQuorum { t: sh.t, n: sh.n });
        }
        if seen.contains(&sh.party_id) {
            return Err(HemQuorumError::DuplicateParty { party: sh.party_id });
        }
        seen.push(sh.party_id);
        pts.push(sh.eval_point);
    }

    let (mu_bytes, mu) = hem_compute_message_mu(&public_dir.pk, msg);
    let latch_pk = public_dir.pk.latch_pq_public_key(public_dir.dkg_pk_seed);
    let binding = qsag_core::dkg::epoch_latch_binding(
        &latch_pk.pk_seed,
        &latch_pk.pk_root,
        latch_cert.epoch(),
        &mu_bytes,
    );
    latch_cert
        .verify_against(latch_authority, n, t, latch_cert.epoch(), &binding)
        .map_err(|_| HemQuorumError::LatchRefused)?;

    let kp = usize::try_from(latch_cert.epoch()).map_err(|_| HemQuorumError::LeafExhausted)?;
    if kp >= public_dir.active_leaves {
        return Err(HemQuorumError::LeafExhausted);
    }
    for sh in signer_shares {
        if kp < sh.high_water_leaf || sh.leaf_vals[kp].len() != HEM_LEAF_SCALARS {
            return Err(HemQuorumError::LeafExhausted);
        }
    }

    let mut prf_leaf = [Goldilocks::ZERO; 4];
    let mut share_buf = vec![Goldilocks::ZERO; signer_shares.len()];
    for (limb, out) in prf_leaf.iter_mut().enumerate() {
        for (i, sh) in signer_shares.iter().enumerate() {
            share_buf[i] = sh.leaf_vals[kp][limb];
        }
        *out = open_and_check_degree_goldilocks(t, &pts, &share_buf, "hem_qsb_open_prf")
            .map_err(|_| HemQuorumError::PrfCommitmentMismatch)?;
    }
    if hem_prf_check_digest_clear(prf_leaf, public_dir.pk.pk_seed) != public_dir.prf_commits[kp] {
        wipe_goldilocks(&mut prf_leaf);
        wipe_goldilocks(&mut share_buf);
        return Err(HemQuorumError::PrfCommitmentMismatch);
    }

    let r_rand = hem_derive_r_rand_clear(prf_leaf, public_dir.pk.pk_seed, mu, kp as u64);
    wipe_goldilocks(&mut prf_leaf);

    let (tsw_ctr, digits) = hem_grind_stateful_tsw_digits(
        public_dir.pk.pk_seed,
        public_dir.pk.pk_root,
        r_rand,
        mu,
        kp as u32,
        100_000,
    )
    .ok_or(HemQuorumError::TswGrindExhausted)?;

    let mut wots_chains = Vec::with_capacity(HEM_WOTS_CHAINS);
    for (r, &d) in digits.iter().enumerate().take(HEM_WOTS_CHAINS) {
        let d_usize = d as usize;
        if d_usize == HEM_WOTS_MAX_STEP {
            wots_chains.push(public_dir.endpoints[kp][r]);
        } else {
            let base = 4 + (r * HEM_WOTS_MAX_STEP + d_usize) * 4;
            let mut node = [Goldilocks::ZERO; 4];
            for (limb, out) in node.iter_mut().enumerate() {
                for (i, sh) in signer_shares.iter().enumerate() {
                    share_buf[i] = sh.leaf_vals[kp][base + limb];
                }
                *out = open_and_check_degree_goldilocks(t, &pts, &share_buf, "hem_qsb_open_chain")
                    .map_err(|_| HemQuorumError::EndpointVerificationFailed { chain: r })?;
            }
            let mut cur = node;
            for step in (d as u32)..(HEM_WOTS_MAX_STEP as u32) {
                cur = hem_wots_step_hash_injective(
                    public_dir.pk.pk_seed,
                    cur,
                    0,
                    0,
                    kp as u32,
                    r as u32,
                    step,
                );
            }
            if cur != public_dir.endpoints[kp][r] {
                wipe_goldilocks(&mut share_buf);
                return Err(HemQuorumError::EndpointVerificationFailed { chain: r });
            }
            wots_chains.push(node);
        }
    }
    wipe_goldilocks(&mut share_buf);

    let (merkle_path, _) = hem_merkle_auth_path(public_dir.pk.pk_seed, &public_dir.leaves, kp)
        .ok_or(HemQuorumError::SignatureSelfCheckFailed)?;
    let sig = HemJortsSignature {
        r_rand,
        stateful_leaf_idx: kp as u32,
        tsw_ctr,
        wots_chains,
        merkle_path,
    };
    if !verify_hem_jorts_signature(&public_dir.pk, msg, &sig) {
        return Err(HemQuorumError::SignatureSelfCheckFailed);
    }
    Ok(sig)
}

// ============================================================================
// 3. Seed-Level SPDZ MPC Coordinator (`HemSpdzSeedQuorum`)
// ============================================================================

/// 100% dealerless seed-level SPDZ MPC quorum (`run_dealerless_dkg_seed32_goldilocks`,
/// `run_dealerless_refresh_seed32_goldilocks`, `run_dealerless_reshare_seed32_goldilocks` +
/// native `[Goldilocks; 4]` SPDZ `sign_hem_jorts_poseidon2_mpc_cached`).
pub struct HemSpdzSeedQuorum {
    quorum_epoch: u64,
    t: usize,
    n: usize,
    high_water_leaf: u64,
    cache: HemJortsCachedTree,
    latch_cluster: HemEpochLatchCluster,
    durable_latch_authority: Option<EpochLatchAuthorityPublic>,
    sk_seed_shares: Vec<ShamirPoseidonSeedShare>,
    sk_prf_shares: Vec<ShamirPoseidonSeedShare>,
}

impl fmt::Debug for HemSpdzSeedQuorum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("HemSpdzSeedQuorum")
            .field("quorum_epoch", &self.quorum_epoch)
            .field("t", &self.t)
            .field("n", &self.n)
            .field("pk", &self.cache.pk)
            .finish_non_exhaustive()
    }
}

// Working copies for a refresh or reshare. The core protocols update or retire the
// slice they are given one sharing at a time; running them on copies lets the seed
// and PRF sharings be replaced together or not at all. Copies wipe on drop.
fn stage_seed_shares(shares: &[ShamirPoseidonSeedShare]) -> Vec<ShamirPoseidonSeedShare> {
    shares
        .iter()
        .map(|s| {
            ShamirPoseidonSeedShare::from_bit_shares(
                s.party_id,
                s.generation,
                s.eval_point,
                s.bit_shares,
            )
        })
        .collect()
}

impl HemSpdzSeedQuorum {
    /// Run a 100% dealerless Goldilocks DKG + native `[Goldilocks; 4]` SPDZ MPC key generation.
    /// Each custodian supplies its own independently seeded private RNG in roster order.
    /// `session_id` is public context and must never be used as the entropy source.
    pub fn keygen_dealerless(
        session_id: [u8; 32],
        t: usize,
        n: usize,
        active_leaves: usize,
        party_rngs: &mut [PartyPrivateRng],
    ) -> Result<Self, HemQuorumError> {
        Self::keygen_inner(session_id, t, n, active_leaves, party_rngs, false)
    }

    /// Online-protocol test constructor: runs real dealerless Goldilocks DKG, Gilboa byte-share
    /// authentication, and SPDZ MPC keygen while filling `pow7` correlations from the test fixture.
    #[cfg(any(test, feature = "testing-ephemeral"))]
    pub fn keygen_dealerless_online_fixture(
        session_id: [u8; 32],
        t: usize,
        n: usize,
        active_leaves: usize,
        party_rngs: &mut [PartyPrivateRng],
    ) -> Result<Self, HemQuorumError> {
        Self::keygen_inner(session_id, t, n, active_leaves, party_rngs, true)
    }

    fn keygen_inner(
        session_id: [u8; 32],
        t: usize,
        n: usize,
        active_leaves: usize,
        party_rngs: &mut [PartyPrivateRng],
        online_fixture: bool,
    ) -> Result<Self, HemQuorumError> {
        if t < 2 || t > n || n > 16 {
            return Err(HemQuorumError::InvalidQuorum { t, n });
        }
        check_randomness_count(party_rngs, n)?;
        let budget = required_hem_jorts_keygen_preprocessing_budget(active_leaves)?;
        let pts = canonical_eval_points(n);
        let mut rngs = private_operation_rngs(&session_id, b"QSAG.HEM.SPDZ.KEYGEN/v2", party_rngs);
        let mut mesh =
            OtMesh::establish(cshake256_32(b"QSAG.HEM.SPDZ.OT/v1", &session_id), &mut rngs)
                .map_err(Poseidon2MpcError::Preprocess)?;

        let (sk_seed_shares, pk_seed) = run_dealerless_dkg_seed32_goldilocks(
            cshake256_32(b"QSAG.HEM.SPDZ.DKG.SEED/v1", &session_id),
            t,
            &pts,
            &mut mesh,
            &mut rngs,
        )?;
        let (sk_prf_shares, _) = run_dealerless_dkg_seed32_goldilocks(
            cshake256_32(b"QSAG.HEM.SPDZ.DKG.PRF/v1", &session_id),
            t,
            &pts,
            &mut mesh,
            &mut rngs,
        )?;

        let prep_pow7 = if online_fixture { 0 } else { budget.0 };
        let (mut key_shares, mut vaults) = authenticate_poseidon_dkg_shares_and_preprocess(
            cshake256_32(b"QSAG.HEM.SPDZ.KEYGEN.PREP/v1", &session_id),
            t,
            &pts,
            pk_seed,
            &sk_seed_shares,
            &sk_prf_shares,
            prep_pow7,
            0,
            0,
            &mut mesh,
            &mut rngs,
        )?;
        #[cfg(any(test, feature = "testing-ephemeral"))]
        if online_fixture {
            qsag_core::preprocessing::PreprocessedPoseidonPartyVault::fill_quorum_online_fixture(
                t,
                &mut vaults,
                budget,
                &mut rngs[0],
            );
        }
        let cache = {
            let mut ks_refs: Vec<_> = key_shares[..t].iter_mut().collect();
            let mut v_refs: Vec<_> = vaults[..t].iter_mut().collect();
            build_distributed_hem_jorts_key_mpc_with_active_leaves(
                cshake256_32(b"QSAG.HEM.SPDZ.KEYGEN.ONLINE/v1", &session_id),
                active_leaves,
                t,
                &mut ks_refs,
                &mut v_refs,
                &mut rngs[..t],
            )?
        };
        let latch_cluster = HemEpochLatchCluster::establish(n, t, 0, &mut rngs)?;

        Ok(Self {
            quorum_epoch: 0,
            t,
            n,
            high_water_leaf: 0,
            cache,
            latch_cluster,
            durable_latch_authority: None,
            sk_seed_shares,
            sk_prf_shares,
        })
    }

    #[inline]
    pub fn public_key(&self) -> HemJortsPublicKey {
        self.cache.pk
    }

    #[inline]
    pub fn quorum_epoch(&self) -> u64 {
        self.quorum_epoch
    }

    /// First leaf that has not been certified for signing.
    #[inline]
    pub fn high_water_leaf(&self) -> u64 {
        self.high_water_leaf
    }

    /// Return the enrolled durable [`EpochLatchAuthorityPublic`], if any.
    #[inline]
    pub fn enrolled_durable_latch_authority(&self) -> Option<&EpochLatchAuthorityPublic> {
        self.durable_latch_authority.as_ref()
    }

    /// Pin a committee [`EpochLatchAuthorityPublic`] (from a durable `QuorumEpochLatchCluster`)
    /// so `t`-of-`n` (`t < n`) SPDZ signing can verify [`EpochLatchCertificate`]s.
    /// Re-enrolling the exact same authority is idempotent; enrolling a different authority or
    /// mismatched committee size fails closed with `CertificateCommitteeMismatch`.
    pub fn enroll_durable_latch_authority(
        &mut self,
        authority: EpochLatchAuthorityPublic,
    ) -> Result<(), HemQuorumError> {
        if authority.committee_size() != self.n {
            return Err(Poseidon2MpcError::LatchCertificateRejected(
                EpochLatchError::CertificateCommitteeMismatch,
            )
            .into());
        }
        match &self.durable_latch_authority {
            None => {
                self.durable_latch_authority = Some(authority);
                Ok(())
            }
            Some(existing) if *existing == authority => Ok(()),
            Some(_) => Err(Poseidon2MpcError::LatchCertificateRejected(
                EpochLatchError::CertificateCommitteeMismatch,
            )
            .into()),
        }
    }

    /// Compute the exact 32-byte [`epoch_latch_binding`] required when certifying `(epoch, msg)`
    /// through an external [`qsag_core::dkg::QuorumEpochLatchCluster`].
    pub fn epoch_latch_binding(&self, epoch: u64, msg: &[u8]) -> [u8; 32] {
        let (mu_bytes, _) = hem_compute_message_mu(&self.cache.pk, msg);
        let latch_pk = self.cache.pk.latch_pq_public_key(self.cache.dkg_pk_seed);
        epoch_latch_binding(&latch_pk.pk_seed, &latch_pk.pk_root, epoch, &mu_bytes)
    }

    /// Proactive bit-level refresh (`run_dealerless_refresh_seed32_goldilocks`) preserving `pk`.
    /// `party_rngs` contains one independently seeded, private, evolving RNG per current
    /// custodian, in roster order. Session IDs alone provide no secret entropy.
    /// After a custodian compromise, reseed its RNG from fresh private entropy before refresh.
    pub fn proactive_refresh(
        &mut self,
        session_id: [u8; 32],
        party_rngs: &mut [PartyPrivateRng],
    ) -> Result<(), HemQuorumError> {
        let pts = canonical_eval_points(self.n);
        check_randomness_count(party_rngs, self.n)?;
        let mut rngs = private_operation_rngs(&session_id, b"QSAG.HEM.SPDZ.REFRESH/v2", party_rngs);
        // Refresh both sharings on copies, then install them together: an error in
        // either leaves the quorum exactly as it was.
        let mut seed_shares = stage_seed_shares(&self.sk_seed_shares);
        let mut prf_shares = stage_seed_shares(&self.sk_prf_shares);
        run_dealerless_refresh_seed32_goldilocks(
            cshake256_32(b"QSAG.HEM.SPDZ.REF.SEED/v1", &session_id),
            self.t,
            &pts,
            &mut seed_shares,
            &mut rngs,
        )?;
        run_dealerless_refresh_seed32_goldilocks(
            cshake256_32(b"QSAG.HEM.SPDZ.REF.PRF/v1", &session_id),
            self.t,
            &pts,
            &mut prf_shares,
            &mut rngs,
        )?;
        self.sk_seed_shares = seed_shares;
        self.sk_prf_shares = prf_shares;
        self.quorum_epoch += 1;
        Ok(())
    }

    /// Dynamic `(t, n) -> (new_t, new_n)` seed resharing (`run_dealerless_reshare_seed32_goldilocks`)
    /// verified in SPDZ MPC via `verify_reshared_hem_jorts_key_mpc` without reconstructing secrets!
    /// Supply independently seeded private RNGs for every old and new custodian in roster
    /// order (lengths `self.n` and `new_n`); no public or common reconstruction seed.
    pub fn reshare_quorum(
        &mut self,
        session_id: [u8; 32],
        old_quorum_indices: &[usize],
        new_t: usize,
        new_n: usize,
        old_party_rngs: &mut [PartyPrivateRng],
        new_party_rngs: &mut [PartyPrivateRng],
    ) -> Result<(), HemQuorumError> {
        self.reshare_quorum_inner(
            session_id,
            old_quorum_indices,
            new_t,
            new_n,
            old_party_rngs,
            new_party_rngs,
            false,
        )
    }

    #[cfg(any(test, feature = "testing-ephemeral"))]
    pub fn reshare_quorum_online_fixture(
        &mut self,
        session_id: [u8; 32],
        old_quorum_indices: &[usize],
        new_t: usize,
        new_n: usize,
        old_party_rngs: &mut [PartyPrivateRng],
        new_party_rngs: &mut [PartyPrivateRng],
    ) -> Result<(), HemQuorumError> {
        self.reshare_quorum_inner(
            session_id,
            old_quorum_indices,
            new_t,
            new_n,
            old_party_rngs,
            new_party_rngs,
            true,
        )
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "explicit private custodian randomness and protocol inputs"
    )]
    fn reshare_quorum_inner(
        &mut self,
        session_id: [u8; 32],
        old_quorum_indices: &[usize],
        new_t: usize,
        new_n: usize,
        old_party_rngs: &mut [PartyPrivateRng],
        new_party_rngs: &mut [PartyPrivateRng],
        online_fixture: bool,
    ) -> Result<(), HemQuorumError> {
        if new_t < 2 || new_t > new_n || new_n > 16 {
            return Err(HemQuorumError::InvalidQuorum { t: new_t, n: new_n });
        }
        check_randomness_count(old_party_rngs, self.n)?;
        check_randomness_count(new_party_rngs, new_n)?;
        validate_party_subset(old_quorum_indices, self.t, self.n)?;
        let active_old = &old_quorum_indices[..self.t];
        let new_pts = canonical_eval_points(new_n);

        let mut old_rngs: Vec<PartyPrivateRng> = active_old
            .iter()
            .map(|&p| {
                private_operation_rng(
                    &session_id,
                    b"QSAG.HEM.SPDZ.RESHARE.OLD/v2",
                    p,
                    &mut old_party_rngs[p],
                )
            })
            .collect();
        let mut new_rngs =
            private_operation_rngs(&session_id, b"QSAG.HEM.SPDZ.RESHARE.NEW/v2", new_party_rngs);
        let mut new_mesh = OtMesh::establish(
            cshake256_32(b"QSAG.HEM.SPDZ.RESHARE.OT/v1", &session_id),
            &mut new_rngs,
        )
        .map_err(Poseidon2MpcError::Preprocess)?;

        // The core reshare retires the old sharing it is given as soon as its own check
        // passes. The PRF sharing has no check of its own here (it is verified together
        // with the seed sharing in the callback below), so both run on copies and the
        // quorum's shares are replaced only after every check has passed.
        let mut old_prf_shares = stage_seed_shares(&self.sk_prf_shares);
        let mut old_seed_shares = stage_seed_shares(&self.sk_seed_shares);

        let enrolled_root = hem_digest4_to_bytes(&self.cache.pk.pk_root);
        let new_prf_shares = run_dealerless_reshare_seed32_goldilocks(
            cshake256_32(b"QSAG.HEM.SPDZ.RESHARE.P/v1", &session_id),
            self.t,
            active_old,
            &mut old_prf_shares,
            new_t,
            &new_pts,
            &mut new_mesh,
            &mut old_rngs,
            &mut new_rngs,
            &enrolled_root,
            |_| Ok(enrolled_root),
        )?;

        let verify_budget = required_hem_jorts_reshare_verify_preprocessing_budget();
        let mut v_rngs = private_operation_rngs(
            &session_id,
            b"QSAG.HEM.SPDZ.RESHARE.VERIFY/v2",
            new_party_rngs,
        );
        let mut v_mesh = OtMesh::establish(
            cshake256_32(b"QSAG.HEM.SPDZ.RESHARE.VOT/v1", &session_id),
            &mut v_rngs,
        )
        .map_err(Poseidon2MpcError::Preprocess)?;

        let dkg_pk_seed = self.cache.dkg_pk_seed;
        let cache_ref = &self.cache;
        let prep_pow7 = if online_fixture { 0 } else { verify_budget.0 };
        let new_seed_shares = run_dealerless_reshare_seed32_goldilocks(
            cshake256_32(b"QSAG.HEM.SPDZ.RESHARE.S/v1", &session_id),
            self.t,
            active_old,
            &mut old_seed_shares,
            new_t,
            &new_pts,
            &mut new_mesh,
            &mut old_rngs,
            &mut new_rngs,
            &enrolled_root,
            |candidate_seed| {
                let (mut new_ks, mut new_vaults) = authenticate_poseidon_dkg_shares_and_preprocess(
                    cshake256_32(b"QSAG.HEM.SPDZ.RESHARE.VPREP/v1", &session_id),
                    new_t,
                    &new_pts,
                    dkg_pk_seed,
                    candidate_seed,
                    &new_prf_shares,
                    prep_pow7,
                    0,
                    0,
                    &mut v_mesh,
                    &mut v_rngs,
                )
                .map_err(|_| DkgError::PublicRootMismatch)?;
                #[cfg(any(test, feature = "testing-ephemeral"))]
                if online_fixture {
                    qsag_core::preprocessing::PreprocessedPoseidonPartyVault::fill_quorum_online_fixture(
                        new_t,
                        &mut new_vaults,
                        verify_budget,
                        &mut v_rngs[0],
                    );
                }
                let mut ks_refs: Vec<_> = new_ks[..new_t].iter_mut().collect();
                let mut v_refs: Vec<_> = new_vaults[..new_t].iter_mut().collect();
                verify_reshared_hem_jorts_key_mpc(
                    cshake256_32(b"QSAG.HEM.SPDZ.RESHARE.VCHK/v1", &session_id),
                    cache_ref,
                    new_t,
                    &mut ks_refs,
                    &mut v_refs,
                    &mut v_rngs[..new_t],
                )
                .map_err(|_| DkgError::PublicRootMismatch)?;
                Ok(enrolled_root)
            },
        )?;

        let new_cluster =
            HemEpochLatchCluster::establish(new_n, new_t, self.high_water_leaf, &mut new_rngs)?;

        // Commit. The replaced old shares wipe themselves on drop; the new committee must
        // explicitly enroll its own durable latch authority before using `durable_cert`.
        self.quorum_epoch += 1;
        self.t = new_t;
        self.n = new_n;
        self.latch_cluster = new_cluster;
        self.durable_latch_authority = None;
        self.sk_seed_shares = new_seed_shares;
        self.sk_prf_shares = new_prf_shares;
        Ok(())
    }

    /// Sign `msg` in native `[Goldilocks; 4]` SPDZ MPC (`0` intermediate A2B!) across
    /// `signer_indices` (`== n` when `durable_cert` is `None`, or `>= t` with a durable
    /// [`EpochLatchCertificate`]). Supply private RNGs in full roster order.
    ///
    /// Argument, latch-acker, certificate and preprocessing errors are returned before the
    /// leaf is touched and a retry uses the same leaf. Once the latch cluster has certified
    /// the leaf, [`Self::high_water_leaf`] has moved past it and an error from the online
    /// protocol leaves it spent; a retry signs at the next leaf.
    pub fn sign_quorum(
        &mut self,
        session_id: [u8; 32],
        signer_indices: &[usize],
        latch_ackers: &[usize],
        durable_cert: Option<&EpochLatchCertificate>,
        msg: &[u8],
        party_rngs: &mut [PartyPrivateRng],
    ) -> Result<(u64, HemJortsSignature), HemQuorumError> {
        self.sign_quorum_inner(
            session_id,
            signer_indices,
            latch_ackers,
            durable_cert,
            msg,
            party_rngs,
            false,
        )
    }

    #[cfg(any(test, feature = "testing-ephemeral"))]
    pub fn sign_quorum_online_fixture(
        &mut self,
        session_id: [u8; 32],
        signer_indices: &[usize],
        latch_ackers: &[usize],
        durable_cert: Option<&EpochLatchCertificate>,
        msg: &[u8],
        party_rngs: &mut [PartyPrivateRng],
    ) -> Result<(u64, HemJortsSignature), HemQuorumError> {
        self.sign_quorum_inner(
            session_id,
            signer_indices,
            latch_ackers,
            durable_cert,
            msg,
            party_rngs,
            true,
        )
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "explicit private custodian randomness and protocol inputs"
    )]
    fn sign_quorum_inner(
        &mut self,
        session_id: [u8; 32],
        signer_indices: &[usize],
        latch_ackers: &[usize],
        durable_cert: Option<&EpochLatchCertificate>,
        msg: &[u8],
        party_rngs: &mut [PartyPrivateRng],
        online_fixture: bool,
    ) -> Result<(u64, HemJortsSignature), HemQuorumError> {
        check_randomness_count(party_rngs, self.n)?;
        let min_signers = if durable_cert.is_some() {
            self.t
        } else {
            self.n
        };
        validate_party_subset(signer_indices, min_signers, self.n)?;
        validate_party_subset(latch_ackers, 1, self.n)?;
        if latch_ackers.len() < self.latch_cluster.latch_quorum {
            return Err(HemQuorumError::LatchRefused);
        }
        // The leaf this attempt will use: the certified one, or the next unused one.
        let epoch = match durable_cert {
            Some(cert) => cert.epoch(),
            None => self.high_water_leaf,
        };
        if epoch < self.high_water_leaf {
            return Err(HemQuorumError::LatchRefused);
        }
        if epoch >= self.cache.active_leaves as u64 {
            return Err(HemQuorumError::LeafExhausted);
        }
        let (mu_bytes, _) = hem_compute_message_mu(&self.cache.pk, msg);
        let latch_pk = self.cache.pk.latch_pq_public_key(self.cache.dkg_pk_seed);

        // Reject an un-enrolled or invalid durable certificate before advancing `party_rngs`,
        // establishing Base OTs, or touching any leaf state.
        if let Some(cert) = durable_cert {
            let binding =
                epoch_latch_binding(&latch_pk.pk_seed, &latch_pk.pk_root, epoch, &mu_bytes);
            let authority = self.durable_latch_authority.as_ref().ok_or(
                Poseidon2MpcError::LatchCertificateRejected(
                    qsag_core::dkg::EpochLatchError::CertificateCommitteeMismatch,
                ),
            )?;
            cert.verify_against(authority, self.n, self.t, epoch, &binding)
                .map_err(Poseidon2MpcError::LatchCertificateRejected)?;
        }

        let pts = canonical_eval_points(self.n);
        let sign_budget = required_hem_jorts_sign_preprocessing_budget_cached();

        let mut rngs = private_operation_rngs(&session_id, b"QSAG.HEM.SPDZ.SIGN/v2", party_rngs);
        let mut mesh = OtMesh::establish(
            cshake256_32(b"QSAG.HEM.SPDZ.SIGN.OT/v1", &session_id),
            &mut rngs,
        )
        .map_err(Poseidon2MpcError::Preprocess)?;

        let prep_pow7 = if online_fixture { 0 } else { sign_budget.0 };
        // `vaults` is only written by the test fixture fill below.
        #[cfg_attr(
            not(any(test, feature = "testing-ephemeral")),
            expect(unused_mut, reason = "mutated only by the online test fixture")
        )]
        let (mut key_shares, mut vaults) = authenticate_poseidon_dkg_shares_and_preprocess(
            cshake256_32(b"QSAG.HEM.SPDZ.SIGN.PREP/v1", &session_id),
            self.t,
            &pts,
            self.cache.dkg_pk_seed,
            &self.sk_seed_shares,
            &self.sk_prf_shares,
            prep_pow7,
            0,
            0,
            &mut mesh,
            &mut rngs,
        )?;
        #[cfg(any(test, feature = "testing-ephemeral"))]
        if online_fixture {
            qsag_core::preprocessing::PreprocessedPoseidonPartyVault::fill_quorum_online_fixture(
                self.t,
                &mut vaults,
                sign_budget,
                &mut rngs[0],
            );
        }
        for ks in &mut key_shares {
            ks.enroll_hem_key_profile(self.cache.pk, self.cache.prf_check)?;
            if let Some(authority) = &self.durable_latch_authority {
                ks.enroll_latch_authority(authority.clone())?;
            }
        }

        // Nothing above has touched the leaf. From here it is spent: the latch quorum
        // binds `epoch` to this message, the high-water mark moves past it before the
        // online protocol opens anything, and an error below does not give it back.
        self.latch_cluster.raise_floor(epoch);
        let hem_cert = self
            .latch_cluster
            .certify_epoch(
                latch_ackers,
                &latch_pk,
                HEM_JORTS_XMSS_HEIGHT as u32,
                &mu_bytes,
            )
            .map_err(|_| HemQuorumError::LatchRefused)?;
        self.high_water_leaf = self.high_water_leaf.max(hem_cert.epoch().saturating_add(1));
        if hem_cert.epoch() != epoch {
            return Err(HemQuorumError::LatchRefused);
        }

        let active_len = signer_indices.len();
        let active_signers = &signer_indices[..active_len];
        let mut sel_ks: Vec<Option<_>> = key_shares.into_iter().map(Some).collect();
        let mut sel_vs: Vec<Option<_>> = vaults.into_iter().map(Some).collect();
        let mut sel_rngs: Vec<Option<_>> = rngs.into_iter().map(Some).collect();

        let mut ks_vec = Vec::with_capacity(active_len);
        let mut v_vec = Vec::with_capacity(active_len);
        let mut r_vec = Vec::with_capacity(active_len);
        for &idx in active_signers {
            ks_vec.push(
                sel_ks[idx]
                    .take()
                    .ok_or(HemQuorumError::DuplicateParty { party: idx })?,
            );
            v_vec.push(
                sel_vs[idx]
                    .take()
                    .ok_or(HemQuorumError::DuplicateParty { party: idx })?,
            );
            r_vec.push(
                sel_rngs[idx]
                    .take()
                    .ok_or(HemQuorumError::DuplicateParty { party: idx })?,
            );
        }
        // Per-signer latches for this one attempt, starting at the certified leaf. The
        // durable record of spent leaves is `high_water_leaf`, already advanced above.
        let mut latches: Vec<MonotonicEpochLatch> = (0..active_len)
            .map(|_| MonotonicEpochLatch::new(epoch))
            .collect();

        let mut ks_refs: Vec<_> = ks_vec.iter_mut().collect();
        let mut v_refs: Vec<_> = v_vec.iter_mut().collect();
        let mut l_refs: Vec<_> = latches.iter_mut().collect();
        let (ep, sig) = sign_hem_jorts_poseidon2_mpc_cached(
            cshake256_32(b"QSAG.HEM.SPDZ.SIGN.ONLINE/v1", &session_id),
            &self.cache,
            self.t,
            durable_cert,
            &mut l_refs,
            msg,
            100_000,
            &mut ks_refs,
            &mut v_refs,
            &mut r_vec,
        )?;
        self.high_water_leaf = self.high_water_leaf.max(ep.saturating_add(1));
        Ok((ep, sig))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn latch_authority_equality_compares_every_key_byte() {
        let base = HemEpochLatchAuthority {
            mac_keys: vec![[0x11; 32], [0x22; 32], [0x33; 32]],
        };
        assert!(base == base.clone());
        // A difference in any single byte of any key, first or last, is detected.
        for key in 0..3 {
            for byte in [0usize, 15, 31] {
                let mut other = base.clone();
                other.mac_keys[key][byte] ^= 0x80;
                assert!(base != other, "key {key} byte {byte}");
                assert!(other != base, "key {key} byte {byte}");
            }
        }
        let shorter = HemEpochLatchAuthority {
            mac_keys: vec![[0x11; 32], [0x22; 32]],
        };
        assert!(base != shorter && shorter != base);
    }

    fn test_party_rngs(seed: u8, n: usize) -> Vec<PartyPrivateRng> {
        (0..n)
            .map(|p| {
                PartyPrivateRng::from_seed(
                    [seed.wrapping_add(p as u8); 32],
                    b"HEM.TEST.PRIVATE.RNG/v1",
                )
            })
            .collect()
    }

    use qsag_agg::{
        AggSigProfile, EpochWalSink, HemAggConfig, HemAggregator, SigError, SignerBitmap,
        SigningMode, ValidatorKeypair, ValidatorPublicKey, ValidatorSignature, WhirSecurityRegime,
        verify_individual_signature,
    };

    #[derive(Default)]
    struct TestEpochWal {
        state: Option<(u32, u32, [u8; 32])>,
    }

    impl EpochWalSink for TestEpochWal {
        fn persist_latched_epoch(
            &mut self,
            _pk_root: &[u8; 32],
            next_unused_epoch: u32,
            latched_epoch: u32,
            mu_bytes: &[u8; 32],
        ) -> Result<(), SigError> {
            self.state = Some((next_unused_epoch, latched_epoch, *mu_bytes));
            Ok(())
        }

        fn recovered_state(
            &self,
            _pk_root: &[u8; 32],
        ) -> Result<Option<(u32, u32, [u8; 32])>, SigError> {
            Ok(self.state)
        }
    }

    #[test]
    fn reshare_public_session_replay_cannot_recover_secret_from_one_recipient() {
        let sid = [0x43; 32];
        let mut quorum = HemDynamicShamirQuorum::stage([0x41; 32], 2, 3, 1).unwrap();
        let original_pk = quorum.public_key();
        let old_points = canonical_eval_points(2);
        let weights = lagrange_weights_zero_goldilocks(&old_points).unwrap();
        let secret = weights[0] * quorum.shares[0].leaf_vals[0][0]
            + weights[1] * quorum.shares[1].leaf_vals[0][0];

        // Exact pre-fix attack: the session, epoch and dealer index disclosed every
        // polynomial coefficient. One recipient could subtract all dealer masks
        // from its aggregate share and learn the secret without reaching threshold.
        let new_points = canonical_eval_points(5);
        let mut public_mask = Goldilocks::ZERO;
        let mut vulnerable_recipient = Goldilocks::ZERO;
        for (party, (&weight, share)) in
            weights.iter().zip(quorum.shares.iter()).enumerate().take(2)
        {
            let seed = cshake256_32(
                b"QSAG.HEM.QSB.DEALER.RNG/v1",
                &encode_multi_frame(&[&sid, &0u64.to_le_bytes(), &(party as u32).to_le_bytes()]),
            );
            let mut replay = PartyPrivateRng::from_seed(seed, b"QSAG.HEM.QSB.DEALER.STREAM/v1");
            let _ = shamir_share_ext2(3, &new_points, GoldilocksExt2::ZERO, &mut replay);
            let mask_secret = replay.next_ext2();
            let _ = shamir_share_ext2(3, &new_points, mask_secret, &mut replay);
            let mask = shamir_share_goldilocks(3, &new_points, Goldilocks::ZERO, &mut replay)[0];
            public_mask += mask;
            vulnerable_recipient += weight * share.leaf_vals[0][0] + mask;
        }
        assert_eq!(vulnerable_recipient - public_mask, secret);

        let before = quorum.shares[0].to_vault_bytes().unwrap();
        assert!(matches!(
            quorum.reshare_quorum(
                sid,
                &[0, 1],
                3,
                5,
                &mut test_party_rngs(1, 2),
                &mut test_party_rngs(5, 5)
            ),
            Err(HemQuorumError::InvalidRandomnessCount {
                expected: 3,
                got: 2
            })
        ));
        assert_eq!(quorum.shares[0].to_vault_bytes().unwrap(), before);
        assert_eq!(quorum.quorum_epoch(), 0);

        quorum
            .reshare_quorum(
                sid,
                &[0, 1],
                3,
                5,
                &mut test_party_rngs(1, 3),
                &mut test_party_rngs(5, 5),
            )
            .unwrap();
        assert_ne!(quorum.shares[0].leaf_vals[0][0] - public_mask, secret);
        let new_weights = lagrange_weights_zero_goldilocks(&new_points[..3]).unwrap();
        let recovered = (0..3).fold(Goldilocks::ZERO, |sum, p| {
            sum + new_weights[p] * quorum.shares[p].leaf_vals[0][0]
        });
        assert_eq!(recovered, secret);
        assert_eq!(quorum.public_key(), original_pk);

        // Same public transcript, distinct private entropy: different shares,
        // same enrolled key. Refresh also preserves the threshold secret.
        let first_share = quorum.shares[0].leaf_vals[0][0];
        quorum
            .proactive_refresh(sid, &mut test_party_rngs(11, 5))
            .unwrap();
        assert_ne!(quorum.shares[0].leaf_vals[0][0], first_share);
        let refreshed = (0..3).fold(Goldilocks::ZERO, |sum, p| {
            sum + new_weights[p] * quorum.shares[p].leaf_vals[0][0]
        });
        assert_eq!(refreshed, secret);
        assert_eq!(quorum.public_key(), original_pk);
    }

    #[test]
    fn dealerless_keygen_public_session_is_not_key_entropy() {
        let sid = [0x39; 32];
        let a = HemSpdzSeedQuorum::keygen_dealerless_online_fixture(
            sid,
            2,
            2,
            1,
            &mut test_party_rngs(1, 2),
        )
        .unwrap();
        let b = HemSpdzSeedQuorum::keygen_dealerless_online_fixture(
            sid,
            2,
            2,
            1,
            &mut test_party_rngs(7, 2),
        )
        .unwrap();
        assert_ne!(a.public_key(), b.public_key());
    }

    #[test]
    fn e2e_dynamic_quorum_switch_2of3_to_3of5_aggregates_in_hem_bciks_qrom128() {
        let _memory = crate::test_budget::reserve_mb(180);
        // 1. Validator 0: QS-B Dynamic Shamir Quorum starts at (2, 3), signs Epoch 0,
        //    switches via Π_reshare to (3, 5) WITHOUT changing its 65B ValidatorPublicKey,
        //    proactively refreshes via Π_refresh, then signs Epoch 1!
        let mut qsb = HemDynamicShamirQuorum::stage([0x11; 32], 2, 3, 8).unwrap();
        let pk0_initial = qsb.public_key();
        let agg_pk0 = ValidatorPublicKey::from_bytes_canonical(&pk0_initial.to_bytes()).unwrap();
        assert_eq!(agg_pk0.profile, AggSigProfile::JortsPoseidon2);

        let (ep0, sig0_warmup) = qsb
            .sign_quorum(&[0, 2], &[0, 1, 2], b"epoch-0 warmup block")
            .unwrap();
        assert_eq!(ep0, 0);
        let agg_sig0_warmup = ValidatorSignature::from_bytes_canonical(
            AggSigProfile::JortsPoseidon2,
            &sig0_warmup.to_bytes(),
        )
        .unwrap();
        assert!(verify_individual_signature(
            &agg_pk0,
            b"epoch-0 warmup block",
            &agg_sig0_warmup
        ));

        // Switch (2, 3) -> (3, 5) via Π_reshare and verify pubkey invariance!
        qsb.reshare_quorum(
            [0x22; 32],
            &[1, 2],
            3,
            5,
            &mut test_party_rngs(1, 3),
            &mut test_party_rngs(4, 5),
        )
        .unwrap();
        assert_eq!(qsb.public_key(), pk0_initial);
        assert_eq!(qsb.threshold_and_size(), (3, 5));
        assert_eq!(qsb.quorum_epoch(), 1);
        assert_eq!(qsb.high_water_leaf(), 1);

        // Proactive refresh Π_refresh on (3, 5) -> pubkey still bit-for-bit identical!
        qsb.proactive_refresh([0x33; 32], &mut test_party_rngs(10, 5))
            .unwrap();
        assert_eq!(qsb.public_key(), pk0_initial);
        assert_eq!(qsb.quorum_epoch(), 2);

        // 2. Validator 1: QS-A Committee-Partitioned Quorum (2-of-3)
        let mut qsa = HemCommitteePartitionedQuorum::stage([0x44; 32], 2, 3, 4).unwrap();
        let agg_pk1 =
            ValidatorPublicKey::from_bytes_canonical(&qsa.public_key().to_bytes()).unwrap();

        // 3. Validator 2: Standard single-custodian `ValidatorKeypair` (`JortsPoseidon2`)
        let mut v2_kp =
            ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[0x55; 32], 2);
        let agg_pk2 = v2_kp.pk;

        // Consensus message signed across ALL THREE heterogeneous custody validators!
        let block_msg = b"qsag consensus block #42: QS <-> AG bridged end-to-end";
        let (ep1, sig_qsb) = qsb
            .sign_quorum(&[1, 3, 4], &[0, 1, 2, 4], block_msg)
            .unwrap();
        assert_eq!(ep1, 1);

        let (_, sig_qsa) = qsa.sign_with_committee(&[0, 2], block_msg).unwrap();
        let mut wal2 = TestEpochWal::default();
        let sig_v2 = v2_kp.sign_stateful(block_msg, 0, &mut wal2).unwrap();

        let agg_sig_qsb = ValidatorSignature::from_bytes_canonical(
            AggSigProfile::JortsPoseidon2,
            &sig_qsb.to_bytes(),
        )
        .unwrap();
        let agg_sig_qsa = ValidatorSignature::from_bytes_canonical(
            AggSigProfile::JortsPoseidon2,
            &sig_qsa.to_bytes(),
        )
        .unwrap();

        assert!(verify_individual_signature(
            &agg_pk0,
            block_msg,
            &agg_sig_qsb
        ));
        assert!(verify_individual_signature(
            &agg_pk1,
            block_msg,
            &agg_sig_qsa
        ));
        assert!(verify_individual_signature(&agg_pk2, block_msg, &sig_v2));

        // 4. Untrusted public `Hem` aggregator proves & verifies under `BciksJohnsonQrom128`!
        let committee_pks = vec![agg_pk0, agg_pk1, agg_pk2];
        let bitmap = SignerBitmap::from_active_indices(3, &[0, 1, 2]).unwrap();
        let mode = SigningMode::SharedMessage(block_msg);
        let cfg = HemAggConfig {
            regime: WhirSecurityRegime::BciksJohnsonQrom128,
            ..HemAggConfig::default_for(AggSigProfile::JortsPoseidon2, [0x77; 32])
        };

        let agg_proof = HemAggregator::aggregate_with_config(
            &committee_pks,
            &bitmap,
            &mode,
            &[agg_sig_qsb, agg_sig_qsa, sig_v2],
            &cfg,
        )
        .unwrap();

        assert_eq!(agg_proof.num_signers(), 3);
        assert!(HemAggregator::verify_with_regime(
            &committee_pks,
            &mode,
            &agg_proof,
            WhirSecurityRegime::BciksJohnsonQrom128,
        ));
    }

    #[test]
    fn negative_proactive_security_old_shares_tamper_and_epoch_mismatch_rejected() {
        let _memory = crate::test_budget::reserve_mb(190);
        let mut qsb = HemDynamicShamirQuorum::stage([0x81; 32], 2, 3, 4).unwrap();
        // Save detached snapshots of Epoch-0 `(2, 3)` shares BEFORE resharing!
        let saved_old_0 = HemShamirCustodianShare::from_vault_bytes(
            &qsb.custodian_shares()[0].to_vault_bytes().unwrap(),
        )
        .unwrap();
        let saved_old_1 = HemShamirCustodianShare::from_vault_bytes(
            &qsb.custodian_shares()[1].to_vault_bytes().unwrap(),
        )
        .unwrap();

        // Spend leaf 0 in Epoch 0
        qsb.sign_quorum(&[0, 1], &[0, 1, 2], b"burn leaf 0")
            .unwrap();

        // 1. Fault A: Tampered sub-share in transit is caught by Round-1 commitment check!
        assert!(matches!(
            qsb.reshare_quorum_with_fault(
                [0x82; 32],
                &[0, 1],
                3,
                5,
                &mut test_party_rngs(20, 3),
                &mut test_party_rngs(30, 5),
                ReshareFaultInjection::TamperInTransit {
                    dealer: 1,
                    recipient: 3,
                },
            ),
            Err(HemQuorumError::CommitmentMismatch {
                dealer: 1,
                recipient: 3,
            })
        ));

        // 2. Fault B: Consistent commitment to degree >= t' polynomial caught by HVZK degree check!
        assert!(matches!(
            qsb.reshare_quorum_with_fault(
                [0x83; 32],
                &[0, 1],
                3,
                5,
                &mut test_party_rngs(20, 3),
                &mut test_party_rngs(30, 5),
                ReshareFaultInjection::CorruptPolynomialDegree { dealer: 0 },
            ),
            Err(HemQuorumError::DegreeCheckFailed { dealer: 0 })
        ));

        // 3. Fault C: Valid degree < t' polynomial with shifted constant term caught by SPDZ MacCheck!
        assert!(matches!(
            qsb.reshare_quorum_with_fault(
                [0x84; 32],
                &[0, 1],
                3,
                5,
                &mut test_party_rngs(20, 3),
                &mut test_party_rngs(30, 5),
                ReshareFaultInjection::ShiftConstantTerm { dealer: 1 },
            ),
            Err(HemQuorumError::ReshareMacCheckFailed)
        ));

        // Genuine reshare (2, 3) -> (3, 5) succeeds!
        qsb.reshare_quorum(
            [0x85; 32],
            &[0, 2],
            3,
            5,
            &mut test_party_rngs(40, 3),
            &mut test_party_rngs(50, 5),
        )
        .unwrap();
        assert_eq!(qsb.quorum_epoch(), 1);
        assert_eq!(qsb.high_water_leaf(), 1);

        // 4. < t' (2 of 5) new shares CANNOT sign!
        assert_eq!(
            qsb.sign_quorum(&[0, 1], &[0, 1, 2, 3], b"sub-threshold attempt"),
            Err(HemQuorumError::NotEnoughSigners { have: 2, need: 3 })
        );

        // Save pre-refresh Epoch-1 share of party 0, then run Π_refresh -> Epoch 2
        let saved_epoch1_p0 = HemShamirCustodianShare::from_vault_bytes(
            &qsb.custodian_shares()[0].to_vault_bytes().unwrap(),
        )
        .unwrap();
        qsb.proactive_refresh([0x86; 32], &mut test_party_rngs(60, 5))
            .unwrap();
        assert_eq!(qsb.quorum_epoch(), 2);

        // Mint a genuine Epoch-2 latch certificate for leaf 1 to test detached share attacks
        let msg = b"target message after refresh";
        let (mu_bytes, _) = hem_compute_message_mu(&qsb.public_key(), msg);
        let latch_pk = qsb
            .public_key()
            .latch_pq_public_key(qsb.public_directory().dkg_pk_seed);
        let cert = qsb
            .latch_cluster
            .certify_epoch(
                &[0, 1, 2, 3],
                &latch_pk,
                HEM_JORTS_XMSS_HEIGHT as u32,
                &mu_bytes,
            )
            .unwrap();
        assert_eq!(cert.epoch(), 1); // Monotone floor prevented leaf 0 replay!

        // 5. Old `(2, 3)` pre-reshare shares are rejected with `QuorumEpochMismatch`!
        assert_eq!(
            sign_from_shamir_share_slice(
                qsb.public_directory(),
                qsb.latch_authority(),
                qsb.quorum_epoch(),
                2,
                3,
                &cert,
                msg,
                &[&saved_old_0, &saved_old_1],
            ),
            Err(HemQuorumError::QuorumEpochMismatch {
                expected: 2,
                got: 0,
                party: 0,
            })
        );

        // 6. Mixing 1 pre-refresh Epoch-1 share with 2 post-refresh Epoch-2 shares is rejected!
        let cur_s1 = &qsb.custodian_shares()[1];
        let cur_s2 = &qsb.custodian_shares()[2];
        assert_eq!(
            sign_from_shamir_share_slice(
                qsb.public_directory(),
                qsb.latch_authority(),
                qsb.quorum_epoch(),
                3,
                5,
                &cert,
                msg,
                &[&saved_epoch1_p0, cur_s1, cur_s2],
            ),
            Err(HemQuorumError::QuorumEpochMismatch {
                expected: 2,
                got: 1,
                party: 0,
            })
        );

        // Even if an attacker forces `quorum_epoch = 2` on `saved_epoch1_p0` in memory,
        // proactive polynomial blinding makes Lagrange reconstruction fail cryptographic verification!
        let mut forged_epoch_p0 = saved_epoch1_p0;
        forged_epoch_p0.quorum_epoch = 2;
        assert!(matches!(
            sign_from_shamir_share_slice(
                qsb.public_directory(),
                qsb.latch_authority(),
                qsb.quorum_epoch(),
                3,
                5,
                &cert,
                msg,
                &[&forged_epoch_p0, cur_s1, cur_s2],
            ),
            Err(HemQuorumError::PrfCommitmentMismatch)
                | Err(HemQuorumError::EndpointVerificationFailed { .. })
        ));
    }

    fn all_share_bytes(q: &HemDynamicShamirQuorum) -> Vec<Vec<u8>> {
        q.custodian_shares()
            .iter()
            .map(|s| s.to_vault_bytes().unwrap())
            .collect()
    }

    #[test]
    fn unanimous_reshare_shift_aborts_and_preserves_live_custody() {
        let mut qsb = HemDynamicShamirQuorum::stage([0xd1; 32], 2, 2, 1).unwrap();
        let pk = qsb.public_key();
        let before = all_share_bytes(&qsb);
        assert!(matches!(
            qsb.reshare_quorum_with_fault(
                [0xd2; 32],
                &[0, 1],
                2,
                2,
                &mut test_party_rngs(21, 2),
                &mut test_party_rngs(31, 2),
                ReshareFaultInjection::ShiftConstantTerm { dealer: 0 },
            ),
            Err(HemQuorumError::ReshareMacCheckFailed)
        ));
        assert_eq!(all_share_bytes(&qsb), before);
        assert_eq!(qsb.quorum_epoch(), 0);
        assert_eq!(qsb.high_water_leaf(), 0);
        let (_, sig) = qsb.sign_quorum(&[0, 1], &[0, 1], b"after-abort").unwrap();
        assert!(verify_hem_jorts_signature(&pk, b"after-abort", &sig));
    }

    #[test]
    fn shamir_rejected_reshare_leaves_old_custody_byte_identical() {
        let mut qsb = HemDynamicShamirQuorum::stage([0xa1; 32], 2, 3, 2).unwrap();
        let pk = qsb.public_key();
        let before = all_share_bytes(&qsb);
        for (sid, fault) in [
            (
                0xa2u8,
                ReshareFaultInjection::TamperInTransit {
                    dealer: 0,
                    recipient: 1,
                },
            ),
            (
                0xa3,
                ReshareFaultInjection::CorruptPolynomialDegree { dealer: 1 },
            ),
            (0xa4, ReshareFaultInjection::ShiftConstantTerm { dealer: 0 }),
        ] {
            assert!(
                qsb.reshare_quorum_with_fault(
                    [sid; 32],
                    &[0, 1],
                    2,
                    4,
                    &mut test_party_rngs(1, 3),
                    &mut test_party_rngs(9, 4),
                    fault,
                )
                .is_err()
            );
            assert_eq!(all_share_bytes(&qsb), before);
            assert_eq!(qsb.quorum_epoch(), 0);
            assert_eq!(qsb.threshold_and_size(), (2, 3));
            assert_eq!(qsb.high_water_leaf(), 0);
        }
        // The untouched old custody still signs at the first leaf.
        let (ep, sig) = qsb.sign_quorum(&[0, 1], &[0, 1, 2], b"after").unwrap();
        assert_eq!(ep, 0);
        assert!(verify_hem_jorts_signature(&pk, b"after", &sig));
    }

    #[test]
    fn shamir_sign_errors_burn_a_leaf_only_after_the_latch_certifies() {
        let mut qsb = HemDynamicShamirQuorum::stage([0xb1; 32], 2, 3, 3).unwrap();
        let pk = qsb.public_key();

        // Rejected before certification: nothing is spent.
        let before = all_share_bytes(&qsb);
        assert_eq!(
            qsb.sign_quorum(&[0], &[0, 1, 2], b"m"),
            Err(HemQuorumError::NotEnoughSigners { have: 1, need: 2 })
        );
        assert_eq!(
            qsb.sign_quorum(&[0, 1], &[0, 1], b"m"),
            Err(HemQuorumError::LatchRefused)
        );
        assert_eq!(qsb.high_water_leaf(), 0);
        assert_eq!(all_share_bytes(&qsb), before);

        // A signer's share of leaf 0 is wrong: the latch certifies leaf 0 for "first",
        // then signing fails. Leaf 0 is spent in every share.
        qsb.shares[1].leaf_vals[0][0] += Goldilocks::ONE;
        assert_eq!(
            qsb.sign_quorum(&[0, 1], &[0, 1, 2], b"first"),
            Err(HemQuorumError::PrfCommitmentMismatch)
        );
        assert_eq!(qsb.high_water_leaf(), 1);
        for sh in qsb.custodian_shares() {
            assert_eq!(sh.high_water_leaf, 1);
            assert!(sh.leaf_vals[0].is_empty() && sh.leaf_macs[0].is_empty());
        }

        // A retry with another message cannot reach leaf 0; it signs at leaf 1.
        let (ep, sig) = qsb.sign_quorum(&[0, 1], &[0, 1, 2], b"second").unwrap();
        assert_eq!(ep, 1);
        assert_eq!(sig.stateful_leaf_idx, 1);
        assert!(verify_hem_jorts_signature(&pk, b"second", &sig));
        assert_eq!(qsb.high_water_leaf(), 2);

        // The burned state survives persistence and reload.
        let dir =
            HemQuorumPublicDirectory::from_bytes_canonical(&qsb.public_directory().to_bytes())
                .unwrap();
        let shares = all_share_bytes(&qsb)
            .iter()
            .map(|b| HemShamirCustodianShare::from_vault_bytes(b).unwrap())
            .collect();
        let mut reloaded =
            HemDynamicShamirQuorum::from_persisted_shares(dir, shares, [0xb2; 32]).unwrap();
        assert_eq!(reloaded.high_water_leaf(), 2);
        let (ep, _) = reloaded.sign_quorum(&[1, 2], &[0, 1, 2], b"third").unwrap();
        assert_eq!(ep, 2);
        assert_eq!(
            reloaded.sign_quorum(&[1, 2], &[0, 1, 2], b"fourth"),
            Err(HemQuorumError::LeafExhausted)
        );
    }

    #[test]
    fn shamir_reserved_leaf_is_gone_from_the_quorum_before_it_is_signed() {
        let mut qsb = HemDynamicShamirQuorum::stage([0xd1; 32], 2, 3, 3).unwrap();
        let pk = qsb.public_key();
        let leaf0_p0 = qsb.shares[0].leaf_vals[0].clone();

        let reserved = qsb.reserve_leaf(&[0, 2], &[0, 1, 2], b"one").unwrap();
        assert_eq!(reserved.leaf_epoch(), 0);
        // What a caller would persist now holds no trace of leaf 0.
        assert_eq!(qsb.high_water_leaf(), 1);
        let persisted = all_share_bytes(&qsb);
        for (p, bytes) in persisted.iter().enumerate() {
            let sh = HemShamirCustodianShare::from_vault_bytes(bytes).unwrap();
            assert_eq!(sh.high_water_leaf, 1, "party {p}");
            assert!(sh.leaf_vals[0].is_empty() && sh.leaf_macs[0].is_empty());
        }
        let needle: Vec<u8> = leaf0_p0[..4].iter().flat_map(|g| g.to_le_bytes()).collect();
        assert!(!persisted[0].windows(needle.len()).any(|w| w == needle));

        // A quorum restored from that state (a crash before signing) cannot reach leaf 0.
        let dir =
            HemQuorumPublicDirectory::from_bytes_canonical(&qsb.public_directory().to_bytes())
                .unwrap();
        let shares = persisted
            .iter()
            .map(|b| HemShamirCustodianShare::from_vault_bytes(b).unwrap())
            .collect();
        let mut restored =
            HemDynamicShamirQuorum::from_persisted_shares(dir, shares, [0xd2; 32]).unwrap();
        let (ep, sig) = restored.sign_quorum(&[0, 1], &[0, 1, 2], b"two").unwrap();
        assert_eq!(ep, 1);
        assert!(verify_hem_jorts_signature(&pk, b"two", &sig));

        // The reservation signs only the message it was certified for, once.
        let other = qsb.reserve_leaf(&[0, 1], &[0, 1, 2], b"three").unwrap();
        assert_eq!(other.leaf_epoch(), 1);
        assert_eq!(
            qsb.sign_reserved(other, b"not three"),
            Err(HemQuorumError::LatchRefused)
        );
        assert_eq!(qsb.high_water_leaf(), 2);
        let (ep, sig) = qsb.sign_reserved(reserved, b"one").unwrap();
        assert_eq!(ep, 0);
        assert!(verify_hem_jorts_signature(&pk, b"one", &sig));

        // Shares a crashed writer left at different marks are brought up to the highest.
        let mut lagging: Vec<HemShamirCustodianShare> = persisted
            .iter()
            .map(|b| HemShamirCustodianShare::from_vault_bytes(b).unwrap())
            .collect();
        for sh in &mut lagging {
            sh.burn_leaves_below(2);
            sh.burn_leaves_below(1);
            assert_eq!(sh.high_water_leaf, 2);
        }
    }

    fn tweak_seed_share(share: &mut ShamirPoseidonSeedShare, undo: bool) {
        let (bit, byte) = (Goldilocks::ONE, Goldilocks::from_u64_reduced(8));
        if undo {
            share.bit_shares[3] -= bit;
            share.byte_shares[0] -= byte;
        } else {
            share.bit_shares[3] += bit;
            share.byte_shares[0] += byte;
        }
    }

    #[test]
    fn spdz_rejected_reshare_and_failed_sign_keep_state_coherent() {
        let _memory = crate::test_budget::reserve_mb(220);
        let mut spdz = HemSpdzSeedQuorum::keygen_dealerless_online_fixture(
            [0xc1; 32],
            2,
            2,
            3,
            &mut test_party_rngs(120, 2),
        )
        .unwrap();
        let pk = spdz.public_key();

        // Reshare with a wrong seed share: the PRF sharing reshares cleanly, then the
        // seed sharing is rejected. Both old sharings must still be the live ones.
        tweak_seed_share(&mut spdz.sk_seed_shares[0], false);
        assert!(
            spdz.reshare_quorum_online_fixture(
                [0xc2; 32],
                &[0, 1],
                2,
                3,
                &mut test_party_rngs(130, 2),
                &mut test_party_rngs(140, 3),
            )
            .is_err()
        );
        tweak_seed_share(&mut spdz.sk_seed_shares[0], true);
        assert!(spdz.sk_prf_shares.iter().all(|s| s.is_valid()));
        assert!(spdz.sk_seed_shares.iter().all(|s| s.is_valid()));
        assert_eq!((spdz.t, spdz.n, spdz.quorum_epoch()), (2, 2, 0));
        assert_eq!(spdz.high_water_leaf(), 0);

        // Too few latch ackers: refused before the leaf is touched.
        assert_eq!(
            spdz.sign_quorum_online_fixture(
                [0xc3; 32],
                &[0, 1],
                &[0],
                None,
                b"m0",
                &mut test_party_rngs(150, 2),
            ),
            Err(HemQuorumError::LatchRefused)
        );
        assert_eq!(spdz.high_water_leaf(), 0);

        // The old custody is intact: it signs at leaf 0.
        let (ep, sig) = spdz
            .sign_quorum_online_fixture(
                [0xc4; 32],
                &[0, 1],
                &[0, 1],
                None,
                b"m0",
                &mut test_party_rngs(151, 2),
            )
            .unwrap();
        assert_eq!(ep, 0);
        assert!(verify_hem_jorts_signature(&pk, b"m0", &sig));
        assert_eq!(spdz.high_water_leaf(), 1);

        // A signing attempt that fails in the online protocol spends its leaf.
        tweak_seed_share(&mut spdz.sk_seed_shares[0], false);
        assert!(
            spdz.sign_quorum_online_fixture(
                [0xc5; 32],
                &[0, 1],
                &[0, 1],
                None,
                b"m1",
                &mut test_party_rngs(152, 2),
            )
            .is_err()
        );
        tweak_seed_share(&mut spdz.sk_seed_shares[0], true);
        assert_eq!(spdz.high_water_leaf(), 2);

        // The retry signs another message at leaf 2, never at the spent leaf 1.
        let (ep, sig) = spdz
            .sign_quorum_online_fixture(
                [0xc6; 32],
                &[0, 1],
                &[0, 1],
                None,
                b"m1-retry",
                &mut test_party_rngs(153, 2),
            )
            .unwrap();
        assert_eq!(ep, 2);
        assert_eq!(sig.stateful_leaf_idx, 2);
        assert!(verify_hem_jorts_signature(&pk, b"m1-retry", &sig));

        // The latch cluster follows the high-water mark across a reshare.
        spdz.reshare_quorum_online_fixture(
            [0xc7; 32],
            &[0, 1],
            2,
            3,
            &mut test_party_rngs(160, 2),
            &mut test_party_rngs(170, 3),
        )
        .unwrap();
        assert_eq!(spdz.public_key(), pk);
        assert_eq!((spdz.t, spdz.n, spdz.quorum_epoch()), (2, 3, 1));
        assert_eq!(
            spdz.sign_quorum_online_fixture(
                [0xc8; 32],
                &[0, 1, 2],
                &[0, 1, 2],
                None,
                b"exhausted",
                &mut test_party_rngs(180, 3),
            ),
            Err(HemQuorumError::LeafExhausted)
        );
        assert_eq!(spdz.high_water_leaf(), 3);
    }

    #[test]
    fn e2e_dealerless_spdz_seed_quorum_sign_reshare_and_hem_aggregate() {
        let _memory = crate::test_budget::reserve_mb(250);
        // 100% dealerless Goldilocks DKG -> Gilboa byte auth -> SPDZ MPC leaf keygen (`active_leaves = 2`)
        let mut spdz = HemSpdzSeedQuorum::keygen_dealerless_online_fixture(
            [0x91; 32],
            2,
            2,
            2,
            &mut test_party_rngs(70, 2),
        )
        .unwrap();
        let pk_initial = spdz.public_key();
        let agg_pk = ValidatorPublicKey::from_bytes_canonical(&pk_initial.to_bytes()).unwrap();

        let (ep0, sig0) = spdz
            .sign_quorum_online_fixture(
                [0x92; 32],
                &[0, 1],
                &[0, 1],
                None,
                b"spdz epoch 0",
                &mut test_party_rngs(80, 2),
            )
            .unwrap();
        assert_eq!(ep0, 0);
        let agg_sig0 = ValidatorSignature::from_bytes_canonical(
            AggSigProfile::JortsPoseidon2,
            &sig0.to_bytes(),
        )
        .unwrap();
        assert!(verify_individual_signature(
            &agg_pk,
            b"spdz epoch 0",
            &agg_sig0
        ));

        // Dynamic `(2, 2) -> (2, 3)` seed reshare verified in SPDZ MPC without reconstructing secrets!
        spdz.reshare_quorum_online_fixture(
            [0x93; 32],
            &[0, 1],
            2,
            3,
            &mut test_party_rngs(90, 2),
            &mut test_party_rngs(100, 3),
        )
        .unwrap();
        assert_eq!(spdz.public_key(), pk_initial);
        assert_eq!(spdz.quorum_epoch(), 1);

        let msg1 = b"spdz epoch 1 after (2,2)->(2,3) reshare";
        let (ep1, sig1) = spdz
            .sign_quorum_online_fixture(
                [0x94; 32],
                &[0, 1, 2],
                &[0, 1, 2],
                None,
                msg1,
                &mut test_party_rngs(110, 3),
            )
            .unwrap();
        assert_eq!(ep1, 1);
        let agg_sig1 = ValidatorSignature::from_bytes_canonical(
            AggSigProfile::JortsPoseidon2,
            &sig1.to_bytes(),
        )
        .unwrap();
        assert!(verify_individual_signature(&agg_pk, msg1, &agg_sig1));

        let bitmap = SignerBitmap::from_active_indices(1, &[0]).unwrap();
        let mode = SigningMode::SharedMessage(msg1);
        let cfg = HemAggConfig {
            regime: WhirSecurityRegime::BciksJohnsonQrom128,
            ..HemAggConfig::default_for(AggSigProfile::JortsPoseidon2, [0x95; 32])
        };
        let proof = HemAggregator::aggregate_with_config(
            core::slice::from_ref(&agg_pk),
            &bitmap,
            &mode,
            &[agg_sig1],
            &cfg,
        )
        .unwrap();
        assert!(HemAggregator::verify_with_regime(
            core::slice::from_ref(&agg_pk),
            &mode,
            &proof,
            WhirSecurityRegime::BciksJohnsonQrom128,
        ));
    }

    #[test]
    fn test_hem_spdz_seed_quorum_durable_latch_certificate_subset_sign() {
        let _memory = crate::test_budget::reserve_mb(360);
        use qsag_core::dkg::{FsWalEpochLatch, QuorumEpochLatchCluster};

        let mut spdz = HemSpdzSeedQuorum::keygen_dealerless_online_fixture(
            [0xA1; 32],
            2,
            4,
            4,
            &mut test_party_rngs(120, 4),
        )
        .unwrap();
        let agg_pk =
            ValidatorPublicKey::from_bytes_canonical(&spdz.public_key().to_bytes()).unwrap();

        let dir = std::env::temp_dir().join(format!(
            "qsag-hem-spdz-durable-cert-{}-{}",
            std::process::id(),
            0xA1B2_u32
        ));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();

        let mac_keys: Vec<[u8; 32]> = (0..4).map(|i| [0x41 + i as u8; 32]).collect();
        let latches: Vec<FsWalEpochLatch> = (0..4)
            .map(|i| {
                FsWalEpochLatch::create_new_for_fresh_key(
                    dir.join(format!("custodian-{i}.wal")),
                    mac_keys[i],
                )
                .unwrap()
            })
            .collect();
        let mut durable_cluster =
            QuorumEpochLatchCluster::from_durable_latches(1, latches, mac_keys).unwrap();

        let msg0 = b"spdz 2-of-4 subset sign with enrolled durable certificate";
        let binding0 = spdz.epoch_latch_binding(0, msg0);
        // Under (n=4, t=2, f=1), 2q > n+f = 5 requires q = 3: 2 approvals fail closed, 3 succeed.
        assert!(durable_cluster.certify_epoch(&[0, 1], 0, binding0).is_err());
        let cert0 = durable_cluster
            .certify_epoch(&[0, 1, 3], 0, binding0)
            .unwrap();

        // Before enrollment, `Some(&cert0)` fails closed without spending leaf 0.
        assert!(
            spdz.sign_quorum_online_fixture(
                [0xA2; 32],
                &[0, 3],
                &[0, 1, 3],
                Some(&cert0),
                msg0,
                &mut test_party_rngs(130, 4),
            )
            .is_err()
        );
        assert_eq!(spdz.high_water_leaf(), 0);

        // Enroll the committee authority once (idempotent on same authority, rejects another).
        spdz.enroll_durable_latch_authority(durable_cluster.authority())
            .unwrap();
        spdz.enroll_durable_latch_authority(durable_cluster.authority())
            .unwrap();

        // Sign with 2-of-4 signers `[0, 3]` and 3-of-4 latch ackers `[0, 1, 3]` (custodian 2 offline).
        let (ep0, sig0) = spdz
            .sign_quorum_online_fixture(
                [0xA3; 32],
                &[0, 3],
                &[0, 1, 3],
                Some(&cert0),
                msg0,
                &mut test_party_rngs(140, 4),
            )
            .unwrap();
        assert_eq!(ep0, 0);
        assert_eq!(spdz.high_water_leaf(), 1);
        let agg_sig0 = ValidatorSignature::from_bytes_canonical(
            AggSigProfile::JortsPoseidon2,
            &sig0.to_bytes(),
        )
        .unwrap();
        assert!(verify_individual_signature(&agg_pk, msg0, &agg_sig0));

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn hem_roster_bound_is_exclusive_and_party_254_roundtrips() {
        assert!(HemDynamicShamirQuorum::stage([0x21; 32], 2, MAX_HEM_QUORUM_PARTIES, 1).is_err());
        let quorum = HemDynamicShamirQuorum::stage([0x22; 32], 2, 255, 1).unwrap();
        let bytes = quorum.shares[254].to_vault_bytes().unwrap();
        let decoded = HemShamirCustodianShare::from_vault_bytes(&bytes).unwrap();
        assert_eq!(decoded.party_id, 254);
        assert_eq!(decoded.n, 255);
    }

    #[test]
    fn hem_qsb_reshare_and_proactive_refresh_above_64_custodians() {
        let _memory = crate::test_budget::reserve_mb(220);
        let mut qsb = HemDynamicShamirQuorum::stage([0x61; 32], 2, 3, 2).expect("stage 2-of-3");
        let pk_initial = qsb.public_key();
        let agg_pk = ValidatorPublicKey::from_bytes_canonical(&pk_initial.to_bytes()).unwrap();

        // Reshare (2, 3) -> (3, 100) (`new_n = 100 > 64`, up to `MAX_HEM_QUORUM_PARTIES = 256`).
        qsb.reshare_quorum(
            [0x62; 32],
            &[0, 2],
            3,
            100,
            &mut test_party_rngs(10, 3),
            &mut test_party_rngs(20, 100),
        )
        .expect("reshare to 3-of-100");
        assert_eq!(qsb.public_key(), pk_initial);
        assert_eq!(qsb.threshold_and_size(), (3, 100));

        // Proactive refresh across all 100 custodians.
        qsb.proactive_refresh([0x63; 32], &mut test_party_rngs(140, 100))
            .expect("proactive refresh on 3-of-100");
        assert_eq!(qsb.public_key(), pk_initial);

        // Sign using high-indexed custodians `[5, 67, 99]` (`> 64`) and `q = 52` latch ackers (`2*52 = 104 > 100 + 2`).
        let ackers: Vec<usize> = (0..52).collect();
        let msg = b"3-of-100 dynamic shamir sign after >64 reshare and refresh";
        let (ep, sig) = qsb
            .sign_quorum(&[5, 67, 99], &ackers, msg)
            .expect("sign on 3-of-100");
        assert_eq!(ep, 0);
        let agg_sig = ValidatorSignature::from_bytes_canonical(
            AggSigProfile::JortsPoseidon2,
            &sig.to_bytes(),
        )
        .unwrap();
        assert!(verify_individual_signature(&agg_pk, msg, &agg_sig));
    }
}
