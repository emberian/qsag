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
    DkgError, EpochLatchAuthorityPublic, EpochLatchCertificate, QuorumEpochLatchCluster,
    ShamirPoseidonSeedShare, run_dealerless_dkg_seed32_goldilocks,
    run_dealerless_refresh_seed32_goldilocks, run_dealerless_reshare_seed32_goldilocks,
};
use qsag_core::field::goldilocks::{Goldilocks, GoldilocksExt2};
pub use qsag_core::poseidon2_mpc::{
    HEM_JORTS_MAX_LEAVES, HEM_JORTS_PK_BYTES, HEM_JORTS_SIG_BYTES, HEM_JORTS_XMSS_HEIGHT,
    HEM_WOTS_BASE_W, HEM_WOTS_CHAINS, HEM_WOTS_MAX_STEP, HEM_WOTS_TARGET_SUM, HemDigest4,
    HemDigest5, HemJortsCachedTree, HemJortsPublicKey, HemJortsSignature,
    verify_hem_jorts_signature,
};
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
use qsag_core::preprocessing::{
    OtMesh, PartyPrivateRng, commit_and_open_spdz_goldilocks_batch_quorum,
    lagrange_weights_at_zero_goldilocks, open_and_check_degree_ext2,
    open_and_check_degree_goldilocks, shamir_share_ext2, shamir_share_goldilocks,
    validate_all_eval_points_goldilocks,
};
use qsag_core::sponge::keccak::{cshake256_32, encode_multi_frame};
use qsag_core::sponge::poseidon2::{POSEIDON2_CONST_IV, poseidon2_hash32};
use qsag_core::tsw_baggy::MonotonicEpochLatch;
use qsag_core::wipe::{ct_eq_bytes32, wipe_bytes32, wipe_ext2, wipe_goldilocks};

use crate::hash::{mac32, mac32_verify};

const HEM_QSA_ECHO_TAG: &[u8] = b"QSAG.HEM.QSA.ECHO/v1";
const HEM_QSB_SUBSHARE_COMMIT_TAG: &[u8] = b"QSAG.HEM.QSB.COMMIT/v1";
const HEM_QSB_CHALLENGE_TAG: &[u8] = b"QSAG.HEM.QSB.CHAL/v1";
const HEM_PUB_DIR_MAGIC: &[u8; 8] = b"QSAGHDIR";
const HEM_CUSTODIAN_SHARE_MAGIC: &[u8; 8] = b"QSAGHSHR";

/// Errors returned by `Hem`-compatible quorum signing, proactive refresh, or dynamic resharing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HemQuorumError {
    InvalidQuorum {
        t: usize,
        n: usize,
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

fn canonical_eval_points(n: usize) -> Vec<Goldilocks> {
    (1..=n as u64).map(Goldilocks::from_u64_reduced).collect()
}

fn validate_party_subset(indices: &[usize], min_len: usize, n: usize) -> Result<(), HemQuorumError> {
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

fn derive_leaf_prf_secret_clear(sk_prf: HemDigest4, pk_seed: HemDigest4, kp_idx: u32) -> HemDigest4 {
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
            for j in (i + 1)..n {
                let k = rng.next_bytes32();
                pair_matrix[i][j] = k;
                pair_matrix[j][i] = k;
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
                let mut prf_rem = prf_secret;
                for &member in &comm.members[..t - 1] {
                    let sh: HemDigest4 = core::array::from_fn(|_| rng.next_goldilocks());
                    for l in 0..4 {
                        prf_rem[l] -= sh[l];
                    }
                    custodians[member].leaf_prf_shares[kp] = Some(sh);
                }
                custodians[comm.members[t - 1]].leaf_prf_shares[kp] = Some(prf_rem);
                wipe_goldilocks(&mut prf_secret);

                let mut kp_endpoints = [[Goldilocks::ZERO; 4]; HEM_WOTS_CHAINS];
                let mut per_member_chains: Vec<Vec<[HemDigest4; HEM_WOTS_MAX_STEP]>> =
                    (0..t).map(|_| Vec::with_capacity(HEM_WOTS_CHAINS)).collect();

                for (r, ep_slot) in kp_endpoints.iter_mut().enumerate().take(HEM_WOTS_CHAINS) {
                    let y0 = hem_wots_base_secret_clear(sk_seed, pk_seed, 0, 0, kp as u32, r as u32);
                    let y1 = hem_wots_step_hash_injective(pk_seed, y0, 0, 0, kp as u32, r as u32, 0);
                    let y2 = hem_wots_step_hash_injective(pk_seed, y1, 0, 0, kp as u32, r as u32, 1);
                    let y3 = hem_wots_step_hash_injective(pk_seed, y2, 0, 0, kp as u32, r as u32, 2);
                    *ep_slot = y3;
                    let secret_states = [y0, y1, y2];

                    let mut member_steps = vec![[[Goldilocks::ZERO; 4]; HEM_WOTS_MAX_STEP]; t];
                    for step in 0..HEM_WOTS_MAX_STEP {
                        let mut rem = secret_states[step];
                        for m_slot in member_steps.iter_mut().take(t - 1) {
                            let sh: HemDigest4 = core::array::from_fn(|_| rng.next_goldilocks());
                            for l in 0..4 {
                                rem[l] -= sh[l];
                            }
                            m_slot[step] = sh;
                        }
                        member_steps[t - 1][step] = rem;
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
                        HEM_QSA_ECHO_TAG,
                        &self.custodians[from].pair_keys[to],
                        &binding,
                    );
                    echoes.push((from, to, tag));
                }
            }
        }
        for (from, to, tag) in &echoes {
            if !mac32_verify(
                HEM_QSA_ECHO_TAG,
                &self.custodians[*to].pair_keys[*from],
                &binding,
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

    fn burn_leaves_below(&mut self, new_high_water: usize) {
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
            Goldilocks::from_le_bytes_canonical(raw).ok_or(HemQuorumError::MalformedVaultBytes)
        };

        let party_id = read_u32(bytes, &mut pos)? as usize;
        let quorum_epoch = read_u64(bytes, &mut pos)?;
        let t = read_u32(bytes, &mut pos)? as usize;
        let n = read_u32(bytes, &mut pos)? as usize;
        if t < 2 || t > n || party_id >= n {
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
    TamperInTransit { dealer: usize, recipient: usize },
    /// Dealer `dealer` commits consistently in Round 1 to shares that have degree `>= new_t`.
    CorruptPolynomialDegree { dealer: usize },
    /// Dealer `dealer` commits to a valid degree-`< new_t` polynomial with shifted constant term.
    ShiftConstantTerm { dealer: usize },
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

/// Mode `QS-B` Dynamic `(t, n)` Shamir Quorum for `Hem` `JortsPoseidon2` supporting:
/// - Threshold signing (`sign_quorum`) emitting canonical 4,328-byte [`HemJortsSignature`]s,
/// - Zero-constant proactive share refresh (`proactive_refresh` / `Π_refresh`),
/// - Dynamic `(t, n) -> (t', n')` threshold & roster switching (`reshare_quorum` / `Π_reshare`)
///   preserving the exact 65-byte validator public key and monotone leaf high-water mark.
