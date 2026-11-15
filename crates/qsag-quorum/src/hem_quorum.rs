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
pub struct HemDynamicShamirQuorum {
    quorum_epoch: u64,
    t: usize,
    n: usize,
    high_water_leaf: usize,
    public_dir: HemQuorumPublicDirectory,
    latch_cluster: QuorumEpochLatchCluster,
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
        if t < 2 || t > n || n > 64 {
            return Err(HemQuorumError::InvalidQuorum { t, n });
        }
        if active_leaves == 0 || active_leaves > HEM_JORTS_MAX_LEAVES {
            return Err(HemQuorumError::InvalidActiveLeaves { active_leaves });
        }

        let eval_points = canonical_eval_points(n);
        validate_all_eval_points_goldilocks(&eval_points)
            .map_err(Poseidon2MpcError::Preprocess)?;

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
        let latch_cluster = QuorumEpochLatchCluster::establish(n, t, 0, &mut latch_rngs)?;

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
    pub fn latch_authority(&self) -> &EpochLatchAuthorityPublic {
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
            QuorumEpochLatchCluster::establish(n, t, high_water_leaf as u64, &mut latch_rngs)?;
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
    pub fn sign_quorum(
        &mut self,
        signer_indices: &[usize],
        latch_ackers: &[usize],
        msg: &[u8],
    ) -> Result<(u64, HemJortsSignature), HemQuorumError> {
        validate_party_subset(signer_indices, self.t, self.n)?;
        validate_party_subset(latch_ackers, 1, self.n)?;
        if self.high_water_leaf >= self.public_dir.active_leaves {
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
        let latch_pk = self.public_dir.pk.latch_pq_public_key(self.public_dir.dkg_pk_seed);
        let cert = self
            .latch_cluster
            .certify_epoch(
                latch_ackers,
                &latch_pk,
                HEM_JORTS_XMSS_HEIGHT as u32,
                &mu_bytes,
            )
            .map_err(|_| HemQuorumError::LatchRefused)?;

        let signer_refs: Vec<&HemShamirCustodianShare> =
            signer_indices.iter().map(|&p| &self.shares[p]).collect();
        let sig = sign_from_shamir_share_slice(
            &self.public_dir,
            self.latch_cluster.authority_public(),
            self.quorum_epoch,
            self.t,
            self.n,
            &cert,
            msg,
            &signer_refs,
        )?;

        let used_leaf = cert.epoch() as usize;
        self.high_water_leaf = used_leaf + 1;
        for sh in &mut self.shares {
            sh.burn_leaves_below(self.high_water_leaf);
        }
        Ok((cert.epoch(), sig))
    }

    /// Proactive share refresh (`Π_refresh`): adds fresh zero-constant degree-`< t` polynomials to
    /// all unspent leaf shares, MAC shares, and `alpha_share`, verifies Round-1 commitments,
    /// HVZK degree `< t`, and SPDZ `MacCheck`, bumps `quorum_epoch`, and preserves the exact
    /// 65-byte validator public key.
    pub fn proactive_refresh(&mut self, session_id: [u8; 32]) -> Result<(), HemQuorumError> {
        let all_parties: Vec<usize> = (0..self.n).collect();
        self.reshare_quorum_with_fault(
            session_id,
            &all_parties[..self.t],
            self.t,
            self.n,
            ReshareFaultInjection::None,
        )
    }

    /// Dynamic `(t, n) -> (t', n')` quorum-switching (`Π_reshare`): transitions custody from
    /// `old_quorum_indices` (`>= t` custodians) to a fresh `(new_t, new_n)` threshold and roster
    /// WITHOUT changing the validator's 65-byte [`HemJortsPublicKey`].
    pub fn reshare_quorum(
        &mut self,
        session_id: [u8; 32],
        old_quorum_indices: &[usize],
        new_t: usize,
        new_n: usize,
    ) -> Result<(), HemQuorumError> {
        self.reshare_quorum_with_fault(
            session_id,
            old_quorum_indices,
            new_t,
            new_n,
            ReshareFaultInjection::None,
        )
    }

    /// Fault-injectable entry point for adversarial verification of `Π_reshare` / `Π_refresh`.
    pub fn reshare_quorum_with_fault(
        &mut self,
        session_id: [u8; 32],
        old_quorum_indices: &[usize],
        new_t: usize,
        new_n: usize,
        fault: ReshareFaultInjection,
    ) -> Result<(), HemQuorumError> {
        if new_t < 2 || new_t > new_n || new_n > 64 {
            return Err(HemQuorumError::InvalidQuorum { t: new_t, n: new_n });
        }
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
        let lambdas = lagrange_weights_at_zero_goldilocks(&old_pts)
            .map_err(Poseidon2MpcError::Preprocess)?;
        let new_pts = canonical_eval_points(new_n);
        validate_all_eval_points_goldilocks(&new_pts).map_err(Poseidon2MpcError::Preprocess)?;

        let unspent_leaves = self.public_dir.active_leaves.saturating_sub(self.high_water_leaf);
        let total_scalars = unspent_leaves * HEM_LEAF_SCALARS;

        // Round 1: Each old custodian `d_slot` deals weighted degree-`< new_t` sub-shares + HVZK
        // blinding evaluations `mask_eval` to `0..new_n` and broadcasts Poseidon2 commitments.
        let mut sub_alpha = vec![vec![GoldilocksExt2::ZERO; new_n]; self.t];
        let mut sub_mask = vec![vec![GoldilocksExt2::ZERO; new_n]; self.t];
        let mut sub_vals = vec![vec![vec![Goldilocks::ZERO; total_scalars]; new_n]; self.t];
        let mut sub_macs = vec![vec![vec![GoldilocksExt2::ZERO; total_scalars]; new_n]; self.t];
        let mut round1_commits = vec![vec![[0u8; 32]; new_n]; self.t];

        for (d_slot, &old_p) in active_old.iter().enumerate() {
            let lam = lambdas[d_slot];
            let seed = cshake256_32(
                b"QSAG.HEM.QSB.DEALER.RNG/v1",
                &encode_multi_frame(&[
                    &session_id,
                    &self.quorum_epoch.to_le_bytes(),
                    &(old_p as u32).to_le_bytes(),
                ]),
            );
            let mut d_rng = PartyPrivateRng::from_seed(seed, b"QSAG.HEM.QSB.DEALER.STREAM/v1");

            // Preserve `alpha` across reshare (`sum_i lam_i * alpha_share_i == alpha`) with fresh polynomial
            let weighted_alpha = self.shares[old_p].alpha_share.mul_base(lam);
            sub_alpha[d_slot] = shamir_share_ext2(new_t, &new_pts, weighted_alpha, &mut d_rng);

            let mask_secret = d_rng.next_ext2();
            sub_mask[d_slot] = shamir_share_ext2(new_t, &new_pts, mask_secret, &mut d_rng);

            let mut flat_idx = 0usize;
            for kp in self.high_water_leaf..self.public_dir.active_leaves {
                for s_idx in 0..HEM_LEAF_SCALARS {
                    let mut w_val = lam * self.shares[old_p].leaf_vals[kp][s_idx];
                    if matches!(fault, ReshareFaultInjection::ShiftConstantTerm { dealer } if dealer == d_slot)
                        && flat_idx == 0
                    {
                        w_val += Goldilocks::ONE;
                    }
                    let w_mac = self.shares[old_p].leaf_macs[kp][s_idx].mul_base(lam);
                    let v_poly = shamir_share_goldilocks(new_t, &new_pts, w_val, &mut d_rng);
                    let m_poly = shamir_share_ext2(new_t, &new_pts, w_mac, &mut d_rng);
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
            let mut z_evals = Vec::with_capacity(new_n);
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
        let mut new_alpha_shares = vec![GoldilocksExt2::ZERO; new_n];
        let mut new_flat_vals = vec![vec![Goldilocks::ZERO; total_scalars]; new_n];
        let mut new_flat_macs = vec![vec![GoldilocksExt2::ZERO; total_scalars]; new_n];
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
        }

        // Round 2C: SPDZ Constant-Term Preservation `MacCheck` over `GoldilocksExt2`!
        // Checks `\sum_k gamma_k * (alpha * val'_k - mac'_k) == 0` via zero-masked Shamir opening
        // AND checks `leaf[high_water_leaf]` / `prf_commits[high_water_leaf]` if unspent leaves remain!
        if total_scalars > 0 {
            // Publicly open nothing secret: combine random linear combination with zero-share mask!
            // First verify via `commit_and_open_spdz_goldilocks_batch_quorum` on the unspent leaf's
            // public `y^(3)` endpoint or a zero-value check wire, AND verify constant-term integrity
            // by checking the random linear combination `sigma_j = sum_k rho_k * mac'_k - alpha_j * V`
            // after masking `V` with a dealerless random authenticated wire? Wait: even simpler and
            // 100% zero-knowledge!
            // If `unspent_leaves > 0`, let's check BOTH:
            // 1) Every unspent leaf's `prf_commit[kp]` & `endpoints[kp]`? No, opening `prf` or `y^(0..2)`
            //    would reveal them! Instead, how does SPDZ verify `[val'_k], [mac'_k]` WITHOUT opening
            //    `val'_k`? Generate ONE random shared mask `(r_val, r_mac = alpha * r_val)` from the
            //    old quorum during Round 1, open `U = r_val + sum_k beta_k * val'_k` (`1` scalar,
            //    completely masked by `r_val`!), and check that `r_mac + sum_k beta_k * mac'_k - alpha * U == 0`!
            let mut mask_v_new = vec![Goldilocks::ZERO; new_n];
            let mut mask_m_new = vec![GoldilocksExt2::ZERO; new_n];
            for (d_slot, &old_p) in active_old.iter().enumerate() {
                let lam = lambdas[d_slot];
                // Each old party contributes `lam_i * leaf_vals[hw][0]`? No — that's not independent!
                // Wait: in Round 1, old party `old_p` holds `alpha_share_i` (not `alpha`), so to mask
                // without OLE we can run `commit_and_open_spdz_goldilocks_batch_quorum` on a zero wire
                // OR run `OtMesh` Gilboa OLE, OR notice:
                // Let's run `OtMesh::establish_ring_lwe_dealerless`? Wait: Ring-LWE OLE for ONE scalar
                // `r` across `new_n` parties is ONLY `1` scalar (`< 2 ms`!) OR even faster:
                // Let's check! How long does `spdz_authenticate_goldilocks_batch_ext2` for `1` scalar take?
                // Wait: in `spdz_authenticate_goldilocks_batch_ext2`, `alpha_contribs` are additive!
                // Look at `alpha_shares` on `new_pts`: each new party `j` can convert its Shamir share
                // `new_alpha_shares[j]` on `0..new_t` into an additive share `alpha_add[j] = mu_j * new_alpha_shares[j]`!
                let _ = (lam, old_p, &mut mask_v_new, &mut mask_m_new);
            }

            let check_quorum = new_t;
            let check_pts = &new_pts[..check_quorum];
            let check_lambdas = lagrange_weights_at_zero_goldilocks(check_pts)
                .map_err(Poseidon2MpcError::Preprocess)?;
            let alpha_contribs: Vec<GoldilocksExt2> = (0..check_quorum)
                .map(|j| new_alpha_shares[j].mul_base(check_lambdas[j]))
                .collect();

            let mut check_rngs: Vec<PartyPrivateRng> = (0..check_quorum)
                .map(|j| {
                    PartyPrivateRng::from_seed(
                        cshake256_32(
                            b"QSAG.HEM.QSB.MACCHK.RNG/v1",
                            &encode_multi_frame(&[&session_id, &(j as u32).to_le_bytes()]),
                        ),
                        b"QSAG.HEM.QSB.MACCHK.STREAM/v1",
                    )
                })
                .collect();
            let mut mesh = OtMesh::establish(
                cshake256_32(b"QSAG.HEM.QSB.MACCHK.OT/v1", &session_id),
                &mut check_rngs,
            )
            .map_err(Poseidon2MpcError::Preprocess)?;
            // Generate 1 random scalar `r = sum_j r_j` and authenticate it under `alpha` via Gilboa OLE!
            let r_inputs: Vec<Vec<Goldilocks>> = (0..check_quorum)
                .map(|j| {
                    let rj = check_rngs[j].next_goldilocks();
                    shamir_share_goldilocks(check_quorum, check_pts, rj, &mut check_rngs[j])
                })
                .collect();
            let mut r_sh = vec![Goldilocks::ZERO; check_quorum];
            for r_row in &r_inputs {
                for j in 0..check_quorum {
                    r_sh[j] += r_row[j];
                }
            }
            let r_batch: Vec<Vec<Goldilocks>> = r_sh.iter().map(|&x| vec![x]).collect();
            let r_macs = qsag_core::preprocessing::spdz_authenticate_goldilocks_batch_ext2(
                &cshake256_32(b"QSAG.HEM.QSB.MACCHK.AUTH/v1", &session_id),
                check_quorum,
                check_pts,
                &mut mesh,
                &alpha_contribs,
                &new_alpha_shares[..check_quorum],
                &r_batch,
                &mut check_rngs,
            )
            .map_err(|_| HemQuorumError::ReshareMacCheckFailed)?;

            // Squeeze `total_scalars` base-field weights `beta_k` and open ONLY the single masked
            // scalar `U = r + sum_k beta_k * val'_k` behind `commit_and_open_spdz_goldilocks_batch_quorum`!
            let mut betas = Vec::with_capacity(total_scalars);
            for _ in 0..total_scalars {
                betas.push(chal_rng.next_goldilocks());
            }
            let mut masked_sh = vec![vec![Goldilocks::ZERO; 1]; check_quorum];
            let mut masked_mac = vec![vec![GoldilocksExt2::ZERO; 1]; check_quorum];
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
                check_quorum,
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

        // All checks passed! Permanently wipe & invalidate ALL old `(t, n)` custodian shares.
        for old_sh in &mut self.shares {
            old_sh.invalidate_and_wipe();
        }

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

        let mut latch_rngs: Vec<PartyPrivateRng> = (0..new_n)
            .map(|j| {
                PartyPrivateRng::from_seed(
                    cshake256_32(
                        b"QSAG.HEM.QSB.NEW.LATCH/v1",
                        &encode_multi_frame(&[
                            &session_id,
                            &next_quorum_epoch.to_le_bytes(),
                            &(j as u32).to_le_bytes(),
                        ]),
                    ),
                    b"QSAG.HEM.QSB.NEW.LATCH.STREAM/v1",
                )
            })
            .collect();
        let new_cluster =
            QuorumEpochLatchCluster::establish(new_n, new_t, hw as u64, &mut latch_rngs)?;

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
    latch_authority: &EpochLatchAuthorityPublic,
    expected_quorum_epoch: u64,
    t: usize,
    n: usize,
    latch_cert: &EpochLatchCertificate,
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
    latch_cluster: QuorumEpochLatchCluster,
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

impl HemSpdzSeedQuorum {
    /// Run a 100% dealerless Goldilocks DKG + native `[Goldilocks; 4]` SPDZ MPC key generation.
    pub fn keygen_dealerless(
        session_id: [u8; 32],
        t: usize,
        n: usize,
        active_leaves: usize,
    ) -> Result<Self, HemQuorumError> {
        if t < 2 || t > n || n > 16 {
            return Err(HemQuorumError::InvalidQuorum { t, n });
        }
        let budget = required_hem_jorts_keygen_preprocessing_budget(active_leaves)?;
        let pts = canonical_eval_points(n);
        let mut rngs: Vec<PartyPrivateRng> = (0..n)
            .map(|p| {
                PartyPrivateRng::from_seed(
                    cshake256_32(
                        b"QSAG.HEM.SPDZ.RNG/v1",
                        &encode_multi_frame(&[&session_id, &(p as u32).to_le_bytes()]),
                    ),
                    b"QSAG.HEM.SPDZ.RNG.STREAM/v1",
                )
            })
            .collect();
        let mut mesh = OtMesh::establish(
            cshake256_32(b"QSAG.HEM.SPDZ.OT/v1", &session_id),
            &mut rngs,
        )
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

        let (mut key_shares, mut vaults) = authenticate_poseidon_dkg_shares_and_preprocess(
            cshake256_32(b"QSAG.HEM.SPDZ.KEYGEN.PREP/v1", &session_id),
            t,
            &pts,
            pk_seed,
            &sk_seed_shares,
            &sk_prf_shares,
            budget.0,
            0,
            0,
            &mut mesh,
            &mut rngs,
        )?;
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
        let latch_cluster = QuorumEpochLatchCluster::establish(n, t, 0, &mut rngs)?;

        Ok(Self {
            quorum_epoch: 0,
            t,
            n,
            high_water_leaf: 0,
            cache,
            latch_cluster,
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

    /// Proactive bit-level refresh (`run_dealerless_refresh_seed32_goldilocks`) preserving `pk`.
    pub fn proactive_refresh(&mut self, session_id: [u8; 32]) -> Result<(), HemQuorumError> {
        let pts = canonical_eval_points(self.n);
        let mut rngs: Vec<PartyPrivateRng> = (0..self.n)
            .map(|p| {
                PartyPrivateRng::from_seed(
                    cshake256_32(
                        b"QSAG.HEM.SPDZ.REF.RNG/v1",
                        &encode_multi_frame(&[&session_id, &(p as u32).to_le_bytes()]),
                    ),
                    b"QSAG.HEM.SPDZ.REF.STREAM/v1",
                )
            })
            .collect();
        let mut mesh = OtMesh::establish(
            cshake256_32(b"QSAG.HEM.SPDZ.REF.OT/v1", &session_id),
            &mut rngs,
        )
        .map_err(Poseidon2MpcError::Preprocess)?;

        run_dealerless_refresh_seed32_goldilocks(
            cshake256_32(b"QSAG.HEM.SPDZ.REF.SEED/v1", &session_id),
            self.t,
            &pts,
            &mut self.sk_seed_shares,
            &mut mesh,
            &mut rngs,
        )?;
        run_dealerless_refresh_seed32_goldilocks(
            cshake256_32(b"QSAG.HEM.SPDZ.REF.PRF/v1", &session_id),
            self.t,
            &pts,
            &mut self.sk_prf_shares,
            &mut mesh,
            &mut rngs,
        )?;
        self.quorum_epoch += 1;
        Ok(())
    }

    /// Dynamic `(t, n) -> (new_t, new_n)` seed resharing (`run_dealerless_reshare_seed32_goldilocks`)
    /// verified in SPDZ MPC via `verify_reshared_hem_jorts_key_mpc` without reconstructing secrets!
    pub fn reshare_quorum(
        &mut self,
        session_id: [u8; 32],
        old_quorum_indices: &[usize],
        new_t: usize,
        new_n: usize,
    ) -> Result<(), HemQuorumError> {
        if new_t < 2 || new_t > new_n || new_n > 16 {
            return Err(HemQuorumError::InvalidQuorum { t: new_t, n: new_n });
        }
        validate_party_subset(old_quorum_indices, self.t, self.n)?;
        let active_old = &old_quorum_indices[..self.t];
        let new_pts = canonical_eval_points(new_n);

        let mut old_rngs: Vec<PartyPrivateRng> = (0..self.t)
            .map(|i| {
                PartyPrivateRng::from_seed(
                    cshake256_32(
                        b"QSAG.HEM.SPDZ.RESHARE.OLD/v1",
                        &encode_multi_frame(&[&session_id, &(i as u32).to_le_bytes()]),
                    ),
                    b"QSAG.HEM.SPDZ.RESHARE.OLD.STREAM/v1",
                )
            })
            .collect();
        let mut new_rngs: Vec<PartyPrivateRng> = (0..new_n)
            .map(|j| {
                PartyPrivateRng::from_seed(
                    cshake256_32(
                        b"QSAG.HEM.SPDZ.RESHARE.NEW/v1",
                        &encode_multi_frame(&[&session_id, &(j as u32).to_le_bytes()]),
                    ),
                    b"QSAG.HEM.SPDZ.RESHARE.NEW.STREAM/v1",
                )
            })
            .collect();
        let mut new_mesh = OtMesh::establish(
            cshake256_32(b"QSAG.HEM.SPDZ.RESHARE.OT/v1", &session_id),
            &mut new_rngs,
        )
        .map_err(Poseidon2MpcError::Preprocess)?;

        let mut old_seed_vec: Vec<ShamirPoseidonSeedShare> = active_old
            .iter()
            .map(|&p| self.sk_seed_shares[p].clone())
            .collect();
        let mut old_prf_vec: Vec<ShamirPoseidonSeedShare> = active_old
            .iter()
            .map(|&p| self.sk_prf_shares[p].clone())
            .collect();
        let mut old_seed_refs: Vec<&mut ShamirPoseidonSeedShare> =
            old_seed_vec.iter_mut().collect();
        let mut old_prf_refs: Vec<&mut ShamirPoseidonSeedShare> = old_prf_vec.iter_mut().collect();

        let new_seed_shares = run_dealerless_reshare_seed32_goldilocks(
            cshake256_32(b"QSAG.HEM.SPDZ.RESHARE.S/v1", &session_id),
            self.t,
            &mut old_seed_refs,
            new_t,
            &new_pts,
            &mut new_mesh,
            &mut old_rngs,
            &mut new_rngs,
            |_, _| Ok(()),
        )?;
        let new_prf_shares = run_dealerless_reshare_seed32_goldilocks(
            cshake256_32(b"QSAG.HEM.SPDZ.RESHARE.P/v1", &session_id),
            self.t,
            &mut old_prf_refs,
            new_t,
            &new_pts,
            &mut new_mesh,
            &mut old_rngs,
            &mut new_rngs,
            |_, _| Ok(()),
        )?;

        let verify_budget = required_hem_jorts_reshare_verify_preprocessing_budget();
        let (mut new_ks, mut new_vaults) = authenticate_poseidon_dkg_shares_and_preprocess(
            cshake256_32(b"QSAG.HEM.SPDZ.RESHARE.VPREP/v1", &session_id),
            new_t,
            &new_pts,
            self.cache.dkg_pk_seed,
            &new_seed_shares,
            &new_prf_shares,
            verify_budget.0,
            0,
            0,
            &mut new_mesh,
            &mut new_rngs,
        )?;
        {
            let mut ks_refs: Vec<_> = new_ks[..new_t].iter_mut().collect();
            let mut v_refs: Vec<_> = new_vaults[..new_t].iter_mut().collect();
            verify_reshared_hem_jorts_key_mpc(
                cshake256_32(b"QSAG.HEM.SPDZ.RESHARE.VCHK/v1", &session_id),
                &self.cache,
                new_t,
                &mut ks_refs,
                &mut v_refs,
                &mut new_rngs[..new_t],
            )?;
        }

        // Wipe all old shares before installing new `(new_t, new_n)` shares
        for sh in &mut self.sk_seed_shares {
            sh.poison_and_wipe();
        }
        for sh in &mut self.sk_prf_shares {
            sh.poison_and_wipe();
        }
        let new_cluster = QuorumEpochLatchCluster::establish(
            new_n,
            new_t,
            self.high_water_leaf,
            &mut new_rngs,
        )?;

        self.quorum_epoch += 1;
        self.t = new_t;
        self.n = new_n;
        self.latch_cluster = new_cluster;
        self.sk_seed_shares = new_seed_shares;
        self.sk_prf_shares = new_prf_shares;
        Ok(())
    }

    /// Sign `msg` in native `[Goldilocks; 4]` SPDZ MPC (`0` intermediate A2B!) across
    /// `signer_indices` (`>= t` custodians).
    pub fn sign_quorum(
        &mut self,
        session_id: [u8; 32],
        signer_indices: &[usize],
        latch_ackers: &[usize],
        msg: &[u8],
    ) -> Result<(u64, HemJortsSignature), HemQuorumError> {
        validate_party_subset(signer_indices, self.t, self.n)?;
        validate_party_subset(latch_ackers, 1, self.n)?;
        let pts = canonical_eval_points(self.n);
        let sign_budget = required_hem_jorts_sign_preprocessing_budget_cached();

        let mut rngs: Vec<PartyPrivateRng> = (0..self.n)
            .map(|p| {
                PartyPrivateRng::from_seed(
                    cshake256_32(
                        b"QSAG.HEM.SPDZ.SIGN.RNG/v1",
                        &encode_multi_frame(&[&session_id, &(p as u32).to_le_bytes()]),
                    ),
                    b"QSAG.HEM.SPDZ.SIGN.STREAM/v1",
                )
            })
            .collect();
        let mut mesh = OtMesh::establish(
            cshake256_32(b"QSAG.HEM.SPDZ.SIGN.OT/v1", &session_id),
            &mut rngs,
        )
        .map_err(Poseidon2MpcError::Preprocess)?;

        let (mut key_shares, mut vaults) = authenticate_poseidon_dkg_shares_and_preprocess(
            cshake256_32(b"QSAG.HEM.SPDZ.SIGN.PREP/v1", &session_id),
            self.t,
            &pts,
            self.cache.dkg_pk_seed,
            &self.sk_seed_shares,
            &self.sk_prf_shares,
            sign_budget.0,
            0,
            0,
            &mut mesh,
            &mut rngs,
        )?;
        for ks in &mut key_shares {
            ks.enroll_hem_key_profile(self.cache.pk, self.cache.prf_check)?;
            ks.enroll_latch_authority(self.latch_cluster.authority_public().clone())?;
        }

        let (mu_bytes, _) = hem_compute_message_mu(&self.cache.pk, msg);
        let latch_pk = self.cache.pk.latch_pq_public_key(self.cache.dkg_pk_seed);
        let cert = self
            .latch_cluster
            .certify_epoch(
                latch_ackers,
                &latch_pk,
                HEM_JORTS_XMSS_HEIGHT as u32,
                &mu_bytes,
            )
            .map_err(|_| HemQuorumError::LatchRefused)?;

        let active_signers = &signer_indices[..self.t];
        let mut sel_ks: Vec<Option<_>> = key_shares.into_iter().map(Some).collect();
        let mut sel_vs: Vec<Option<_>> = vaults.into_iter().map(Some).collect();
        let mut sel_rngs: Vec<Option<_>> = rngs.into_iter().map(Some).collect();

        let mut ks_vec = Vec::with_capacity(self.t);
        let mut v_vec = Vec::with_capacity(self.t);
        let mut r_vec = Vec::with_capacity(self.t);
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
        let mut latches: Vec<MonotonicEpochLatch> = (0..self.t)
            .map(|_| MonotonicEpochLatch::new(self.high_water_leaf))
            .collect();

        let mut ks_refs: Vec<_> = ks_vec.iter_mut().collect();
        let mut v_refs: Vec<_> = v_vec.iter_mut().collect();
        let mut l_refs: Vec<_> = latches.iter_mut().collect();
        let (ep, sig) = sign_hem_jorts_poseidon2_mpc_cached(
            cshake256_32(b"QSAG.HEM.SPDZ.SIGN.ONLINE/v1", &session_id),
            &self.cache,
            self.t,
            Some(&cert),
            &mut l_refs,
            msg,
            100_000,
            &mut ks_refs,
            &mut v_refs,
            &mut r_vec,
        )?;
        self.high_water_leaf = ep + 1;
        Ok((ep, sig))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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
    fn e2e_dynamic_quorum_switch_2of3_to_3of5_aggregates_in_hem_bciks_qrom128() {
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
        qsb.reshare_quorum([0x22; 32], &[1, 2], 3, 5).unwrap();
        assert_eq!(qsb.public_key(), pk0_initial);
        assert_eq!(qsb.threshold_and_size(), (3, 5));
        assert_eq!(qsb.quorum_epoch(), 1);
        assert_eq!(qsb.high_water_leaf(), 1);

        // Proactive refresh Π_refresh on (3, 5) -> pubkey still bit-for-bit identical!
        qsb.proactive_refresh([0x33; 32]).unwrap();
        assert_eq!(qsb.public_key(), pk0_initial);
        assert_eq!(qsb.quorum_epoch(), 2);

        // 2. Validator 1: QS-A Committee-Partitioned Quorum (2-of-3)
        let mut qsa = HemCommitteePartitionedQuorum::stage([0x44; 32], 2, 3, 4).unwrap();
        let agg_pk1 =
            ValidatorPublicKey::from_bytes_canonical(&qsa.public_key().to_bytes()).unwrap();

        // 3. Validator 2: Standard single-custodian `ValidatorKeypair` (`JortsPoseidon2`)
        let mut v2_kp = ValidatorKeypair::keygen_deterministic(
            AggSigProfile::JortsPoseidon2,
            &[0x55; 32],
            2,
        );
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

        assert!(verify_individual_signature(&agg_pk0, block_msg, &agg_sig_qsb));
        assert!(verify_individual_signature(&agg_pk1, block_msg, &agg_sig_qsa));
        assert!(verify_individual_signature(&agg_pk2, block_msg, &sig_v2));

        // 4. Untrusted public `Hem` aggregator proves & verifies under `BciksJohnsonQrom128`!
        let committee_pks = vec![agg_pk0, agg_pk1, agg_pk2];
        let mut bitmap = SignerBitmap::new(3);
        bitmap.set(0);
        bitmap.set(1);
        bitmap.set(2);
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
                ReshareFaultInjection::ShiftConstantTerm { dealer: 1 },
            ),
            Err(HemQuorumError::ReshareMacCheckFailed)
        ));

        // Genuine reshare (2, 3) -> (3, 5) succeeds!
        qsb.reshare_quorum([0x85; 32], &[0, 2], 3, 5).unwrap();
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
        qsb.proactive_refresh([0x86; 32]).unwrap();
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
}
