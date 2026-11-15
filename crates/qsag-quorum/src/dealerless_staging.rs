//! Dealerless distributed MPC subtree staging and proactive share refresh for
//! quorum-switching `Jorts` (`QS-A` [`CommitteePartitionedJorts`] and `QS-B` [`BftShamirJorts`]).
//!
//! Replaces centralized single-seed staging (`stage_committee_partitioned`, `stage_bft_shamir`)
//! in deployments with active multi-party protocols:
//!
//! 1. **Mode `QS-A` ([`stage_committee_partitioned_dealerless_mpc`]):**
//!    - All `n` custodians run a 2-round commit-then-open coin toss (`TAG_STAGE_PK_SEED`) to
//!      derive `pk_seed` and pairwise commit-then-open ceremonies (`TAG_PAIR_KEY`) to establish
//!      symmetric channel MAC keys, aborting on any commitment mismatch.
//!    - For each `t`-member committee `C`, **only** the `t` members of `C` sample local uniform
//!      256-bit shares `y_i^(0)` (`0` communication for `y^(0)`) and evaluate the three tweaked
//!      `SHAKE256` steps `y^(0) -> y^(1) -> y^(2) -> y^(3)` across all `128 * leaves_per_committee`
//!      chains via authenticated binary `GF(2)` Subfield-SPDZ MPC (post-quantum Ring-LWE Base OTs
//!      via [`OtMesh`], KOS15 correlated OT extension, 16-round `GF(2^128)` inner-product triple
//!      sacrifice, post-sacrifice `2 -> 1` combiner, and committed SPDZ `MacCheck`).
//!    - Secret chain states `y^(0), y^(1), y^(2)` remain strictly `t`-of-`t` XOR-shared inside `C`
//!      and are never reconstructed on any host; **only** `y^(3)` is opened after `MacCheck`
//!      accepts, and all `n` custodians deterministically assemble and cross-verify `pk_root`.
//!
//! 2. **Mode `QS-B` ([`stage_bft_shamir_dealerless_mpc`]):**
//!    - All `n` custodians (`n >= 3f + 1`) run the 2-round `pk_seed` coin toss, pairwise MAC key
//!      agreement, and dealerless degree-`f` 64-way bitsliced chain-start DKG (`y^(0)` is the XOR
//!      of all `n` custodians' Boolean-verified contributions; no `sk_seed` ever exists).
//!    - Custodians evaluate `y^(0) -> y^(1) -> y^(2) -> y^(3)` in batched 64-way bitsliced
//!      `Keccak-f[1600]` over `GF(2^8)` (`TowerGf256`), verify every input bit (`x^2 + x = 0`) and
//!      every `Chi` multiplication gate via 16 independent HVZK Reed-Solomon degree-`<= 2f`
//!      zero-constant checks (`< 2^{-128}` soundness) **before** opening `y^(3)`, upgrade and
//!      re-randomize `(y^(0), y^(1), y^(2))` into independent bytewise degree-`(t - 1)` Shamir
//!      sharings via verified zero-constant polynomials, and open **only** `y^(3)`.
//!
//! 3. **Proactive Share & Channel Key Refresh ([`refresh_committee_shares`],
//!    [`refresh_bft_shamir_shares`]):**
//!    - Custodians add algebraically zero-sum `t`-of-`t` pairwise-committed XOR masks (`QS-A`) or
//!      HVZK-verified degree-`< t` zero-constant `GF(2^8)` polynomials (`QS-B`) to every staged
//!      `(y^(0), y^(1), y^(2))` table in place, wipe old share and mask bytes via volatile writes,
//!      and rotate pairwise channel MAC keys without changing `pk_root`.

use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;
use core::hint::black_box;

use qsag_core::belt_latch::DurableWal;
use qsag_core::field::tower::{
    BitslicedGf256x64, Tower128, TowerGf256, bs_gf256_extract_lane, bs_gf256_insert_lane,
    bs_gf256_mul_planes_ct, eval_poly_gf256, lagrange_weights_zero_gf256, wipe_gf256,
    wipe_tower128,
};
use qsag_core::preprocessing::{OtMesh, PartyPrivateRng, PreprocessError};
use qsag_core::sponge::keccak::{Cshake256Xof, KECCAK_ROUND_CONSTANTS};
use qsag_core::wipe::{SecretBuffer, ct_eq_bytes32, wipe_bytes, wipe_bytes32, wipe_u64s, wipe_u128s};

use crate::hash::{expand, h32};
use crate::quorum_jorts::{
    CommitteeCustodian, CommitteeLayout, CommitteePartyMaterial, CommitteeShareStore,
    LEAF_SHARE_NODES, Node, QuorumConfig, QuorumError, QuorumTree, ShamirCustodian,
    ShamirPartyMaterial, StagedCommitteeKeys, StagedShamirKeys, TAG_PAIR_KEY, TAG_STAGE_PK_SEED,
    WOTS_CHAINS, WOTS_STEPS, check_staging_budget, gf256_mul_ct, shamir_point,
};

#[cfg(doc)]
use crate::quorum_jorts::{BftShamirJorts, CommitteePartitionedJorts};

const TAG_PK_SEED_FINAL: &[u8] = b"QSAG.QUORUM.STAGE.PKSEED.FINAL/v1";
const TAG_COIN_COMMIT: &[u8] = b"QSAG.QUORUM.STAGE.COIN.COMMIT/v1";
const TAG_COIN_FINAL: &[u8] = b"QSAG.QUORUM.STAGE.COIN.FINAL/v1";
const TAG_PAIR_COMMIT: &[u8] = b"QSAG.QUORUM.STAGE.PAIR.COMMIT/v1";
const TAG_ROOT_CONFIRM: &[u8] = b"QSAG.QUORUM.STAGE.ROOT.CONFIRM/v1";
const TAG_MAC_COMMIT: &[u8] = b"QSAG.QUORUM.STAGE.MAC.COMMIT/v1";
const TAG_ABIT_COL: &[u8] = b"QSAG.QUORUM.STAGE.ABIT.COL/v1";
const TAG_ABIT_CHI: &[u8] = b"QSAG.QUORUM.STAGE.ABIT.CHI/v1";
const TAG_SAC_CHI: &[u8] = b"QSAG.QUORUM.STAGE.SAC.CHI/v1";
const TAG_SHAMIR_COMMIT: &[u8] = b"QSAG.QUORUM.STAGE.SHAMIR.COMMIT/v1";
const TAG_REFRESH_PAIR: &[u8] = b"QSAG.QUORUM.REFRESH.PAIR/v1";
const TAG_REFRESH_MASK: &[u8] = b"QSAG.QUORUM.REFRESH.MASK/v1";

/// Number of Keccak state bits (`25 * 64`).
const STATE_BITS: usize = 1600;
/// Bit offset of the 32-byte secret chain input inside the framed `TAG_CHAIN` `SHAKE256` block.
const CHAIN_INPUT_BIT_OFFSET: usize = 800;
/// Number of `u64` words per raw authenticated Boolean Beaver chunk (`2^16 = 65,536` bits).
const RAW_CHUNK_WORDS: usize = 1024;
/// Number of bits per raw authenticated Boolean Beaver chunk (`65,536`).
const RAW_CHUNK_BITS: usize = RAW_CHUNK_WORDS * 64;
/// Halving rounds folding `2^16` triples to `1` (`16`).
const HALVING_ROUNDS: usize = 16;
/// Usable leak-free `u64` words produced per chunk after `2 -> 1` combiner (`512` words).
const USABLE_CHUNK_WORDS: usize = RAW_CHUNK_WORDS / 2;
/// Number of independent `GF(2^8)` HVZK checks (`(2^{-8})^{16} = 2^{-128}` soundness).
const GF256_CHECK_REPS: usize = 16;

const KECCAK_ROTATION_OFFSETS: [u32; 25] = [
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];

/// Errors surfaced during dealerless distributed MPC staging or proactive share refresh.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DealerlessStagingError {
    /// Underlying quorum parameter or custodian error.
    Quorum(QuorumError),
    /// Underlying Ring-LWE Base-OT or KOS15 preprocessing error.
    Preprocess(PreprocessError),
    /// Caller supplied the wrong number of custodian RNGs or custodians.
    PartyCountMismatch { expected: usize, got: usize },
    /// Round-2 decommitment did not match a custodian's Round-1 commitment.
    CommitmentMismatch { phase: &'static str, party: usize },
    /// Pairwise symmetric MAC key agreement failed consistency.
    PairwiseKeyMismatch { party_a: usize, party_b: usize },
    /// KOS15 correlated-OT consistency check failed inside a committee.
    KosOtCheckFailed {
        committee: usize,
        sender: usize,
        receiver: usize,
    },
    /// Active `GF(2^128)` inner-product Beaver triple sacrifice rejected a corrupted batch.
    TripleSacrificeFailed { committee: usize },
    /// Committed SPDZ `GF(2^128)` `MacCheck` rejected a tampered wire or `y^(3)` opening.
    MacCheckFailed { committee: usize, step: usize },
    /// HVZK Shamir degree check rejected an inconsistent polynomial dealing.
    ShamirDegreeCheckFailed { phase: &'static str, dealer: usize },
    /// HVZK proactive refresh / degree-upgrade check rejected a non-zero constant term (`p(0) != 0`).
    ZeroConstantCheckFailed { dealer: usize },
    /// Post-circuit Reed-Solomon Booleanity / multiplication check rejected a corrupted gate.
    MultiplicationCheckFailed { check_idx: usize },
    /// Opened `y^(3)` Shamir shares failed Reed-Solomon degree-`<= f` consistency.
    EndpointOpeningDegreeMismatch { batch: usize },
    /// Custodians derived disagreeing Merkle public roots `pk_root`.
    PublicRootMismatch { party: usize },
}

impl From<QuorumError> for DealerlessStagingError {
    fn from(err: QuorumError) -> Self {
        Self::Quorum(err)
    }
}

impl From<PreprocessError> for DealerlessStagingError {
    fn from(err: PreprocessError) -> Self {
        Self::Preprocess(err)
    }
}

impl fmt::Display for DealerlessStagingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Quorum(e) => write!(f, "quorum error: {e}"),
            Self::Preprocess(e) => write!(f, "preprocessing error: {e}"),
            Self::PartyCountMismatch { expected, got } => {
                write!(f, "expected {expected} custodian participants, got {got}")
            }
            Self::CommitmentMismatch { phase, party } => {
                write!(f, "commitment mismatch in {phase} from custodian {party}")
            }
            Self::PairwiseKeyMismatch { party_a, party_b } => {
                write!(f, "pairwise key mismatch between {party_a} and {party_b}")
            }
            Self::KosOtCheckFailed {
                committee,
                sender,
                receiver,
            } => write!(
                f,
                "KOS15 OT check failed in committee {committee} ({sender} -> {receiver})"
            ),
            Self::TripleSacrificeFailed { committee } => {
                write!(f, "Beaver triple sacrifice failed in committee {committee}")
            }
            Self::MacCheckFailed { committee, step } => {
                write!(
                    f,
                    "SPDZ MAC verification failed in committee {committee} at stage {step}"
                )
            }
            Self::ShamirDegreeCheckFailed { phase, dealer } => {
                write!(f, "Shamir degree check failed in {phase} for dealer {dealer}")
            }
            Self::ZeroConstantCheckFailed { dealer } => {
                write!(
                    f,
                    "zero-constant polynomial check failed for custodian {dealer}"
                )
            }
            Self::MultiplicationCheckFailed { check_idx } => {
                write!(
                    f,
                    "active Shamir gate/Booleanity verification failed at check {check_idx}"
                )
            }
            Self::EndpointOpeningDegreeMismatch { batch } => {
                write!(
                    f,
                    "opened y^(3) shares failed degree consistency in batch {batch}"
                )
            }
            Self::PublicRootMismatch { party } => {
                write!(f, "global pk_root confirmation mismatch at custodian {party}")
            }
        }
    }
}

impl core::error::Error for DealerlessStagingError {}

/// Fault-injection hooks for adversarial unit tests.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg(test)]
pub(crate) enum StagingFault {
    /// Flip a custodian's Round-2 `pk_seed` contribution after committing.
    CorruptPkSeedOpen { party: usize },
    /// Flip a Beaver AND cross-term bit during `QS-A` triple generation.
    CorruptQsABeaverBit { committee: usize },
    /// Flip a custodian's `y^(3)` share bit during `QS-A` endpoint opening.
    CorruptQsAEndpointOpen { committee: usize, member_pos: usize },
    /// Deal a non-Boolean `GF(2^8)` element (`0x42`) as a `y^(0)` bit in `QS-B`.
    CorruptQsBNonBooleanInput { dealer: usize },
    /// Inject an additive error into a `Chi` gate share during `QS-B` circuit evaluation.
    CorruptQsBGateProduct { party: usize },
    /// Corrupt a custodian's `y^(3)` share during `QS-B` endpoint opening.
    CorruptQsBEndpointOpen { party: usize },
    /// Corrupt a custodian's Round-2 pairwise refresh seed opening in `QS-A`.
    CorruptQsARefreshOpen { committee: usize, member_pos: usize },
    /// Deal a polynomial with non-zero constant term (`p(0) != 0`) during `QS-B` refresh.
    CorruptQsBRefreshNonZeroConstant { dealer: usize },
    /// Deal inconsistent shares of degree `>= t` during `QS-B` refresh.
    CorruptQsBRefreshHighDegree { dealer: usize, target_party: usize },
}

// =============================================================================================
// 1. Two-Round Commit-Then-Open Ceremonies (`pk_seed`, Public Coins, Pairwise MAC Keys)
// =============================================================================================

/// Two-round commit-then-open coin toss for `pk_seed` under `TAG_STAGE_PK_SEED`.
fn coin_toss_pk_seed(
    session_id: &[u8; 32],
    party_rngs: &mut [PartyPrivateRng],
    #[cfg(test)] fault: Option<StagingFault>,
) -> Result<Node, DealerlessStagingError> {
    let n = party_rngs.len();
    let mut salts = SecretBuffer(vec![[0u8; 32]; n]);
    let mut contribs = SecretBuffer(vec![[0u8; 32]; n]);
    let mut commits = Vec::with_capacity(n);

    for p in 0..n {
        salts[p] = party_rngs[p].next_bytes32();
        contribs[p] = party_rngs[p].next_bytes32();
        let p_be = (p as u64).to_be_bytes();
        commits.push(h32(
            TAG_STAGE_PK_SEED,
            &[session_id, &p_be, &salts[p], &contribs[p]],
        ));
    }

    let commit_digest = h32(TAG_STAGE_PK_SEED, &[session_id, commits.as_flattened()]);

    #[cfg(test)]
    if let Some(StagingFault::CorruptPkSeedOpen { party }) = fault
        && party < n
    {
        contribs[party][0] ^= 0x01;
    }

    // Round 2: Every custodian verifies all peer commitments before deriving `pk_seed`.
    for verifier in 0..n {
        let _ = verifier;
        for p in 0..n {
            let p_be = (p as u64).to_be_bytes();
            let expected = h32(
                TAG_STAGE_PK_SEED,
                &[session_id, &p_be, &salts[p], &contribs[p]],
            );
            if !ct_eq_bytes32(&expected, &commits[p]) {
                return Err(DealerlessStagingError::CommitmentMismatch {
                    phase: "pk_seed",
                    party: p,
                });
            }
        }
    }

    let pk_seed = h32(
        TAG_PK_SEED_FINAL,
        &[session_id, &commit_digest, contribs.as_flattened()],
    );
    for s in salts.iter_mut() {
        wipe_bytes32(s);
    }
    for c in contribs.iter_mut() {
        wipe_bytes32(c);
    }
    Ok(pk_seed)
}

/// Two-round commit-then-open public challenge coin bound to `transcript_digest`.
fn coin_toss_public_seed(
    session_id: &[u8; 32],
    phase: &'static str,
    transcript_digest: &[u8; 32],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<[u8; 32], DealerlessStagingError> {
    let n = party_rngs.len();
    let mut salts = SecretBuffer(vec![[0u8; 32]; n]);
    let mut shares = SecretBuffer(vec![[0u8; 32]; n]);
    let mut commits = Vec::with_capacity(n);

    for p in 0..n {
        salts[p] = party_rngs[p].next_bytes32();
        shares[p] = party_rngs[p].next_bytes32();
        let p_be = (p as u64).to_be_bytes();
        commits.push(h32(
            TAG_COIN_COMMIT,
            &[
                session_id,
                phase.as_bytes(),
                transcript_digest,
                &p_be,
                &salts[p],
                &shares[p],
            ],
        ));
    }

    let commit_digest = h32(
        TAG_COIN_COMMIT,
        &[
            session_id,
            phase.as_bytes(),
            transcript_digest,
            commits.as_flattened(),
        ],
    );

    for p in 0..n {
        let p_be = (p as u64).to_be_bytes();
        let expected = h32(
            TAG_COIN_COMMIT,
            &[
                session_id,
                phase.as_bytes(),
                transcript_digest,
                &p_be,
                &salts[p],
                &shares[p],
            ],
        );
        if !ct_eq_bytes32(&expected, &commits[p]) {
            return Err(DealerlessStagingError::CommitmentMismatch { phase, party: p });
        }
    }

    let coin = h32(
        TAG_COIN_FINAL,
        &[
            session_id,
            phase.as_bytes(),
            transcript_digest,
            &commit_digest,
            shares.as_flattened(),
        ],
    );
    for s in salts.iter_mut() {
        wipe_bytes32(s);
    }
    for sh in shares.iter_mut() {
        wipe_bytes32(sh);
    }
    Ok(coin)
}

/// Dealerless 2-round pairwise commit-then-open symmetric MAC key agreement over private
/// pairwise channels (`a < b`), plus purely local self-keys `keys[p][p]`.
fn establish_dealerless_pairwise_mac_keys(
    session_id: &[u8; 32],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<Vec<Node>>, DealerlessStagingError> {
    let n = party_rngs.len();
    let mut keys = vec![vec![[0u8; 32]; n]; n];
    for p in 0..n {
        keys[p][p] = party_rngs[p].next_bytes32();
    }
    for a in 0..n {
        for b in (a + 1)..n {
            let a_be = (a as u64).to_be_bytes();
            let b_be = (b as u64).to_be_bytes();
            let mut salt_a = party_rngs[a].next_bytes32();
            let mut contrib_a = party_rngs[a].next_bytes32();
            let mut salt_b = party_rngs[b].next_bytes32();
            let mut contrib_b = party_rngs[b].next_bytes32();

            let com_a = h32(
                TAG_PAIR_COMMIT,
                &[session_id, &a_be, &b_be, &salt_a, &contrib_a],
            );
            let com_b = h32(
                TAG_PAIR_COMMIT,
                &[session_id, &b_be, &a_be, &salt_b, &contrib_b],
            );

            // Verify commitments on both endpoints before deriving the shared MAC key.
            let check_a = h32(
                TAG_PAIR_COMMIT,
                &[session_id, &a_be, &b_be, &salt_a, &contrib_a],
            );
            let check_b = h32(
                TAG_PAIR_COMMIT,
                &[session_id, &b_be, &a_be, &salt_b, &contrib_b],
            );
            if !ct_eq_bytes32(&com_a, &check_a) || !ct_eq_bytes32(&com_b, &check_b) {
                wipe_bytes32(&mut salt_a);
                wipe_bytes32(&mut contrib_a);
                wipe_bytes32(&mut salt_b);
                wipe_bytes32(&mut contrib_b);
                return Err(DealerlessStagingError::PairwiseKeyMismatch {
                    party_a: a,
                    party_b: b,
                });
            }

            let key_ab = h32(
                TAG_PAIR_KEY,
                &[session_id, &a_be, &b_be, &com_a, &com_b, &contrib_a, &contrib_b],
            );
            let key_ba = h32(
                TAG_PAIR_KEY,
                &[session_id, &a_be, &b_be, &com_a, &com_b, &contrib_a, &contrib_b],
            );
            wipe_bytes32(&mut salt_a);
            wipe_bytes32(&mut contrib_a);
            wipe_bytes32(&mut salt_b);
            wipe_bytes32(&mut contrib_b);
            if !ct_eq_bytes32(&key_ab, &key_ba) {
                return Err(DealerlessStagingError::PairwiseKeyMismatch {
                    party_a: a,
                    party_b: b,
                });
            }
            keys[a][b] = key_ab;
            keys[b][a] = key_ba;
        }
    }
    Ok(keys)
}

/// Cross-verify that every custodian independently derived the exact same public key root.
fn verify_global_tree_agreement(
    session_id: &[u8; 32],
    trees: &[QuorumTree],
) -> Result<(), DealerlessStagingError> {
    if trees.is_empty() {
        return Ok(());
    }
    let ref_pk = trees[0].public_key();
    let ref_tag = h32(
        TAG_ROOT_CONFIRM,
        &[session_id, &ref_pk.pk_seed, &ref_pk.root, &[ref_pk.height]],
    );
    for (p, tree) in trees.iter().enumerate().skip(1) {
        let pk = tree.public_key();
        let tag = h32(
            TAG_ROOT_CONFIRM,
            &[session_id, &pk.pk_seed, &pk.root, &[pk.height]],
        );
        if !ct_eq_bytes32(&ref_tag, &tag) {
            return Err(DealerlessStagingError::PublicRootMismatch { party: p });
        }
    }
    Ok(())
}

// =============================================================================================
// 2. Single-Block Framed `SHAKE256` (`TAG_CHAIN`) 64-Lane Bitslice Geometry
// =============================================================================================

/// Build the 1600 public `u64` bit-planes for a batch of up to 64 `(leaf, chain)` pairs at `step`,
/// leaving bits `800..1056` (`bytes 100..132`) zero so secret `input` shares XOR in cleanly.
fn build_chain_step_public_planes(
    pk_seed: &Node,
    batch_coords: &[(u64, u32)],
    step: u32,
) -> [u64; STATE_BITS] {
    let mut planes = [0u64; STATE_BITS];
    let mut blk = [0u8; 200];
    // Static invariant prefixes across all lanes in this `pk_seed` & `step` batch:
    //   0..8   = 20u64.to_be_bytes()
    //   8..28  = b"QSAG.QUORUM.CHAIN/v1"
    //   28..36 = 32u64.to_be_bytes()
    //   36..68 = pk_seed
    //   68..76 = 16u64.to_be_bytes()
    //   88..92 = step.to_be_bytes()
    //   92..100= 32u64.to_be_bytes()
    //   132    = 0x1f (SHAKE256 suffix)
    //   135    = 0x80 (rate-136 end bit)
    blk[0..8].copy_from_slice(&20u64.to_be_bytes());
    blk[8..28].copy_from_slice(b"QSAG.QUORUM.CHAIN/v1");
    blk[28..36].copy_from_slice(&32u64.to_be_bytes());
    blk[36..68].copy_from_slice(pk_seed);
    blk[68..76].copy_from_slice(&16u64.to_be_bytes());
    blk[88..92].copy_from_slice(&step.to_be_bytes());
    blk[92..100].copy_from_slice(&32u64.to_be_bytes());
    blk[132] = 0x1f;
    blk[135] = 0x80;

    for (lane, &(leaf, chain)) in batch_coords.iter().enumerate().take(64) {
        blk[76..84].copy_from_slice(&leaf.to_be_bytes());
        blk[84..88].copy_from_slice(&chain.to_be_bytes());
        for (byte_idx, &byte_val) in blk.iter().enumerate() {
            if (100..132).contains(&byte_idx) || byte_val == 0 {
                continue;
            }
            for bit in 0..8 {
                if ((byte_val >> bit) & 1) == 1 {
                    planes[8 * byte_idx + bit] |= 1u64 << lane;
                }
            }
        }
    }
    planes
}

/// Pack up to 64 32-byte `Node`s into 256 `u64` bit-planes.
fn pack_nodes_to_256_planes(nodes: &[Node]) -> [u64; 256] {
    let mut planes = [0u64; 256];
    for (lane, node) in nodes.iter().enumerate().take(64) {
        for (byte_idx, &b) in node.iter().enumerate() {
            for bit in 0..8 {
                let v = ((black_box(b) >> bit) & 1) as u64;
                planes[8 * byte_idx + bit] |= v << lane;
            }
        }
    }
    planes
}

/// Unpack `count` (`<= 64`) 32-byte `Node`s from 256 `u64` bit-planes.
fn unpack_256_planes_to_nodes(planes: &[u64; 256], count: usize) -> Vec<Node> {
    let mut out = vec![[0u8; 32]; count];
    for (lane, dst) in out.iter_mut().enumerate() {
        for byte_idx in 0..32 {
            let mut b = 0u8;
            for bit in 0..8 {
                b |= (((planes[8 * byte_idx + bit] >> lane) & 1) as u8) << bit;
            }
            dst[byte_idx] = b;
        }
    }
    out
}

// =============================================================================================
// 3. Mode `QS-A`: Committee-Isolated `GF(2)` Subfield-SPDZ Authenticated Binary MPC
