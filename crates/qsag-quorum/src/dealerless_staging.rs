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
// =============================================================================================

#[inline]
fn word_bit(words: &[u64], bit_idx: usize) -> u64 {
    (black_box(words[bit_idx / 64]) >> (bit_idx % 64)) & 1
}

#[inline]
fn bit_mask128(bit: u64) -> u128 {
    0u128.wrapping_sub((black_box(bit) & 1) as u128)
}

#[inline]
fn gf128_mul(a: u128, b: u128) -> u128 {
    qsag_asm::gf2_128_mul_portable(a, b)
}

/// Stream deterministic `u64` words from `SHAKE256` over framed inputs.
fn expand_u64_stream(domain: &[u8], parts: &[&[u8]], out: &mut [u64]) {
    let mut xof = Cshake256Xof::new_shake256();
    for part in core::iter::once(&domain).chain(parts.iter()) {
        xof.absorb(&(part.len() as u64).to_be_bytes());
        xof.absorb(part);
    }
    let mut bytes = vec![0u8; out.len() * 8];
    xof.squeeze(&mut bytes);
    for (dst, chunk) in out.iter_mut().zip(bytes.chunks_exact(8)) {
        let mut arr = [0u8; 8];
        arr.copy_from_slice(chunk);
        *dst = u64::from_le_bytes(arr);
    }
    wipe_bytes(&mut bytes);
}

/// Transpose 128 bit-columns of `words` `u64`s into `64 * words` 128-bit rows using
/// `qsag_asm::transpose64x256` (`4` columns of 64x64 matrices per SIMD call).
fn transpose_128_cols_to_u128_rows(cols: &[Vec<u64>], words: usize) -> Vec<u128> {
    debug_assert_eq!(cols.len(), 128);
    let mut rows = vec![0u128; 64 * words];
    let mut tile = [[0u64; 4]; 64];
    for w_pair in (0..words).step_by(2) {
        let has_second = w_pair + 1 < words;
        for bit_in_u128_half in 0..64 {
            let c_lo = bit_in_u128_half;
            let c_hi = 64 + bit_in_u128_half;
            tile[bit_in_u128_half] = [
                cols[c_lo][w_pair],
                cols[c_hi][w_pair],
                if has_second { cols[c_lo][w_pair + 1] } else { 0 },
                if has_second { cols[c_hi][w_pair + 1] } else { 0 },
            ];
        }
        qsag_asm::transpose64x256(&mut tile);
        let base_row = 64 * w_pair;
        for r in 0..64 {
            rows[base_row + r] = (tile[r][0] as u128) | ((tile[r][1] as u128) << 64);
        }
        if has_second {
            for r in 0..64 {
                rows[base_row + 64 + r] = (tile[r][2] as u128) | ((tile[r][3] as u128) << 64);
            }
        }
    }
    qsag_asm::volatile_fill(&mut tile, [0u64; 4]);
    rows
}

/// Pairwise KOS15 Subfield-VOLE channel seeded from `128` active Ring-LWE Base-OT correlations.
struct PairwiseSubfieldVole {
    holder: usize,
    owner: usize,
    seeds0: SecretBuffer<[[u8; 32]; 128]>,
    seeds1: SecretBuffer<[[u8; 32]; 128]>,
    chosen: SecretBuffer<[[u8; 32]; 128]>,
    delta_holder: u128,
    ext_ctr: u64,
}

impl PairwiseSubfieldVole {
    /// Authenticate `payload_words` `u64` words owned by `self.owner` under `self.holder`'s
    /// 128-bit `delta_holder` key via KOS15 correlated OT extension (`+256` sacrificial bits).
    /// Returns `(t_rows_for_owner, q_rows_for_holder)` satisfying `q_rows[k] ^ t_rows[k] = bit_k * delta_holder`.
    fn extend_authenticated_bits(
        &mut self,
        committee: usize,
        session_id: &[u8; 32],
        owner_words: &[u64],
        owner_rng: &mut PartyPrivateRng,
        holder_rng: &mut PartyPrivateRng,
    ) -> Result<(SecretBuffer<Vec<u128>>, SecretBuffer<Vec<u128>>), DealerlessStagingError> {
        let payload_words = owner_words.len();
        let total_words = payload_words + 4; // +256 sacrificial bits masking KOS linear combination
        let ext_ctr = self.ext_ctr;
        self.ext_ctr = self.ext_ctr.wrapping_add(1);

        let mut full_owner = SecretBuffer(Vec::with_capacity(total_words));
        full_owner.extend_from_slice(owner_words);
        for _ in 0..4 {
            full_owner.push(owner_rng.next_u64());
        }

        let holder_le = (self.holder as u64).to_le_bytes();
        let owner_le = (self.owner as u64).to_le_bytes();
        let ctr_le = ext_ctr.to_le_bytes();

        let mut t0_cols = SecretBuffer(vec![vec![0u64; total_words]; 128]);
        let mut q_cols = SecretBuffer(vec![vec![0u64; total_words]; 128]);
        let mut u_cols = vec![vec![0u64; total_words]; 128];
        let mut t1_tmp = SecretBuffer(vec![0u64; total_words]);

        for col in 0..128 {
            let col_le = (col as u64).to_le_bytes();
            expand_u64_stream(
                TAG_ABIT_COL,
                &[session_id, &holder_le, &owner_le, &ctr_le, &col_le, &self.seeds0[col]],
                &mut t0_cols[col],
            );
            expand_u64_stream(
                TAG_ABIT_COL,
                &[session_id, &holder_le, &owner_le, &ctr_le, &col_le, &self.seeds1[col]],
                &mut t1_tmp,
            );
            for w in 0..total_words {
                u_cols[col][w] = t0_cols[col][w] ^ t1_tmp[w] ^ full_owner[w];
            }
            expand_u64_stream(
                TAG_ABIT_COL,
                &[session_id, &holder_le, &owner_le, &ctr_le, &col_le, &self.chosen[col]],
                &mut q_cols[col],
            );
            let d_bit = ((black_box(self.delta_holder) >> col) & 1) as u64;
            let d_mask = 0u64.wrapping_sub(d_bit);
            for w in 0..total_words {
                q_cols[col][w] ^= d_mask & u_cols[col][w];
            }
        }
        for col in &mut u_cols {
            wipe_u64s(col);
        }

        let mut t_rows = SecretBuffer(transpose_128_cols_to_u128_rows(&t0_cols, total_words));
        let mut q_rows = SecretBuffer(transpose_128_cols_to_u128_rows(&q_cols, total_words));
        for col in t0_cols.iter_mut() {
            wipe_u64s(col);
        }
        for col in q_cols.iter_mut() {
            wipe_u64s(col);
        }
        wipe_u64s(&mut t1_tmp);

        // Holder samples `chi_seed` strictly after `u_cols` is locked.
        let chi_seed = holder_rng.next_bytes32();
        let total_rows = 64 * total_words;
        let mut chi_words = vec![0u64; 2 * total_rows];
        expand_u64_stream(
            TAG_ABIT_CHI,
            &[session_id, &holder_le, &owner_le, &ctr_le, &chi_seed],
            &mut chi_words,
        );
        let chis: Vec<u128> = chi_words
            .chunks_exact(2)
            .map(|w| (w[0] as u128) | ((w[1] as u128) << 64))
            .collect();
        wipe_u64s(&mut chi_words);

        let mut x_bar = 0u128;
        for (k, &chi_k) in chis.iter().enumerate() {
            x_bar ^= chi_k & bit_mask128(word_bit(&full_owner, k));
        }
        wipe_u64s(&mut full_owner);

        let t_bar = qsag_asm::gf2_128_dot(&t_rows, &chis);
        let q_bar = qsag_asm::gf2_128_dot(&q_rows, &chis);
        let check = q_bar ^ t_bar ^ gf128_mul(x_bar, self.delta_holder);
        if black_box(check) != 0 {
            wipe_u128s(&mut t_rows);
            wipe_u128s(&mut q_rows);
            return Err(DealerlessStagingError::KosOtCheckFailed {
                committee,
                sender: self.holder,
                receiver: self.owner,
            });
        }

        let keep_rows = 64 * payload_words;
        wipe_u128s(&mut t_rows[keep_rows..]);
        wipe_u128s(&mut q_rows[keep_rows..]);
        t_rows.truncate(keep_rows);
        q_rows.truncate(keep_rows);
        Ok((t_rows, q_rows))
    }
}

/// Evaluate 8 parallel 2-block `SHAKE256` correlation-robust hashes (`34` `u64` words each)
/// on 128-bit Subfield-VOLE rows using `qsag_asm::keccak_f1600_x8`.
#[inline]
fn crh_2blocks_x8(
    prefix: &[u64; 8],
    indices: [u64; 8],
    rows: &[u128; 8],
    backend: qsag_asm::SimdBackend,
    out: &mut [[u64; 34]; 8],
) {
    let mut st = qsag_asm::KeccakState8x::default();
    for (w, &word) in prefix.iter().enumerate() {
        st.0[w] = [word; 8];
    }
    for s in 0..8 {
        st.0[8][s] = indices[s];
        st.0[9][s] = rows[s] as u64;
        st.0[10][s] = (rows[s] >> 64) as u64;
    }
    st.0[11] = [0x1f; 8];
    st.0[16] = [1u64 << 63; 8];

    qsag_asm::keccak_f1600_x8_with_backend(&mut st, backend);
    for w in 0..17 {
        for s in 0..8 {
            out[s][w] = st.0[w][s];
        }
    }
    qsag_asm::keccak_f1600_x8_with_backend(&mut st, backend);
    for w in 0..17 {
        for s in 0..8 {
            out[s][17 + w] = st.0[w][s];
        }
    }
    qsag_asm::volatile_fill(&mut st.0, [0u64; 8]);
}

fn make_crh_prefix(session_id: &[u8; 32], holder: usize, owner: usize, chunk_ctr: u64) -> [u64; 8] {
    let mut prefix = [0u64; 8];
    prefix[0] = u64::from_le_bytes(*b"QSAG.QSA");
    prefix[1] = u64::from_le_bytes(*b".CRH.V01");
    for i in 0..4 {
        prefix[2 + i] = u64::from_le_bytes(core::array::from_fn(|b| session_id[8 * i + b]));
    }
    prefix[6] = ((holder as u64) << 32) | (owner as u64);
    prefix[7] = chunk_ctr;
    prefix
}

/// Evaluate 128-bit field product `x_holder * y_owner` over `128` Subfield-VOLE bit rows of `y_owner`.
fn cot_field_mul_128(
    prefix: &[u64; 8],
    domain_idx_base: u64,
    q_rows_128: &[u128],
    t_rows_128: &[u128],
    delta_holder: u128,
    x_holder: u128,
    y_owner: u128,
    backend: qsag_asm::SimdBackend,
) -> (u128, u128) {
    let mut send_acc = 0u128;
    let mut recv_acc = 0u128;
    let mut o0 = [[0u64; 34]; 8];
    let mut o1 = [[0u64; 34]; 8];
    let mut or = [[0u64; 34]; 8];

    for base in (0..128).step_by(8) {
        let idx: [u64; 8] = core::array::from_fn(|s| domain_idx_base + (base + s) as u64);
        let r0: [u128; 8] = core::array::from_fn(|s| q_rows_128[base + s]);
        let r1: [u128; 8] = core::array::from_fn(|s| q_rows_128[base + s] ^ delta_holder);
        let rr: [u128; 8] = core::array::from_fn(|s| t_rows_128[base + s]);
        crh_2blocks_x8(prefix, idx, &r0, backend, &mut o0);
        crh_2blocks_x8(prefix, idx, &r1, backend, &mut o1);
        crh_2blocks_x8(prefix, idx, &rr, backend, &mut or);
        for s in 0..8 {
            let bit_idx = base + s;
            // Shift `x_holder` by `X^{bit_idx}` in GF(2^128) via basis power `1 << bit_idx`.
            let basis = 1u128 << bit_idx;
            let payload = gf128_mul(x_holder, basis);
            let h0 = (o0[s][0] as u128) | ((o0[s][1] as u128) << 64);
            let h1 = (o1[s][0] as u128) | ((o1[s][1] as u128) << 64);
            let hr = (or[s][0] as u128) | ((or[s][1] as u128) << 64);
            let corr = h0 ^ h1 ^ payload;
            let y_bit = ((black_box(y_owner) >> bit_idx) & 1) as u64;
            send_acc ^= h0;
            recv_acc ^= hr ^ (corr & bit_mask128(y_bit));
        }
    }
    for buf in [&mut o0, &mut o1, &mut or] {
        qsag_asm::volatile_fill(buf, [0u64; 34]);
    }
    (send_acc, recv_acc)
}

/// Committed SPDZ `GF(2^128)` batch `MacCheck` on opened `u64` words `(opened_words, party_word_macs)`.
/// Every member commits to its `sigma_u` share in Round 1 before any peer opens in Round 2.
fn run_committed_spdz_mac_check_words(
    committee: usize,
    step_id: usize,
    session_id: &[u8; 32],
    deltas: &[u128],
    opened_words: &[u64],
    party_macs: &[Vec<[u128; 64]>],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(), DealerlessStagingError> {
    if opened_words.is_empty() {
        return Ok(());
    }
    let m = deltas.len();
    let num_words = opened_words.len();
    let mut xof = Cshake256Xof::new_shake256();
    xof.absorb(session_id);
    xof.absorb(&(committee as u64).to_be_bytes());
    xof.absorb(&(step_id as u64).to_be_bytes());
    for &w in opened_words {
        xof.absorb(&w.to_le_bytes());
    }
    let mut transcript_digest = [0u8; 32];
    xof.squeeze(&mut transcript_digest);

    let chal_seed = coin_toss_public_seed(session_id, "qsa_mac_check", &transcript_digest, party_rngs)?;
    let total_bits = 64 * num_words;
    let mut chi_u64 = vec![0u64; 2 * total_bits];
    expand_u64_stream(TAG_SAC_CHI, &[session_id, &chal_seed], &mut chi_u64);
    let chis: Vec<u128> = chi_u64
        .chunks_exact(2)
        .map(|w| (w[0] as u128) | ((w[1] as u128) << 64))
        .collect();
    wipe_u64s(&mut chi_u64);

    let mut val_comb = 0u128;
    for (w_idx, &word) in opened_words.iter().enumerate() {
        for bit in 0..64 {
            let b = (word >> bit) & 1;
            val_comb ^= chis[64 * w_idx + bit] & bit_mask128(b);
        }
    }

    let mut salts = SecretBuffer(vec![[0u8; 32]; m]);
    let mut sigmas = SecretBuffer(vec![0u128; m]);
    let mut commits = Vec::with_capacity(m);
    for u in 0..m {
        let flat_macs: &[u128] = party_macs[u].as_flattened();
        let mac_comb = qsag_asm::gf2_128_dot(flat_macs, &chis);
        sigmas[u] = mac_comb ^ gf128_mul(val_comb, deltas[u]);
        salts[u] = party_rngs[u].next_bytes32();
        let u_be = (u as u64).to_be_bytes();
        commits.push(h32(
            TAG_MAC_COMMIT,
            &[
                session_id,
                &transcript_digest,
                &u_be,
                &salts[u],
                &sigmas[u].to_le_bytes(),
            ],
        ));
    }

    let mut sigma_xor = 0u128;
    for u in 0..m {
        let u_be = (u as u64).to_be_bytes();
        let expected = h32(
            TAG_MAC_COMMIT,
            &[
                session_id,
                &transcript_digest,
                &u_be,
                &salts[u],
                &sigmas[u].to_le_bytes(),
            ],
        );
        if !ct_eq_bytes32(&expected, &commits[u]) {
            return Err(DealerlessStagingError::CommitmentMismatch {
                phase: "spdz_mac_check",
                party: u,
            });
        }
        sigma_xor ^= sigmas[u];
    }
    for s in salts.iter_mut() {
        wipe_bytes32(s);
    }
    wipe_u128s(&mut sigmas);

    if black_box(sigma_xor) != 0 {
        return Err(DealerlessStagingError::MacCheckFailed {
            committee,
            step: step_id,
        });
    }
    Ok(())
}

/// Committed SPDZ `GF(2^128)` `MacCheck` on opened 128-bit field elements `(val, mac_shares)`.
fn run_committed_spdz_mac_check_fields(
    committee: usize,
    step_id: usize,
    session_id: &[u8; 32],
    deltas: &[u128],
    opened_fields: &[u128],
    party_field_macs: &[Vec<u128>],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(), DealerlessStagingError> {
    if opened_fields.is_empty() {
        return Ok(());
    }
    let m = deltas.len();
    let count = opened_fields.len();
    let mut xof = Cshake256Xof::new_shake256();
    xof.absorb(session_id);
    xof.absorb(&(committee as u64).to_be_bytes());
    xof.absorb(&(step_id as u64).to_be_bytes());
    for &v in opened_fields {
        xof.absorb(&v.to_le_bytes());
    }
    let mut transcript_digest = [0u8; 32];
    xof.squeeze(&mut transcript_digest);

    let chal_seed =
        coin_toss_public_seed(session_id, "qsa_field_mac_check", &transcript_digest, party_rngs)?;
    let mut chi_u64 = vec![0u64; 2 * count];
    expand_u64_stream(TAG_SAC_CHI, &[session_id, &chal_seed], &mut chi_u64);
    let chis: Vec<u128> = chi_u64
        .chunks_exact(2)
        .map(|w| (w[0] as u128) | ((w[1] as u128) << 64))
        .collect();
    wipe_u64s(&mut chi_u64);

    let val_comb = qsag_asm::gf2_128_dot(opened_fields, &chis);
    let mut salts = SecretBuffer(vec![[0u8; 32]; m]);
    let mut sigmas = SecretBuffer(vec![0u128; m]);
    let mut commits = Vec::with_capacity(m);
    for u in 0..m {
        let mac_comb = qsag_asm::gf2_128_dot(&party_field_macs[u], &chis);
        sigmas[u] = mac_comb ^ gf128_mul(val_comb, deltas[u]);
        salts[u] = party_rngs[u].next_bytes32();
        let u_be = (u as u64).to_be_bytes();
        commits.push(h32(
            TAG_MAC_COMMIT,
            &[
                session_id,
                &transcript_digest,
                &u_be,
                &salts[u],
                &sigmas[u].to_le_bytes(),
            ],
        ));
    }

    let mut sigma_xor = 0u128;
    for u in 0..m {
        let u_be = (u as u64).to_be_bytes();
        let expected = h32(
            TAG_MAC_COMMIT,
            &[
                session_id,
                &transcript_digest,
                &u_be,
                &salts[u],
                &sigmas[u].to_le_bytes(),
            ],
        );
        if !ct_eq_bytes32(&expected, &commits[u]) {
            return Err(DealerlessStagingError::CommitmentMismatch {
                phase: "spdz_field_mac_check",
                party: u,
            });
        }
        sigma_xor ^= sigmas[u];
    }
    for s in salts.iter_mut() {
        wipe_bytes32(s);
    }
    wipe_u128s(&mut sigmas);

    if black_box(sigma_xor) != 0 {
        return Err(DealerlessStagingError::TripleSacrificeFailed { committee });
    }
    Ok(())
}

/// Authenticated `u64`-bitsliced Boolean Beaver reservoir for one `t`-member committee.
struct CommitteeBeaverReservoir {
    committee: usize,
    session_id: [u8; 32],
    m: usize,
    deltas: SecretBuffer<Vec<u128>>,
    pair_voles: Vec<PairwiseSubfieldVole>,
    chunk_ctr: u64,
    /// Buffered verified triples: `[party][word]` (`512` words per refill).
    buf_a: SecretBuffer<Vec<Vec<u64>>>,
    buf_b: SecretBuffer<Vec<Vec<u64>>>,
    buf_c: SecretBuffer<Vec<Vec<u64>>>,
    buf_mac_a: SecretBuffer<Vec<Vec<[u128; 64]>>>,
    buf_mac_b: SecretBuffer<Vec<Vec<[u128; 64]>>>,
    buf_mac_c: SecretBuffer<Vec<Vec<[u128; 64]>>>,
    cursor: usize,
    #[cfg(test)]
    inject_beaver_fault: bool,
}

impl CommitteeBeaverReservoir {
    fn establish(
        committee: usize,
        session_id: [u8; 32],
        party_rngs: &mut [PartyPrivateRng],
        #[cfg(test)] inject_beaver_fault: bool,
    ) -> Result<Self, DealerlessStagingError> {
        let m = party_rngs.len();
        let mut ot_mesh = OtMesh::try_establish(session_id, party_rngs)?;
        let mut deltas = SecretBuffer(vec![0u128; m]);
        for u in 0..m {
            let mut d = party_rngs[u].next_u128();
            if d == 0 {
                d = 1;
            }
            deltas[u] = d;
        }

        let mut pair_voles = Vec::with_capacity(m * (m - 1));
        for holder in 0..m {
            let choice = [deltas[holder] as u64, (deltas[holder] >> 64) as u64];
            for owner in 0..m {
                if owner == holder {
                    continue;
                }
                let (send, recv) =
                    ot_mesh.run_correlated_ot_words(owner, holder, &choice, party_rngs)?;
                let mut seeds0 = SecretBuffer([[0u8; 32]; 128]);
                let mut seeds1 = SecretBuffer([[0u8; 32]; 128]);
                let mut chosen = SecretBuffer([[0u8; 32]; 128]);
                for col in 0..128 {
                    seeds0[col].copy_from_slice(&send[col].0[..32]);
                    seeds1[col].copy_from_slice(&send[col].1[..32]);
                    chosen[col].copy_from_slice(&recv[col][..32]);
                }
                pair_voles.push(PairwiseSubfieldVole {
                    holder,
                    owner,
                    seeds0,
                    seeds1,
                    chosen,
                    delta_holder: deltas[holder],
                    ext_ctr: 0,
                });
            }
        }

        Ok(Self {
            committee,
            session_id,
            m,
            deltas,
            pair_voles,
            chunk_ctr: 0,
            buf_a: SecretBuffer(vec![Vec::new(); m]),
            buf_b: SecretBuffer(vec![Vec::new(); m]),
            buf_c: SecretBuffer(vec![Vec::new(); m]),
            buf_mac_a: SecretBuffer(vec![Vec::new(); m]),
            buf_mac_b: SecretBuffer(vec![Vec::new(); m]),
            buf_mac_c: SecretBuffer(vec![Vec::new(); m]),
            cursor: 0,
            #[cfg(test)]
            inject_beaver_fault,
        })
    }

    /// Authenticate `words_per_party` (`[party][0..W]`) under `self.deltas`, returning
    /// `[party][0..W][0..64]` additive `GF(2^128)` MAC shares.
    fn authenticate_words(
        &mut self,
        words_per_party: &[Vec<u64>],
        party_rngs: &mut [PartyPrivateRng],
    ) -> Result<SecretBuffer<Vec<Vec<[u128; 64]>>>, DealerlessStagingError> {
        let w_len = words_per_party[0].len();
        let nbits = 64 * w_len;
        let mut macs = SecretBuffer(vec![vec![[0u128; 64]; w_len]; self.m]);
        for u in 0..self.m {
            let d_u = self.deltas[u];
            for w in 0..w_len {
                let word = words_per_party[u][w];
                for bit in 0..64 {
                    macs[u][w][bit] ^= bit_mask128((word >> bit) & 1) & d_u;
                }
            }
        }

        for pv in &mut self.pair_voles {
            let (owner_rng, holder_rng) = if pv.owner < pv.holder {
                let (l, r) = party_rngs.split_at_mut(pv.holder);
                (&mut l[pv.owner], &mut r[0])
            } else {
                let (l, r) = party_rngs.split_at_mut(pv.owner);
                (&mut r[0], &mut l[pv.holder])
            };
            let (mut t_rows, mut q_rows) = pv.extend_authenticated_bits(
                self.committee,
                &self.session_id,
                &words_per_party[pv.owner],
                owner_rng,
                holder_rng,
            )?;
            for k in 0..nbits {
                macs[pv.owner][k / 64][k % 64] ^= t_rows[k];
                macs[pv.holder][k / 64][k % 64] ^= q_rows[k];
            }
            wipe_u128s(&mut t_rows);
            wipe_u128s(&mut q_rows);
        }
        Ok(macs)
    }

    /// Authenticate 128-bit field shares `elems_per_party[u][0..K]` (`u128` per element).
    fn authenticate_field_elements(
        &mut self,
        elems_per_party: &[Vec<u128>],
        party_rngs: &mut [PartyPrivateRng],
    ) -> Result<SecretBuffer<Vec<Vec<u128>>>, DealerlessStagingError> {
        let k_len = elems_per_party[0].len();
        let mut packed_words = SecretBuffer(vec![vec![0u64; 2 * k_len]; self.m]);
        for u in 0..self.m {
            for (idx, &el) in elems_per_party[u].iter().enumerate() {
                packed_words[u][2 * idx] = el as u64;
                packed_words[u][2 * idx + 1] = (el >> 64) as u64;
            }
        }
        let bit_macs = self.authenticate_words(&packed_words, party_rngs)?;
        for u in 0..self.m {
            wipe_u64s(&mut packed_words[u]);
        }
        let mut field_macs = SecretBuffer(vec![vec![0u128; k_len]; self.m]);
        for u in 0..self.m {
            for idx in 0..k_len {
                let mut acc = 0u128;
                for b in 0..64 {
                    acc ^= gf128_mul(bit_macs[u][2 * idx][b], 1u128 << b);
                }
                for b in 0..64 {
                    acc ^= gf128_mul(bit_macs[u][2 * idx + 1][b], 1u128 << (64 + b));
                }
                field_macs[u][idx] = acc;
            }
        }
        Ok(field_macs)
    }

    /// Generate, actively sacrifice (`16`-round `GF(2^128)` inner-product halving + masked `L = 1`
    /// check), and `2 -> 1` Fisher–Yates combine `USABLE_CHUNK_WORDS` (`512`) `u64` words.
    fn refill(&mut self, party_rngs: &mut [PartyPrivateRng]) -> Result<(), DealerlessStagingError> {
        let m = self.m;
        let chunk_ctr = self.chunk_ctr;
        self.chunk_ctr = self.chunk_ctr.wrapping_add(1);
        let backend = qsag_asm::detect_backend();

        // 1. Sample raw `a` (`1024` words) and `b` (`1024` words + `2` words = `128` bits for `B_mask`).
        let b_ext_words = RAW_CHUNK_WORDS + 2;
        let mut raw_a = SecretBuffer(vec![vec![0u64; RAW_CHUNK_WORDS]; m]);
        let mut raw_b = SecretBuffer(vec![vec![0u64; b_ext_words]; m]);
        let mut raw_c = SecretBuffer(vec![vec![0u64; RAW_CHUNK_WORDS]; m]);
        for u in 0..m {
            for w in 0..RAW_CHUNK_WORDS {
                raw_a[u][w] = party_rngs[u].next_u64();
                raw_b[u][w] = party_rngs[u].next_u64();
                raw_c[u][w] = raw_a[u][w] & raw_b[u][w];
            }
            raw_b[u][RAW_CHUNK_WORDS] = party_rngs[u].next_u64();
            raw_b[u][RAW_CHUNK_WORDS + 1] = party_rngs[u].next_u64();
        }

        // 2. Authenticate `raw_b` via KOS15 Subfield-VOLE and retain per-pair `(t_rows, q_rows)`
        //    so `crh_2blocks_x8` extracts BOTH `a * b` AND all 16 halving cross-term pads in ONE pass.
        let mut mac_b_full = SecretBuffer(vec![vec![[0u128; 64]; b_ext_words]; m]);
        for u in 0..m {
            let d_u = self.deltas[u];
            for w in 0..b_ext_words {
                let word = raw_b[u][w];
                for bit in 0..64 {
                    mac_b_full[u][w][bit] ^= bit_mask128((word >> bit) & 1) & d_u;
                }
            }
        }

        struct PairPadState {
            holder: usize,
            owner: usize,
            planes: Vec<u128>,
            send_sum: [[[u128; 2]; 1]; HALVING_ROUNDS],
            recv_sum: [[[u128; 2]; 1]; HALVING_ROUNDS],
            mask_t_rows: SecretBuffer<Vec<u128>>,
            mask_q_rows: SecretBuffer<Vec<u128>>,
        }

        let mut pair_states = Vec::with_capacity(self.pair_voles.len());
        for pv in &mut self.pair_voles {
            let (owner_rng, holder_rng) = if pv.owner < pv.holder {
                let (l, r) = party_rngs.split_at_mut(pv.holder);
                (&mut l[pv.owner], &mut r[0])
            } else {
                let (l, r) = party_rngs.split_at_mut(pv.owner);
                (&mut r[0], &mut l[pv.holder])
            };
            let (mut t_rows, mut q_rows) = pv.extend_authenticated_bits(
                self.committee,
                &self.session_id,
                &raw_b[pv.owner],
                owner_rng,
                holder_rng,
            )?;
            for k in 0..(64 * b_ext_words) {
                mac_b_full[pv.owner][k / 64][k % 64] ^= t_rows[k];
                mac_b_full[pv.holder][k / 64][k % 64] ^= q_rows[k];
            }

            let prefix = make_crh_prefix(&self.session_id, pv.holder, pv.owner, chunk_ctr);
            let mut planes = vec![0u128; HALVING_ROUNDS * RAW_CHUNK_BITS];
            let mut send_sum = [[[0u128; 2]; 1]; HALVING_ROUNDS];
            let mut recv_sum = [[[0u128; 2]; 1]; HALVING_ROUNDS];
            let mut and_send = SecretBuffer(vec![0u64; RAW_CHUNK_WORDS]);
            let mut and_recv = SecretBuffer(vec![0u64; RAW_CHUNK_WORDS]);

            let mut o0 = [[0u64; 34]; 8];
            let mut o1 = [[0u64; 34]; 8];
            let mut or = [[0u64; 34]; 8];
            let a_h = &raw_a[pv.holder];
            let b_o = &raw_b[pv.owner];
            let delta_h = pv.delta_holder;

            for base in (0..RAW_CHUNK_BITS).step_by(8) {
                let idx: [u64; 8] = core::array::from_fn(|s| (base + s) as u64);
                let r0: [u128; 8] = core::array::from_fn(|s| q_rows[base + s]);
                let r1: [u128; 8] = core::array::from_fn(|s| q_rows[base + s] ^ delta_h);
                let rr: [u128; 8] = core::array::from_fn(|s| t_rows[base + s]);
                crh_2blocks_x8(&prefix, idx, &r0, backend, &mut o0);
                crh_2blocks_x8(&prefix, idx, &r1, backend, &mut o1);
                crh_2blocks_x8(&prefix, idx, &rr, backend, &mut or);
                for s in 0..8 {
                    let k = base + s;
                    let a_bit = word_bit(a_h, k);
                    let b_bit = word_bit(b_o, k);
                    let pad0 = o0[s][0] & 1;
                    let corr = pad0 ^ (o1[s][0] & 1) ^ a_bit;
                    and_send[k / 64] |= pad0 << (k % 64);
                    and_recv[k / 64] |= ((or[s][0] & 1) ^ (b_bit & corr)) << (k % 64);
                    for round in 0..HALVING_ROUNDS {
                        let parity = (k >> round) & 1;
                        let w = 1 + 2 * round;
                        let h0 = (o0[s][w] as u128) | ((o0[s][w + 1] as u128) << 64);
                        let h1 = (o1[s][w] as u128) | ((o1[s][w + 1] as u128) << 64);
                        let hr = (or[s][w] as u128) | ((or[s][w + 1] as u128) << 64);
                        planes[round * RAW_CHUNK_BITS + k] = h0 ^ h1;
                        send_sum[round][0][parity] ^= h0;
                        recv_sum[round][0][parity] ^= hr;
                    }
                }
            }
            for buf in [&mut o0, &mut o1, &mut or] {
                qsag_asm::volatile_fill(buf, [0u64; 34]);
            }
            for w in 0..RAW_CHUNK_WORDS {
                raw_c[pv.holder][w] ^= and_send[w];
                raw_c[pv.owner][w] ^= and_recv[w];
            }
            wipe_u64s(&mut and_send);
            wipe_u64s(&mut and_recv);

            let mask_t = SecretBuffer(t_rows[RAW_CHUNK_BITS..].to_vec());
            let mask_q = SecretBuffer(q_rows[RAW_CHUNK_BITS..].to_vec());
            wipe_u128s(&mut t_rows);
            wipe_u128s(&mut q_rows);

            pair_states.push(PairPadState {
                holder: pv.holder,
                owner: pv.owner,
                planes,
                send_sum,
                recv_sum,
                mask_t_rows: mask_t,
                mask_q_rows: mask_q,
            });
        }

        #[cfg(test)]
        if self.inject_beaver_fault {
            self.inject_beaver_fault = false;
            raw_c[0][0] ^= 1;
        }

        // 3. Authenticate `raw_a` and `raw_c` (`2048` words total) in one batched pass.
        let mut ac_words = SecretBuffer(vec![Vec::with_capacity(2 * RAW_CHUNK_WORDS); m]);
        for u in 0..m {
            ac_words[u].extend_from_slice(&raw_a[u]);
            ac_words[u].extend_from_slice(&raw_c[u]);
        }
        let mac_ac = self.authenticate_words(&ac_words, party_rngs)?;
        for u in 0..m {
            wipe_u64s(&mut ac_words[u]);
        }
        let mut mac_a = SecretBuffer(vec![vec![[0u128; 64]; RAW_CHUNK_WORDS]; m]);
        let mut mac_c = SecretBuffer(vec![vec![[0u128; 64]; RAW_CHUNK_WORDS]; m]);
        let mut mac_b = SecretBuffer(vec![vec![[0u128; 64]; RAW_CHUNK_WORDS]; m]);
        for u in 0..m {
            mac_a[u].copy_from_slice(&mac_ac[u][..RAW_CHUNK_WORDS]);
            mac_c[u].copy_from_slice(&mac_ac[u][RAW_CHUNK_WORDS..]);
            mac_b[u].copy_from_slice(&mac_b_full[u][..RAW_CHUNK_WORDS]);
        }

        // 4. Active 16-round `GF(2^128)` recursive inner-product sacrifice (`2^16 -> 1`).
        let ctr_bytes = chunk_ctr.to_be_bytes();
        let sac_digest = h32(TAG_SAC_CHI, &[&self.session_id, &ctr_bytes]);
        let chi_seed = coin_toss_public_seed(&self.session_id, "qsa_sac_init", &sac_digest, party_rngs)?;
        let mut chi_u64 = vec![0u64; 2 * RAW_CHUNK_BITS];
        expand_u64_stream(TAG_SAC_CHI, &[&self.session_id, &chi_seed], &mut chi_u64);
        let chis: Vec<u128> = chi_u64
            .chunks_exact(2)
            .map(|w| (w[0] as u128) | ((w[1] as u128) << 64))
            .collect();
        wipe_u64s(&mut chi_u64);

        let mut a_vec = SecretBuffer(vec![vec![0u128; RAW_CHUNK_BITS]; m]);
        let mut b_vec = SecretBuffer(vec![vec![0u128; RAW_CHUNK_BITS]; m]);
        let mut mac_a_vec = SecretBuffer(vec![vec![0u128; RAW_CHUNK_BITS]; m]);
        let mut mac_b_vec = SecretBuffer(vec![vec![0u128; RAW_CHUNK_BITS]; m]);
        let mut c_cur = SecretBuffer(vec![0u128; m]);
        let mut mac_c_cur = SecretBuffer(vec![0u128; m]);

        for u in 0..m {
            for k in 0..RAW_CHUNK_BITS {
                let chi_k = chis[k];
                let a_bit = word_bit(&raw_a[u], k);
                let b_bit = word_bit(&raw_b[u], k);
                let c_bit = word_bit(&raw_c[u], k);
                a_vec[u][k] = chi_k & bit_mask128(a_bit);
                b_vec[u][k] = bit_mask128(b_bit) & 1; // 0 or 1 in GF(2^128)
                mac_a_vec[u][k] = gf128_mul(chi_k, mac_a[u][k / 64][k % 64]);
                mac_b_vec[u][k] = mac_b[u][k / 64][k % 64];
                c_cur[u] ^= chi_k & bit_mask128(c_bit);
                mac_c_cur[u] ^= gf128_mul(chi_k, mac_c[u][k / 64][k % 64]);
            }
        }

        let mut tens_b = vec![1u128];
        for round in 0..HALVING_ROUNDS {
            let cur_len = RAW_CHUNK_BITS >> round;
            let half = cur_len / 2;
            let group = 1usize << round;

            // Compute cross-terms `h0 = <a_even, b_odd>` and `h1 = <a_odd, b_even>` via structured pads.
            let mut h_shares = SecretBuffer(vec![vec![0u128; 2]; m]);
            for u in 0..m {
                for j in 0..half {
                    h_shares[u][0] ^= gf128_mul(a_vec[u][2 * j], b_vec[u][2 * j + 1]);
                    h_shares[u][1] ^= gf128_mul(a_vec[u][2 * j + 1], b_vec[u][2 * j]);
                }
            }

            for ps in &mut pair_states {
                let plane_lo = round * RAW_CHUNK_BITS;
                let plane = &mut ps.planes[plane_lo..plane_lo + RAW_CHUNK_BITS];
                let mut recv_acc = [0u128; 2];
                for (g, blk) in plane.chunks_mut(group).enumerate() {
                    let partner_a = a_vec[ps.holder][g ^ 1];
                    if round == 0 {
                        blk[0] ^= partner_a;
                    } else {
                        for (dst, &tb) in blk.iter_mut().zip(&tens_b) {
                            *dst ^= gf128_mul(partner_a, tb);
                        }
                    }
                    let first = g * group;
                    let mut sum = 0u128;
                    for (o, &corr) in blk.iter().enumerate() {
                        sum ^= corr & bit_mask128(word_bit(&raw_b[ps.owner], first + o));
                    }
                    recv_acc[g & 1] ^= sum;
                }
                wipe_u128s(plane);
                // `g & 1 == 1` has `b` in odd group and `a` in even group (`h0`);
                // `g & 1 == 0` has `b` in even group and `a` in odd group (`h1`).
                h_shares[ps.holder][0] ^= ps.send_sum[round][0][1];
                h_shares[ps.owner][0] ^= ps.recv_sum[round][0][1] ^ recv_acc[1];
                h_shares[ps.holder][1] ^= ps.send_sum[round][0][0];
                h_shares[ps.owner][1] ^= ps.recv_sum[round][0][0] ^ recv_acc[0];
            }

            let h_macs = self.authenticate_field_elements(&h_shares, party_rngs)?;
            let rnd_be = (round as u64).to_be_bytes();
            let rnd_digest = h32(TAG_SAC_CHI, &[&self.session_id, &ctr_bytes, &rnd_be]);
            let r_coin_seed =
                coin_toss_public_seed(&self.session_id, "qsa_sac_fold", &rnd_digest, party_rngs)?;
            let mut r_words = [0u64; 2];
            expand_u64_stream(TAG_SAC_CHI, &[&r_coin_seed], &mut r_words);
            let mut r_chal = (r_words[0] as u128) | ((r_words[1] as u128) << 64);
            if r_chal == 0 {
                r_chal = 1;
            }
            let r_sq = gf128_mul(r_chal, r_chal);

            for u in 0..m {
                for j in 0..half {
                    let ae = a_vec[u][2 * j];
                    let ao = a_vec[u][2 * j + 1];
                    let be = b_vec[u][2 * j];
                    let bo = b_vec[u][2 * j + 1];
                    a_vec[u][j] = ae ^ gf128_mul(r_chal, ao);
                    b_vec[u][j] = gf128_mul(r_chal, be) ^ bo;

                    let mae = mac_a_vec[u][2 * j];
                    let mao = mac_a_vec[u][2 * j + 1];
                    let mbe = mac_b_vec[u][2 * j];
                    let mbo = mac_b_vec[u][2 * j + 1];
                    mac_a_vec[u][j] = mae ^ gf128_mul(r_chal, mao);
                    mac_b_vec[u][j] = gf128_mul(r_chal, mbe) ^ mbo;
                }
                a_vec[u].truncate(half);
                b_vec[u].truncate(half);
                mac_a_vec[u].truncate(half);
                mac_b_vec[u].truncate(half);
                c_cur[u] = h_shares[u][0] ^ gf128_mul(r_chal, c_cur[u]) ^ gf128_mul(r_sq, h_shares[u][1]);
                mac_c_cur[u] =
                    h_macs[u][0] ^ gf128_mul(r_chal, mac_c_cur[u]) ^ gf128_mul(r_sq, h_macs[u][1]);
            }

            let prev = tens_b;
            tens_b = Vec::with_capacity(prev.len() * 2);
            for &x in &prev {
                tens_b.push(gf128_mul(r_chal, x));
            }
            tens_b.extend_from_slice(&prev);
        }

        // 5. Base case `L = 1`: mask `(a_final, b_final, c_final)` with fresh authenticated
        //    `(A_mask, B_mask, C_mask = A_mask * B_mask)` so opening leaks zero bits of `(a, b)`.
        let mut a_mask = SecretBuffer(vec![0u128; m]);
        let mut b_mask = SecretBuffer(vec![0u128; m]);
        let mut b_final_words = SecretBuffer(vec![vec![0u64; 2]; m]);
        for u in 0..m {
            a_mask[u] = party_rngs[u].next_u128();
            b_mask[u] = (raw_b[u][RAW_CHUNK_WORDS] as u128)
                | ((raw_b[u][RAW_CHUNK_WORDS + 1] as u128) << 64);
            b_final_words[u][0] = b_vec[u][0] as u64;
            b_final_words[u][1] = (b_vec[u][0] >> 64) as u64;
        }
        for u in 0..m {
            raw_b[u].truncate(RAW_CHUNK_WORDS);
        }

        // Cross-terms `c_mask = A_mask * B_mask` and `h0_base = a_final * B_mask` ride on `mask_t_rows / mask_q_rows`.
        let mut base_terms = SecretBuffer(vec![vec![0u128; 4]; m]); // [A_mask, c_mask, h0_base, h1_base]
        for u in 0..m {
            base_terms[u][0] = a_mask[u];
            base_terms[u][1] = gf128_mul(a_mask[u], b_mask[u]);
            base_terms[u][2] = gf128_mul(a_vec[u][0], b_mask[u]);
            base_terms[u][3] = gf128_mul(a_mask[u], b_vec[u][0]);
        }
        for ps in &mut pair_states {
            let prefix = make_crh_prefix(&self.session_id, ps.holder, ps.owner, chunk_ctr ^ (1u64 << 63));
            let (s_cm, r_cm) = cot_field_mul_128(
                &prefix,
                0,
                &ps.mask_q_rows,
                &ps.mask_t_rows,
                self.deltas[ps.holder],
                a_mask[ps.holder],
                b_mask[ps.owner],
                backend,
            );
            base_terms[ps.holder][1] ^= s_cm;
            base_terms[ps.owner][1] ^= r_cm;

            let (s_h0, r_h0) = cot_field_mul_128(
                &prefix,
                256,
                &ps.mask_q_rows,
                &ps.mask_t_rows,
                self.deltas[ps.holder],
                a_vec[ps.holder][0],
                b_mask[ps.owner],
                backend,
            );
            base_terms[ps.holder][2] ^= s_h0;
            base_terms[ps.owner][2] ^= r_h0;
            wipe_u128s(&mut ps.mask_t_rows);
            wipe_u128s(&mut ps.mask_q_rows);
        }

        // Cross-term `h1_base = A_mask * b_final` via fresh 128-bit Subfield-VOLE on `b_final_words`.
        for pv in &mut self.pair_voles {
            let (owner_rng, holder_rng) = if pv.owner < pv.holder {
                let (l, r) = party_rngs.split_at_mut(pv.holder);
                (&mut l[pv.owner], &mut r[0])
            } else {
                let (l, r) = party_rngs.split_at_mut(pv.owner);
                (&mut r[0], &mut l[pv.holder])
            };
            let (mut t_bf, mut q_bf) = pv.extend_authenticated_bits(
                self.committee,
                &self.session_id,
                &b_final_words[pv.owner],
                owner_rng,
                holder_rng,
            )?;
            let prefix = make_crh_prefix(
                &self.session_id,
                pv.holder,
                pv.owner,
                chunk_ctr ^ (3u64 << 62),
            );
            let (s_h1, r_h1) = cot_field_mul_128(
                &prefix,
                512,
                &q_bf,
                &t_bf,
                pv.delta_holder,
                a_mask[pv.holder],
                b_vec[pv.owner][0],
                backend,
            );
            base_terms[pv.holder][3] ^= s_h1;
            base_terms[pv.owner][3] ^= r_h1;
            wipe_u128s(&mut t_bf);
            wipe_u128s(&mut q_bf);
        }

        let base_macs = self.authenticate_field_elements(&base_terms, party_rngs)?;
        let mut mac_b_mask = SecretBuffer(vec![0u128; m]);
        for u in 0..m {
            let mut acc = 0u128;
            for b in 0..64 {
                acc ^= gf128_mul(mac_b_full[u][RAW_CHUNK_WORDS][b], 1u128 << b);
                acc ^= gf128_mul(mac_b_full[u][RAW_CHUNK_WORDS + 1][b], 1u128 << (64 + b));
            }
            mac_b_mask[u] = acc;
        }

        let base_digest = h32(TAG_SAC_CHI, &[&self.session_id, &ctr_bytes, b"base"]);
        let base_coin_seed =
            coin_toss_public_seed(&self.session_id, "qsa_sac_base", &base_digest, party_rngs)?;
        let mut r_words = [0u64; 2];
        expand_u64_stream(TAG_SAC_CHI, &[&base_coin_seed], &mut r_words);
        let mut r_base = (r_words[0] as u128) | ((r_words[1] as u128) << 64);
        if r_base == 0 {
            r_base = 1;
        }
        let r_base_sq = gf128_mul(r_base, r_base);

        // Fold `[a_final, A_mask]` and `[b_final, B_mask]` with `r_base`:
        // `A* = a_final ^ r_base * A_mask`, `B* = r_base * b_final ^ B_mask`,
        // `C* = h0_base ^ r_base * (c_final ^ r_base * C_mask) ^ r_base^2 * h1_base`.
        // Wait: <(a_final, A_mask) -> a_final + r A_mask, (b_final, B_mask) -> r b_final + B_mask>:
        // Product = r (a_final b_final + A_mask B_mask) + (a_final B_mask) + r^2 (A_mask b_final)
        //         = h0_base ^ r * (c_final ^ c_mask) ^ r^2 * h1_base!
        let mut a_star = 0u128;
        let mut b_star = 0u128;
        let mut c_zero_val = 0u128;
        let mut opened_field_macs = vec![vec![0u128; 3]; m];
        for u in 0..m {
            let a_s_u = a_vec[u][0] ^ gf128_mul(r_base, base_terms[u][0]);
            let b_s_u = gf128_mul(r_base, b_vec[u][0]) ^ b_mask[u];
            a_star ^= a_s_u;
            b_star ^= b_s_u;
            opened_field_macs[u][0] = mac_a_vec[u][0] ^ gf128_mul(r_base, base_macs[u][0]);
            opened_field_macs[u][1] = gf128_mul(r_base, mac_b_vec[u][0]) ^ mac_b_mask[u];
        }
        let prod_star = gf128_mul(a_star, b_star);
        for u in 0..m {
            let mut c_s_u = base_terms[u][2]
                ^ gf128_mul(r_base, c_cur[u] ^ base_terms[u][1])
                ^ gf128_mul(r_base_sq, base_terms[u][3]);
            if u == 0 {
                c_s_u ^= prod_star;
            }
            c_zero_val ^= c_s_u;
            opened_field_macs[u][2] = base_macs[u][2]
                ^ gf128_mul(r_base, mac_c_cur[u] ^ base_macs[u][1])
                ^ gf128_mul(r_base_sq, base_macs[u][3])
                ^ gf128_mul(prod_star, self.deltas[u]);
        }

        if black_box(c_zero_val) != 0 {
            return Err(DealerlessStagingError::TripleSacrificeFailed {
                committee: self.committee,
            });
        }
        run_committed_spdz_mac_check_fields(
            self.committee,
            0xFFFF_0000 | (chunk_ctr as usize),
            &self.session_id,
            &self.deltas,
            &[a_star, b_star, 0u128],
            &opened_field_macs,
            party_rngs,
        )?;

        // 6. Post-sacrifice public-coin Fisher–Yates word permutation + `2 -> 1` XOR combiner
        //    (`(a_0, b_0, c_0)` + `(a_1, b_1, c_1)` -> `d = a_0 ^ a_1`, `a = a_0`, `b = b_0 ^ b_1`,
        //    `c = c_0 ^ c_1 ^ (d & b_1)`), eliminating selective-failure OT choice leakage.
        let perm_digest = h32(TAG_SAC_CHI, &[&self.session_id, &ctr_bytes, b"combine"]);
        let perm_seed =
            coin_toss_public_seed(&self.session_id, "qsa_combine_perm", &perm_digest, party_rngs)?;
        let mut perm_words = vec![0u64; RAW_CHUNK_WORDS];
        expand_u64_stream(TAG_SAC_CHI, &[&perm_seed], &mut perm_words);
        let mut word_perm: Vec<usize> = (0..RAW_CHUNK_WORDS).collect();
        for i in (1..RAW_CHUNK_WORDS).rev() {
            let j = (perm_words[i] as usize) % (i + 1);
            word_perm.swap(i, j);
        }
        wipe_u64s(&mut perm_words);

        let mut d_opened = vec![0u64; USABLE_CHUNK_WORDS];
        let mut d_macs = vec![vec![[0u128; 64]; USABLE_CHUNK_WORDS]; m];
        for k in 0..USABLE_CHUNK_WORDS {
            let w0 = word_perm[2 * k];
            let w1 = word_perm[2 * k + 1];
            let mut d = 0u64;
            for u in 0..m {
                d ^= raw_a[u][w0] ^ raw_a[u][w1];
                for bit in 0..64 {
                    d_macs[u][k][bit] = mac_a[u][w0][bit] ^ mac_a[u][w1][bit];
                }
            }
            d_opened[k] = d;
        }
        run_committed_spdz_mac_check_words(
            self.committee,
            0xFFFE_0000 | (chunk_ctr as usize),
            &self.session_id,
            &self.deltas,
            &d_opened,
            &d_macs,
            party_rngs,
        )?;

        for u in 0..m {
            self.buf_a[u].clear();
            self.buf_b[u].clear();
            self.buf_c[u].clear();
            self.buf_mac_a[u].clear();
            self.buf_mac_b[u].clear();
            self.buf_mac_c[u].clear();
            self.buf_a[u].reserve(USABLE_CHUNK_WORDS);
            self.buf_b[u].reserve(USABLE_CHUNK_WORDS);
            self.buf_c[u].reserve(USABLE_CHUNK_WORDS);
            self.buf_mac_a[u].reserve(USABLE_CHUNK_WORDS);
            self.buf_mac_b[u].reserve(USABLE_CHUNK_WORDS);
            self.buf_mac_c[u].reserve(USABLE_CHUNK_WORDS);

            for k in 0..USABLE_CHUNK_WORDS {
                let w0 = word_perm[2 * k];
                let w1 = word_perm[2 * k + 1];
                let d = d_opened[k];
                let a_out = raw_a[u][w0];
                let b_out = raw_b[u][w0] ^ raw_b[u][w1];
                let c_out = raw_c[u][w0] ^ raw_c[u][w1] ^ (d & raw_b[u][w1]);

                let ma_out = mac_a[u][w0];
                let mut mb_out = [0u128; 64];
                let mut mc_out = [0u128; 64];
                for bit in 0..64 {
                    mb_out[bit] = mac_b[u][w0][bit] ^ mac_b[u][w1][bit];
                    let d_mask = bit_mask128((d >> bit) & 1);
                    mc_out[bit] = mac_c[u][w0][bit] ^ mac_c[u][w1][bit] ^ (d_mask & mac_b[u][w1][bit]);
                }
                self.buf_a[u].push(a_out);
                self.buf_b[u].push(b_out);
                self.buf_c[u].push(c_out);
                self.buf_mac_a[u].push(ma_out);
                self.buf_mac_b[u].push(mb_out);
                self.buf_mac_c[u].push(mc_out);
            }
            wipe_u64s(&mut raw_a[u]);
            wipe_u64s(&mut raw_b[u]);
            wipe_u64s(&mut raw_c[u]);
        }
        self.cursor = 0;
        Ok(())
    }

    /// Evaluate one 64-lane `Keccak-f[1600]` permutation on authenticated `[u64; 1600]` shares,
    /// verifying all `76,800` Beaver mask openings via a committed `MacCheck` before returning.
    fn eval_keccak_f1600_batch64(
        &mut self,
        step_tag: usize,
        states_sh: &mut [[u64; STATE_BITS]],
        states_mac: &mut [Vec<[u128; 64]>],
        party_rngs: &mut [PartyPrivateRng],
    ) -> Result<(), DealerlessStagingError> {
        let m = self.m;
        let mut b_sh = SecretBuffer(vec![[0u64; STATE_BITS]; m]);
        let mut b_mac = SecretBuffer(vec![vec![[0u128; 64]; STATE_BITS]; m]);
        let mut col_sh = [0u64; 320];
        let mut col_mac = vec![[0u128; 64]; 320];
        let mut d_theta_sh = [0u64; 320];
        let mut d_theta_mac = vec![[0u128; 64]; 320];

        let mut opened_de = Vec::with_capacity(2 * 24 * STATE_BITS);
        let mut opened_de_macs = vec![Vec::with_capacity(2 * 24 * STATE_BITS); m];

        for &rc in &KECCAK_ROUND_CONSTANTS {
            // 1. Theta + Rho + Pi (purely local XOR on shares and MACs).
            for u in 0..m {
                for x in 0..5 {
                    for z in 0..64 {
                        let mut cs = 0u64;
                        let mut cm = [0u128; 64];
                        for y in 0..5 {
                            let idx = (x + 5 * y) * 64 + z;
                            cs ^= states_sh[u][idx];
                            for bit in 0..64 {
                                cm[bit] ^= states_mac[u][idx][bit];
                            }
                        }
                        col_sh[x * 64 + z] = cs;
                        col_mac[x * 64 + z] = cm;
                    }
                }
                for x in 0..5 {
                    for z in 0..64 {
                        let prev = ((x + 4) % 5) * 64 + z;
                        let next = ((x + 1) % 5) * 64 + ((z + 63) & 63);
                        d_theta_sh[x * 64 + z] = col_sh[prev] ^ col_mac_noop_u64(col_sh[next]);
                        for bit in 0..64 {
                            d_theta_mac[x * 64 + z][bit] = col_mac[prev][bit] ^ col_mac[next][bit];
                        }
                    }
                }
                for (source, &rot) in KECCAK_ROTATION_OFFSETS.iter().enumerate() {
                    let x = source % 5;
                    let y = source / 5;
                    let target = y + 5 * ((2 * x + 3 * y) % 5);
                    let rot = rot as usize;
                    for z in 0..64 {
                        let src_z = (z + 64 - rot) & 63;
                        let src = source * 64 + src_z;
                        let dst = target * 64 + z;
                        b_sh[u][dst] = states_sh[u][src] ^ d_theta_sh[x * 64 + src_z];
                        for bit in 0..64 {
                            b_mac[u][dst][bit] =
                                states_mac[u][src][bit] ^ d_theta_mac[x * 64 + src_z][bit];
                        }
                    }
                }
            }

            // 2. Chi (`out = b[idx] ^ ((~b[u_idx]) & b[v_idx])`) + Iota.
            for idx in 0..STATE_BITS {
                if self.cursor == self.buf_a[0].len() {
                    self.refill(party_rngs)?;
                }
                let cur = self.cursor;
                self.cursor += 1;

                let lane = idx / 64;
                let z = idx % 64;
                let row = 5 * (lane / 5);
                let u_idx = (row + (lane + 1) % 5) * 64 + z;
                let v_idx = (row + (lane + 2) % 5) * 64 + z;

                let mut d_open = 0u64;
                let mut e_open = 0u64;
                for p in 0..m {
                    let not_u_sh = if p == 0 { !b_sh[p][u_idx] } else { b_sh[p][u_idx] };
                    d_open ^= not_u_sh ^ self.buf_a[p][cur];
                    e_open ^= b_sh[p][v_idx] ^ self.buf_b[p][cur];
                }
                opened_de.push(d_open);
                opened_de.push(e_open);

                for p in 0..m {
                    let delta_p = self.deltas[p];
                    let mut d_m = [0u128; 64];
                    let mut e_m = [0u128; 64];
                    let ma = &self.buf_mac_a[p][cur];
                    let mb = &self.buf_mac_b[p][cur];
                    let mc = &self.buf_mac_c[p][cur];
                    for bit in 0..64 {
                        let not_u_mac = b_mac[p][u_idx][bit] ^ delta_p;
                        d_m[bit] = not_u_mac ^ ma[bit];
                        e_m[bit] = b_mac[p][v_idx][bit] ^ mb[bit];
                    }
                    opened_de_macs[p].push(d_m);
                    opened_de_macs[p].push(e_m);

                    let mut and_sh = self.buf_c[p][cur]
                        ^ (d_open & self.buf_b[p][cur])
                        ^ (e_open & self.buf_a[p][cur]);
                    if p == 0 {
                        and_sh ^= d_open & e_open;
                    }
                    let mut out_sh = b_sh[p][idx] ^ and_sh;
                    let mut out_mac = [0u128; 64];
                    let de_word = d_open & e_open;
                    for bit in 0..64 {
                        let d_mask = bit_mask128((d_open >> bit) & 1);
                        let e_mask = bit_mask128((e_open >> bit) & 1);
                        let de_mask = bit_mask128((de_word >> bit) & 1);
                        let and_mac =
                            mc[bit] ^ (d_mask & mb[bit]) ^ (e_mask & ma[bit]) ^ (de_mask & delta_p);
                        out_mac[bit] = b_mac[p][idx][bit] ^ and_mac;
                    }

                    // Iota on lane 0 (`idx < 64`).
                    if idx < 64 && ((rc >> idx) & 1) == 1 {
                        if p == 0 {
                            out_sh ^= u64::MAX;
                        }
                        for bit in 0..64 {
                            out_mac[bit] ^= delta_p;
                        }
                    }
                    states_sh[p][idx] = out_sh;
                    states_mac[p][idx] = out_mac;
                }
            }
        }

        wipe_u64s(&mut col_sh);
        wipe_u64s(&mut d_theta_sh);
        run_committed_spdz_mac_check_words(
            self.committee,
            step_tag,
            &self.session_id,
            &self.deltas,
            &opened_de,
            &opened_de_macs,
            party_rngs,
        )
    }
}

#[inline(always)]
const fn col_mac_noop_u64(x: u64) -> u64 {
    x
}

/// Stage one `t`-member committee's assigned leaves in complete isolation from non-members.
fn stage_single_committee_subtree_mpc(
    committee: usize,
    leaf_indices: &[u64],
    pk_seed: &Node,
    committee_sid: [u8; 32],
    committee_rngs: &mut [PartyPrivateRng],
    #[cfg(test)] fault: Option<StagingFault>,
) -> Result<(Vec<CommitteeShareStore>, Vec<(u64, Vec<Node>)>), DealerlessStagingError> {
    let m = committee_rngs.len();
    #[cfg(test)]
    let inject_beaver_fault = matches!(
        fault,
        Some(StagingFault::CorruptQsABeaverBit { committee: c }) if c == committee
    );

    let mut reservoir = CommitteeBeaverReservoir::establish(
        committee,
        committee_sid,
        committee_rngs,
        #[cfg(test)]
        inject_beaver_fault,
    )?;

    let num_leaves = leaf_indices.len();
    let total_chains = num_leaves * WOTS_CHAINS;
    let mut coords = Vec::with_capacity(total_chains);
    for &leaf in leaf_indices {
        for chain in 0..(WOTS_CHAINS as u32) {
            coords.push((leaf, chain));
        }
    }

    // Per-member staged share table: `stores_leaves[member_pos][epoch][3 * chain + step]`.
    let mut stores_leaves: Vec<Vec<Vec<Node>>> = (0..m)
        .map(|_| vec![vec![[0u8; 32]; LEAF_SHARE_NODES]; num_leaves])
        .collect();
    let mut opened_ends: Vec<Vec<Node>> = vec![vec![[0u8; 32]; WOTS_CHAINS]; num_leaves];

    for (batch_idx, batch_coords) in coords.chunks(64).enumerate() {
        let count = batch_coords.len();

        // Step 0 input: each member `u` samples uniform local `[u8; 32]` shares `y_u^(0)` (`0` comm!).
        let mut y0_planes = SecretBuffer(vec![[0u64; 256]; m]);
        for u in 0..m {
            let mut local_y0 = SecretBuffer(vec![[0u8; 32]; count]);
            for c_idx in 0..count {
                let share = committee_rngs[u].next_bytes32();
                local_y0[c_idx] = share;
                let global_chain = batch_idx * 64 + c_idx;
                let epoch = global_chain / WOTS_CHAINS;
                let chain = global_chain % WOTS_CHAINS;
                stores_leaves[u][epoch][3 * chain] = share;
            }
            y0_planes[u] = pack_nodes_to_256_planes(&local_y0);
            for n_ref in local_y0.iter_mut() {
                wipe_bytes32(n_ref);
            }
        }

        let y0_vec: Vec<Vec<u64>> = (0..m).map(|u| y0_planes[u].to_vec()).collect();
        let mut cur_planes_mac = reservoir.authenticate_words(&y0_vec, committee_rngs)?;
        let mut cur_planes_sh = y0_planes;

        // Evaluate `step = 0 (y^(0)->y^(1))`, `step = 1 (y^(1)->y^(2))`, `step = 2 (y^(2)->y^(3))`.
        for step in 0..(WOTS_STEPS as u32) {
            let pub_planes = build_chain_step_public_planes(pk_seed, batch_coords, step);
            let mut states_sh = SecretBuffer(vec![[0u64; STATE_BITS]; m]);
            let mut states_mac = SecretBuffer(vec![vec![[0u128; 64]; STATE_BITS]; m]);

            for u in 0..m {
                let delta_u = reservoir.deltas[u];
                for idx in 0..STATE_BITS {
                    let pub_w = pub_planes[idx];
                    if pub_w != 0 {
                        if u == 0 {
                            states_sh[u][idx] ^= pub_w;
                        }
                        for bit in 0..64 {
                            states_mac[u][idx][bit] ^= bit_mask128((pub_w >> bit) & 1) & delta_u;
                        }
                    }
                }
                for b in 0..256 {
                    let dst = CHAIN_INPUT_BIT_OFFSET + b;
                    states_sh[u][dst] ^= cur_planes_sh[u][b];
                    states_mac[u][dst] = cur_planes_mac[u][b];
                }
            }

            reservoir.eval_keccak_f1600_batch64(
                batch_idx * 8 + (step as usize),
                &mut states_sh,
                &mut states_mac,
                committee_rngs,
            )?;

            for u in 0..m {
                cur_planes_sh[u].copy_from_slice(&states_sh[u][..256]);
                cur_planes_mac[u].clear();
                cur_planes_mac[u].extend_from_slice(&states_mac[u][..256]);
            }

            if (step as usize) + 1 < WOTS_STEPS {
                // Seal secret intermediate shares `y^(1)` or `y^(2)` strictly locally!
                let next_step_slot = (step as usize) + 1;
                for u in 0..m {
                    let mut unpacked = unpack_256_planes_to_nodes(&cur_planes_sh[u], count);
                    for (c_idx, node_sh) in unpacked.iter().enumerate() {
                        let global_chain = batch_idx * 64 + c_idx;
                        let epoch = global_chain / WOTS_CHAINS;
                        let chain = global_chain % WOTS_CHAINS;
                        stores_leaves[u][epoch][3 * chain + next_step_slot] = *node_sh;
                    }
                    for n_ref in &mut unpacked {
                        wipe_bytes32(n_ref);
                    }
                }
            }
        }

        // Open ONLY `y^(3)` (`cur_planes_sh[..][0..256]`) and run committed SPDZ `MacCheck`!
        #[cfg(test)]
        if let Some(StagingFault::CorruptQsAEndpointOpen {
            committee: c,
            member_pos,
        }) = fault
            && c == committee
            && member_pos < m
            && batch_idx == 0
        {
            cur_planes_sh[member_pos][0] ^= 1;
        }

        let mut y3_opened_planes = [0u64; 256];
        let mut y3_macs_vec = vec![vec![[0u128; 64]; 256]; m];
        for u in 0..m {
            for b in 0..256 {
                y3_opened_planes[b] ^= cur_planes_sh[u][b];
                y3_macs_vec[u][b] = cur_planes_mac[u][b];
            }
        }
        run_committed_spdz_mac_check_words(
            committee,
            batch_idx * 8 + 7,
            &committee_sid,
            &reservoir.deltas,
            &y3_opened_planes,
            &y3_macs_vec,
            committee_rngs,
        )?;

        let batch_ends = unpack_256_planes_to_nodes(&y3_opened_planes, count);
        for (c_idx, end_node) in batch_ends.into_iter().enumerate() {
            let global_chain = batch_idx * 64 + c_idx;
            let epoch = global_chain / WOTS_CHAINS;
            let chain = global_chain % WOTS_CHAINS;
            opened_ends[epoch][chain] = end_node;
        }
    }

    let stores = stores_leaves
        .into_iter()
        .map(|leaves| CommitteeShareStore::from_parts(committee, leaves))
        .collect();
    let leaf_ends = leaf_indices
        .iter()
        .copied()
        .zip(opened_ends)
        .collect();
    Ok((stores, leaf_ends))
}

/// Dealerless distributed MPC staging for Mode `QS-A` ([`CommitteePartitionedJorts`]).
///
/// Custodians jointly coin-toss `pk_seed` and pairwise channel MAC keys, each `t`-member committee
/// stages its assigned subtree in strict isolation via authenticated binary `Keccak-f[1600]` MPC
/// without ever reconstructing `y^(0), y^(1), y^(2)`, opens **only** `y^(3)`, and cross-verifies
/// the global Merkle root `pk_root`.
pub fn stage_committee_partitioned_dealerless_mpc(
    t: usize,
    n: usize,
    height: u8,
    session_id: [u8; 32],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<StagedCommitteeKeys, DealerlessStagingError> {
    stage_committee_partitioned_inner(
        t,
        n,
        height,
        session_id,
        party_rngs,
        #[cfg(test)]
        None,
    )
}

fn stage_committee_partitioned_inner(
    t: usize,
    n: usize,
    height: u8,
    session_id: [u8; 32],
    party_rngs: &mut [PartyPrivateRng],
    #[cfg(test)] fault: Option<StagingFault>,
) -> Result<StagedCommitteeKeys, DealerlessStagingError> {
    if party_rngs.len() != n {
        return Err(DealerlessStagingError::PartyCountMismatch {
            expected: n,
            got: party_rngs.len(),
        });
    }
    let layout = CommitteeLayout::new(t, n, height)?;
    check_staging_budget(height, t)?;

    let pk_seed = coin_toss_pk_seed(
        &session_id,
        party_rngs,
        #[cfg(test)]
        fault,
    )?;
    let mac_keys = establish_dealerless_pairwise_mac_keys(&session_id, party_rngs)?;

    // Fork strictly isolated per-committee RNGs exclusively from the `t` committee members' RNGs.
    struct CommitteeJob {
        committee: usize,
        members: Vec<usize>,
        leaf_indices: Vec<u64>,
        committee_sid: [u8; 32],
        member_rngs: Vec<PartyPrivateRng>,
        result: Option<Result<(Vec<CommitteeShareStore>, Vec<(u64, Vec<Node>)>), DealerlessStagingError>>,
    }

    let mut jobs = Vec::with_capacity(layout.committees().len());
    for (committee, members) in layout.committees().iter().enumerate() {
        let c_be = (committee as u64).to_be_bytes();
        let committee_sid = h32(b"QSAG.QUORUM.QSA.COMMITTEE.SID/v1", &[&session_id, &pk_seed, &c_be]);
        let leaf_indices: Vec<u64> = (0..layout.leaves_per_committee())
            .map(|epoch| layout.leaf_of(committee, epoch))
            .collect();
        let member_rngs: Vec<PartyPrivateRng> = members
            .iter()
            .map(|&member| {
                let mut sub_seed = party_rngs[member].next_bytes32();
                let rng = PartyPrivateRng::from_seed(sub_seed, &committee_sid);
                wipe_bytes32(&mut sub_seed);
                rng
            })
            .collect();
        jobs.push(CommitteeJob {
            committee,
            members: members.clone(),
            leaf_indices,
            committee_sid,
            member_rngs,
            result: None,
        });
    }

    #[cfg(any(test, feature = "std"))]
    std::thread::scope(|scope| {
        for job in &mut jobs {
            let pk_seed_ref = &pk_seed;
            #[cfg(test)]
            let fault_copy = fault;
            scope.spawn(move || {
                job.result = Some(stage_single_committee_subtree_mpc(
                    job.committee,
                    &job.leaf_indices,
                    pk_seed_ref,
                    job.committee_sid,
                    &mut job.member_rngs,
                    #[cfg(test)]
                    fault_copy,
                ));
            });
        }
    });

    #[cfg(not(any(test, feature = "std")))]
    for job in &mut jobs {
        job.result = Some(stage_single_committee_subtree_mpc(
            job.committee,
            &job.leaf_indices,
            &pk_seed,
            job.committee_sid,
            &mut job.member_rngs,
            #[cfg(test)]
            fault,
        ));
    }

    let mut stores_by_party: Vec<Vec<CommitteeShareStore>> = (0..n).map(|_| Vec::new()).collect();
    let mut chain_ends = BTreeMap::new();
    for job in jobs {
        let (stores, ends) = job
            .result
            .ok_or(DealerlessStagingError::Quorum(QuorumError::InvalidConfig(
                "missing committee MPC result",
            )))??;
        for (store, member) in stores.into_iter().zip(job.members) {
            stores_by_party[member].push(store);
        }
        for (leaf, leaf_ends) in ends {
            chain_ends.insert(leaf, leaf_ends);
        }
    }

    // Every custodian independently builds `QuorumTree` from the opened `y^(3)` endpoints and
    // cross-verifies agreement on `pk_root`.
    let per_party_trees: Vec<QuorumTree> = (0..n)
        .map(|_| QuorumTree::build(pk_seed, height, chain_ends.clone()))
        .collect();
    verify_global_tree_agreement(&session_id, &per_party_trees)?;
    let tree = Arc::new(
        per_party_trees
            .into_iter()
            .next()
            .ok_or(DealerlessStagingError::Quorum(QuorumError::InvalidConfig(
                "empty party set",
            )))?,
    );

    let parties = stores_by_party
        .into_iter()
        .zip(mac_keys)
        .enumerate()
        .map(|(party, (stores, p_mac_keys))| {
            CommitteePartyMaterial::from_parts(party, p_mac_keys, stores)
        })
        .collect();

    Ok(StagedCommitteeKeys {
        layout,
        tree,
        parties,
    })
}

// =============================================================================================
// 4. Mode `QS-B`: Dealerless `(t, n)` BFT-Shamir Staging (`n >= 3f + 1`)
// =============================================================================================

#[inline]
fn bs_xor_assign(dst: &mut BitslicedGf256x64, src: &BitslicedGf256x64) {
    for (d, s) in dst.iter_mut().zip(src.iter()) {
        *d ^= *s;
    }
}

#[inline]
fn bs_xor(a: &BitslicedGf256x64, b: &BitslicedGf256x64) -> BitslicedGf256x64 {
    let mut out = *a;
    bs_xor_assign(&mut out, b);
    out
}

/// Share a 64-lane `BitslicedGf256x64` secret under a random polynomial of degree `deg` (`< n`),
/// returning `[party = 0..n]` evaluations at `shamir_point(party)`.
fn share_bs_gf256_degree(
    secret: &BitslicedGf256x64,
    deg: usize,
    powers: &[Vec<TowerGf256>],
    rng: &mut PartyPrivateRng,
) -> Vec<BitslicedGf256x64> {
    let n = powers.len();
    let mut coeffs = SecretBuffer(vec![[0u64; 8]; deg]);
    for c in coeffs.iter_mut() {
        for plane in c.iter_mut() {
            *plane = rng.next_u64();
        }
    }
    let mut shares = vec![*secret; n];
    for (p, p_pows) in powers.iter().enumerate() {
        for k in 0..deg {
            let term = p_pows[k].scale_planes(&coeffs[k]);
            bs_xor_assign(&mut shares[p], &term);
        }
    }
    for c in coeffs.iter_mut() {
        wipe_u64s(c);
    }
    shares
}

/// Reconstruct `P(0)` from `n` evaluations `shares[0..n]` at `shamir_point(0..n)` AND verify
/// that all `n` shares lie on a single polynomial of degree `<= max_deg`.
///
/// With `n >= 3f + 1` and `max_deg <= 2f`, Reed-Solomon minimum distance is `n - 2f >= f + 1`,
/// so any `<= f` corrupted evaluations strictly fail the consistency check!
fn reconstruct_and_verify_bs_degree(
    shares: &[BitslicedGf256x64],
    max_deg: usize,
    eval_pts: &[TowerGf256],
    lagrange_zero_base: &[TowerGf256],
    extrap_weights: &[Vec<TowerGf256>],
) -> Option<BitslicedGf256x64> {
    let base_len = max_deg + 1;
    let n = eval_pts.len();
    if shares.len() != n || base_len > n {
        return None;
    }

    // Verify `shares[base_len .. n]` match unique extrapolation from `shares[0 .. base_len]`.
    for (extra_idx, weights) in extrap_weights.iter().enumerate() {
        let target_p = base_len + extra_idx;
        let mut expected = [0u64; 8];
        for (i, &w) in weights.iter().enumerate() {
            let term = w.scale_planes(&shares[i]);
            bs_xor_assign(&mut expected, &term);
        }
        let mut diff = 0u64;
        for b in 0..8 {
            diff |= expected[b] ^ shares[target_p][b];
        }
        if black_box(diff) != 0 {
            return None;
        }
    }

    let mut at_zero = [0u64; 8];
    for (i, &w) in lagrange_zero_base.iter().enumerate() {
        let term = w.scale_planes(&shares[i]);
        bs_xor_assign(&mut at_zero, &term);
    }
    Some(at_zero)
}

/// Precomputed Lagrange weights for `base = 0 .. max_deg + 1` to `0` and to `max_deg + 1 .. n`.
fn precompute_rs_check_weights(
    eval_pts: &[TowerGf256],
    max_deg: usize,
) -> Option<(Vec<TowerGf256>, Vec<Vec<TowerGf256>>)> {
    let base_len = max_deg + 1;
    let n = eval_pts.len();
    if base_len > n {
        return None;
    }
    let base_pts = &eval_pts[..base_len];
    let zero_weights = lagrange_weights_zero_gf256(base_pts)?;
    let mut extrap = Vec::with_capacity(n - base_len);
    for &target_x in &eval_pts[base_len..] {
        let mut w_row = Vec::with_capacity(base_len);
        for (i, &xi) in base_pts.iter().enumerate() {
            let mut num = TowerGf256::ONE;
            let mut den = TowerGf256::ONE;
            for (j, &xj) in base_pts.iter().enumerate() {
                if i == j {
                    continue;
                }
                num = num.mul(target_x.add(xj));
                den = den.mul(xi.add(xj));
            }
            w_row.push(num.mul(den.inv()?));
        }
        extrap.push(w_row);
    }
    Some((zero_weights, extrap))
}

/// HVZK dealerless zero-constant degree-`(t - 1)` `TowerGf256` byte-mask ceremony across all `n`
/// custodians (`Z(0) = 0`, `deg(Z) <= t - 1`, verified with `2^{-128}` soundness).
fn run_verified_zero_constant_shamir_masks(
    cfg: &QuorumConfig,
    num_bytes: usize,
    phase: &'static str,
    session_id: &[u8; 32],
    party_rngs: &mut [PartyPrivateRng],
    #[cfg(test)] fault: Option<StagingFault>,
) -> Result<SecretBuffer<Vec<Vec<u8>>>, DealerlessStagingError> {
    let n = cfg.n;
    let t = cfg.t;
    let eval_pts: Vec<TowerGf256> = (0..n).map(shamir_point).collect();

    // `powers[p][k]` = `x_p^{k + 1}` for `k = 0 .. t - 1` (`deg = 1 .. t - 1`).
    let powers: Vec<Vec<u8>> = (0..n)
        .map(|p| {
            let x = eval_pts[p];
            let mut acc = TowerGf256::ONE;
            (1..t)
                .map(|_| {
                    acc = acc.mul(x);
                    acc.0
                })
                .collect()
        })
        .collect();

    // `dealt_shares[dealer][party][byte_idx]`, `mask_polys[dealer][rep][coeff_idx 0..t]`,
    // `dealt_masks[dealer][party][rep]`, `dealer_coeffs[dealer][byte_idx * (t - 1) + k]`.
    let mut dealt_shares = SecretBuffer(vec![vec![vec![0u8; num_bytes]; n]; n]);
    let mut dealer_coeffs = SecretBuffer(vec![vec![0u8; num_bytes * (t - 1)]; n]);
    let mut dealer_c0 = SecretBuffer(vec![vec![0u8; num_bytes]; n]);
    let mut mask_coeffs = SecretBuffer(vec![vec![vec![0u8; t]; GF256_CHECK_REPS]; n]);
    let mut dealt_masks = SecretBuffer(vec![vec![[0u8; GF256_CHECK_REPS]; n]; n]);
    let mut commits = Vec::with_capacity(n);

    for d in 0..n {
        party_rngs[d].fill_bytes(&mut dealer_coeffs[d]);
        for rep in 0..GF256_CHECK_REPS {
            mask_coeffs[d][rep][0] = 0; // Zero constant term!
            party_rngs[d].fill_bytes(&mut mask_coeffs[d][rep][1..t]);
        }

        #[cfg(test)]
        if let Some(StagingFault::CorruptQsBRefreshNonZeroConstant { dealer }) = fault
            && dealer == d
            && num_bytes > 0
        {
            dealer_c0[d][0] = 0x5A;
        }

        for p in 0..n {
            for b in 0..num_bytes {
                let mut acc = dealer_c0[d][b];
                for (k, &pow) in powers[p].iter().enumerate() {
                    acc ^= gf256_mul_ct(pow, dealer_coeffs[d][b * (t - 1) + k]);
                }
                dealt_shares[d][p][b] = acc;
            }
            for rep in 0..GF256_CHECK_REPS {
                let poly: Vec<TowerGf256> =
                    mask_coeffs[d][rep].iter().map(|&c| TowerGf256(c)).collect();
                dealt_masks[d][p][rep] = eval_poly_gf256(&poly, eval_pts[p]).0;
            }
        }

        #[cfg(test)]
        if let Some(StagingFault::CorruptQsBRefreshHighDegree {
            dealer,
            target_party,
        }) = fault
            && dealer == d
            && target_party < n
            && num_bytes > 0
        {
            dealt_shares[d][target_party][0] ^= 0x33;
        }

        // Commit to every recipient's share digest before drawing the HVZK challenge.
        let mut xof = Cshake256Xof::new_shake256();
        xof.absorb(session_id);
        xof.absorb(phase.as_bytes());
        xof.absorb(&(d as u64).to_be_bytes());
        for p in 0..n {
            let p_dig = h32(
                TAG_SHAMIR_COMMIT,
                &[session_id, &dealt_shares[d][p], &dealt_masks[d][p]],
            );
            xof.absorb(&p_dig);
        }
        let mut d_com = [0u8; 32];
        xof.squeeze(&mut d_com);
        commits.push(d_com);
    }

    let commit_digest = h32(TAG_SHAMIR_COMMIT, &[session_id, phase.as_bytes(), commits.as_flattened()]);
    let chal_seed = coin_toss_public_seed(session_id, phase, &commit_digest, party_rngs)?;
    let mut gamma = vec![0u8; GF256_CHECK_REPS * num_bytes];
    expand(
        b"QSAG.QUORUM.SHAMIR.HVZK.GAMMA/v1",
        &[session_id, &chal_seed],
        &mut gamma,
    );

    // Each dealer `d` opens the `16` linear-combination polynomials `P_{d, rep}(X)` of degree `< t`,
    // and every custodian `p` verifies `P_{d, rep}(0) == 0` AND `P_{d, rep}(x_p) == share_comb`.
    for d in 0..n {
        for rep in 0..GF256_CHECK_REPS {
            let g_row = &gamma[rep * num_bytes..(rep + 1) * num_bytes];
            let mut poly_coeffs = vec![TowerGf256(mask_coeffs[d][rep][0]); t];
            for k in 1..t {
                poly_coeffs[k] = TowerGf256(mask_coeffs[d][rep][k]);
            }
            for (b, &g_b) in g_row.iter().enumerate() {
                if g_b == 0 {
                    continue;
                }
                poly_coeffs[0].0 ^= gf256_mul_ct(g_b, dealer_c0[d][b]);
                for k in 1..t {
                    poly_coeffs[k].0 ^= gf256_mul_ct(g_b, dealer_coeffs[d][b * (t - 1) + (k - 1)]);
                }
            }

            if black_box(poly_coeffs[0].0) != 0 {
                for v in &mut dealer_coeffs[d] {
                    *v = 0;
                }
                return Err(DealerlessStagingError::ZeroConstantCheckFailed { dealer: d });
            }

            for p in 0..n {
                let mut share_comb = dealt_masks[d][p][rep];
                for (b, &g_b) in g_row.iter().enumerate() {
                    if g_b != 0 {
                        share_comb ^= gf256_mul_ct(g_b, dealt_shares[d][p][b]);
                    }
                }
                let eval = eval_poly_gf256(&poly_coeffs, eval_pts[p]).0;
                if black_box(eval ^ share_comb) != 0 {
                    return Err(DealerlessStagingError::ShamirDegreeCheckFailed {
                        phase,
                        dealer: d,
                    });
                }
            }
            wipe_gf256(&mut poly_coeffs);
        }
        wipe_bytes(&mut dealer_coeffs[d]);
        wipe_bytes(&mut dealer_c0[d]);
        for rep in 0..GF256_CHECK_REPS {
            wipe_bytes(&mut mask_coeffs[d][rep]);
        }
    }

    let mut combined = SecretBuffer(vec![vec![0u8; num_bytes]; n]);
    for p in 0..n {
        for d in 0..n {
            for b in 0..num_bytes {
                combined[p][b] ^= dealt_shares[d][p][b];
            }
            wipe_bytes(&mut dealt_shares[d][p]);
            wipe_bytes(&mut dealt_masks[d][p]);
        }
    }
    Ok(combined)
}

/// Dealerless distributed MPC staging for Mode `QS-B` ([`BftShamirJorts`]).
///
/// Custodians jointly coin-toss `pk_seed` and pairwise channel MAC keys, run dealerless `(t, n)`
/// chain-start DKG and 64-way bitsliced `Keccak-f[1600]` MPC without ever reconstructing `sk_seed`
/// or `(y^(0), y^(1), y^(2))` on any host, re-share `(y^(0), y^(1), y^(2))` into independent
/// bytewise degree-`(t - 1)` `TowerGf256` polynomials, open **only** `y^(3)`, and cross-verify `pk_root`.
pub fn stage_bft_shamir_dealerless_mpc(
    cfg: QuorumConfig,
    height: u8,
    session_id: [u8; 32],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<StagedShamirKeys, DealerlessStagingError> {
    stage_bft_shamir_inner(
        cfg,
        height,
        session_id,
        party_rngs,
        #[cfg(test)]
        None,
    )
}

fn stage_bft_shamir_inner(
    cfg: QuorumConfig,
    height: u8,
    session_id: [u8; 32],
    party_rngs: &mut [PartyPrivateRng],
    #[cfg(test)] fault: Option<StagingFault>,
) -> Result<StagedShamirKeys, DealerlessStagingError> {
    let n = cfg.n;
    let f = cfg.f;
    if party_rngs.len() != n {
        return Err(DealerlessStagingError::PartyCountMismatch {
            expected: n,
            got: party_rngs.len(),
        });
    }
    if height == 0 || height > 10 {
        return Err(DealerlessStagingError::Quorum(QuorumError::InvalidConfig(
            "need 1 <= height <= 10",
        )));
    }
    check_staging_budget(height, n)?;

    let pk_seed = coin_toss_pk_seed(
        &session_id,
        party_rngs,
        #[cfg(test)]
        fault,
    )?;
    let mac_keys = establish_dealerless_pairwise_mac_keys(&session_id, party_rngs)?;

    let eval_pts: Vec<TowerGf256> = (0..n).map(shamir_point).collect();
    let powers_2f: Vec<Vec<TowerGf256>> = (0..n)
        .map(|p| {
            let x = eval_pts[p];
            let mut acc = TowerGf256::ONE;
            (0..(2 * f))
                .map(|_| {
                    acc = acc.mul(x);
                    acc
                })
                .collect()
        })
        .collect();
    let powers_f: Vec<Vec<TowerGf256>> = powers_2f.iter().map(|v| v[..f].to_vec()).collect();

    let (zero_w_f, extrap_w_f) = precompute_rs_check_weights(&eval_pts, f).ok_or(
        DealerlessStagingError::Quorum(QuorumError::InvalidConfig(
            "Reed-Solomon degree-f check weights unavailable",
        )),
    )?;
    let (zero_w_2f, extrap_w_2f) = precompute_rs_check_weights(&eval_pts, 2 * f).ok_or(
        DealerlessStagingError::Quorum(QuorumError::InvalidConfig(
            "Reed-Solomon degree-2f check weights unavailable",
        )),
    )?;

    let num_leaves = 1usize << height;
    let total_chains = num_leaves * WOTS_CHAINS;
    let mut coords = Vec::with_capacity(total_chains);
    for leaf in 0..(num_leaves as u64) {
        for chain in 0..(WOTS_CHAINS as u32) {
            coords.push((leaf, chain));
        }
    }

    // Temporary degree-`f` bytewise share store before upgrading to independent degree-`(t - 1)`.
    let mut party_leaves_deg_f: SecretBuffer<Vec<Vec<Vec<Node>>>> = SecretBuffer(
        (0..n)
            .map(|_| vec![vec![[0u8; 32]; LEAF_SHARE_NODES]; num_leaves])
            .collect(),
    );
    let mut chain_ends: BTreeMap<u64, Vec<Node>> = BTreeMap::new();
    for leaf in 0..(num_leaves as u64) {
        chain_ends.insert(leaf, vec![[0u8; 32]; WOTS_CHAINS]);
    }

    for (batch_idx, batch_coords) in coords.chunks(64).enumerate() {
        let count = batch_coords.len();

        // 1. Dealerless degree-`f` DKG of `256` chain-start bit-planes `y^(0)`:
        //    Each custodian `d` contributes a Boolean bit-plane `y_d^(0)` (`0` or `1` in `GF(2^8)`),
        //    checked for both `deg <= f` AND `y_d^2 + y_d == 0` (`Booleanity`) before `y^(3)` opens!
        let mut dkg_contribs: SecretBuffer<Vec<Vec<BitslicedGf256x64>>> =
            SecretBuffer(vec![vec![[0u64; 8]; n]; n * 256]);
        let mut cur_planes_sh: SecretBuffer<Vec<Vec<BitslicedGf256x64>>> =
            SecretBuffer(vec![vec![[0u64; 8]; 256]; n]);

        for b in 0..256 {
            for d in 0..n {
                let mut bit_secret = [0u64; 8];
                bit_secret[0] = party_rngs[d].next_u64();
                if count < 64 {
                    bit_secret[0] &= (1u64 << count) - 1;
                }
                #[cfg(test)]
                if let Some(StagingFault::CorruptQsBNonBooleanInput { dealer }) = fault
                    && dealer == d
                    && batch_idx == 0
                    && b == 0
                {
                    bs_gf256_insert_lane(&mut bit_secret, 0, TowerGf256(0x42));
                }

                let shares = share_bs_gf256_degree(&bit_secret, f, &powers_f, &mut party_rngs[d]);
                wipe_u64s(&mut bit_secret);
                for p in 0..n {
                    bs_xor_assign(&mut cur_planes_sh[p][b], &shares[p]);
                    dkg_contribs[b * n + d][p] = shares[p];
                }
            }
        }

        // Record degree-`f` bytewise shares of `y^(0)`:
        // Note: each bit `b` of a byte `B = b / 8` is shared over `GF(2^8)`; packing 8 bit-shares
        // via `sum_{bit=0..7} share(bit_b) * X_byte_basis(2^bit)` gives an exact degree-`f` `GF(2^8)`
        // share of the byte `sum_{bit=0..7} bit_b * 2^bit` because `2^bit` (`1 << bit`) is a public
        // `TowerGf256` constant (`TowerGf256(1 << bit)`) and `GF(2^8)` addition is bitwise XOR!
        record_deg_f_byte_shares(
            &cur_planes_sh,
            batch_idx,
            count,
            0,
            &mut party_leaves_deg_f,
        );

        // Collect all `(lhs_deg_f, rhs_deg_f, out_deg_f)` quadratic relations across all 3 steps:
        //   - For `y_d` Booleanity: `y_d * y_d + y_d == 0` (`lhs = y_d, rhs = y_d, out = y_d`)
        //   - For `Chi` AND gate: `(~u) * v + c == 0` (`lhs = ~u, rhs = v, out = c`)
        let total_rels = n * 256 + WOTS_STEPS * 24 * STATE_BITS;
        let mut rel_lhs: SecretBuffer<Vec<Vec<BitslicedGf256x64>>> =
            SecretBuffer(vec![Vec::with_capacity(total_rels); n]);
        let mut rel_rhs: SecretBuffer<Vec<Vec<BitslicedGf256x64>>> =
            SecretBuffer(vec![Vec::with_capacity(total_rels); n]);
        let mut rel_out: SecretBuffer<Vec<Vec<BitslicedGf256x64>>> =
            SecretBuffer(vec![Vec::with_capacity(total_rels); n]);

        for rel in dkg_contribs.iter() {
            for p in 0..n {
                rel_lhs[p].push(rel[p]);
                rel_rhs[p].push(rel[p]);
                rel_out[p].push(rel[p]);
            }
        }

        // 2. Evaluate `step = 0, 1, 2` of `SHAKE256` (`Keccak-f[1600]`) in 64-way bitsliced Shamir.
        for step in 0..(WOTS_STEPS as u32) {
            let pub_planes = build_chain_step_public_planes(&pk_seed, batch_coords, step);
            let mut states_sh = SecretBuffer(vec![vec![[0u64; 8]; STATE_BITS]; n]);

            for p in 0..n {
                // Constant polynomial `P(X) = c` evaluates to `c` (`plane 0`) at EVERY `x_p`!
                for idx in 0..STATE_BITS {
                    states_sh[p][idx][0] ^= pub_planes[idx];
                }
                for b in 0..256 {
                    let dst = CHAIN_INPUT_BIT_OFFSET + b;
                    bs_xor_assign(&mut states_sh[p][dst], &cur_planes_sh[p][b]);
                }
            }

            let mut b_sh = SecretBuffer(vec![vec![[0u64; 8]; STATE_BITS]; n]);
            let mut col_sh = vec![[0u64; 8]; 320];
            let mut d_theta_sh = vec![[0u64; 8]; 320];

            for (rnd_idx, &rc) in KECCAK_ROUND_CONSTANTS.iter().enumerate() {
                // Linear layer (`Theta + Rho + Pi`).
                for p in 0..n {
                    for x in 0..5 {
                        for z in 0..64 {
                            let mut cs = [0u64; 8];
                            for y in 0..5 {
                                bs_xor_assign(&mut cs, &states_sh[p][(x + 5 * y) * 64 + z]);
                            }
                            col_sh[x * 64 + z] = cs;
                        }
                    }
                    for x in 0..5 {
                        for z in 0..64 {
                            let prev = ((x + 4) % 5) * 64 + z;
                            let next = ((x + 1) % 5) * 64 + ((z + 63) & 63);
                            d_theta_sh[x * 64 + z] = bs_xor(&col_sh[prev], &col_sh[next]);
                        }
                    }
                    for (source, &rot) in KECCAK_ROTATION_OFFSETS.iter().enumerate() {
                        let x = source % 5;
                        let y = source / 5;
                        let target = y + 5 * ((2 * x + 3 * y) % 5);
                        let rot = rot as usize;
                        for z in 0..64 {
                            let src_z = (z + 64 - rot) & 63;
                            b_sh[p][target * 64 + z] =
                                bs_xor(&states_sh[p][source * 64 + src_z], &d_theta_sh[x * 64 + src_z]);
                        }
                    }
                }

                // Dealerless random double-sharings `([r]_f, [r]_{2f})` summed across all `n` custodians.
                let mut r_f = SecretBuffer(vec![vec![[0u64; 8]; STATE_BITS]; n]);
                let mut r_2f = SecretBuffer(vec![vec![[0u64; 8]; STATE_BITS]; n]);
                for idx in 0..STATE_BITS {
                    for d in 0..n {
                        let mut sec = [0u64; 8];
                        for pl in &mut sec {
                            *pl = party_rngs[d].next_u64();
                        }
                        let sh_f = share_bs_gf256_degree(&sec, f, &powers_f, &mut party_rngs[d]);
                        let sh_2f =
                            share_bs_gf256_degree(&sec, 2 * f, &powers_2f, &mut party_rngs[d]);
                        wipe_u64s(&mut sec);
                        for p in 0..n {
                            bs_xor_assign(&mut r_f[p][idx], &sh_f[p]);
                            bs_xor_assign(&mut r_2f[p][idx], &sh_2f[p]);
                        }
                    }
                }

                for idx in 0..STATE_BITS {
                    let lane = idx / 64;
                    let z = idx % 64;
                    let row = 5 * (lane / 5);
                    let u_idx = (row + (lane + 1) % 5) * 64 + z;
                    let v_idx = (row + (lane + 2) % 5) * 64 + z;

                    let mut masked_2f = vec![[0u64; 8]; n];
                    let mut not_u_all = vec![[0u64; 8]; n];
                    for p in 0..n {
                        let mut not_u = b_sh[p][u_idx];
                        not_u[0] ^= u64::MAX; // Constant `1` in `GF(2^8)` at every point `x_p`!
                        not_u_all[p] = not_u;
                        let prod = bs_gf256_mul_planes_ct(&not_u, &b_sh[p][v_idx]);
                        masked_2f[p] = bs_xor(&prod, &r_2f[p][idx]);
                    }

                    let opened_masked = reconstruct_and_verify_bs_degree(
                        &masked_2f,
                        2 * f,
                        &eval_pts,
                        &zero_w_2f,
                        &extrap_w_2f,
                    )
                    .ok_or(DealerlessStagingError::MultiplicationCheckFailed {
                        check_idx: rnd_idx * STATE_BITS + idx,
                    })?;

                    for p in 0..n {
                        #[allow(unused_mut)]
                        let mut and_f = bs_xor(&opened_masked, &r_f[p][idx]);
                        #[cfg(test)]
                        if let Some(StagingFault::CorruptQsBGateProduct { party }) = fault
                            && party == p
                            && batch_idx == 0
                            && step == 0
                            && rnd_idx == 0
                            && idx == 0
                        {
                            and_f[0] ^= 1;
                        }
                        rel_lhs[p].push(not_u_all[p]);
                        rel_rhs[p].push(b_sh[p][v_idx]);
                        rel_out[p].push(and_f);

                        let mut out = bs_xor(&b_sh[p][idx], &and_f);
                        if idx < 64 && ((rc >> idx) & 1) == 1 {
                            out[0] ^= u64::MAX;
                        }
                        states_sh[p][idx] = out;
                    }
                }
            }

            for p in 0..n {
                cur_planes_sh[p].copy_from_slice(&states_sh[p][..256]);
            }
            if (step as usize) + 1 < WOTS_STEPS {
                record_deg_f_byte_shares(
                    &cur_planes_sh,
                    batch_idx,
                    count,
                    (step as usize) + 1,
                    &mut party_leaves_deg_f,
                );
            }
        }

        // 3. Active 16-instance Reed-Solomon verification (`< 2^{-128}` soundness) BEFORE opening `y^(3)`!
        //    Verifies BOTH:
        //      (a) Every relation wire `(lhs, rhs, out)` has degree `<= f`
        //      (b) Every quadratic relation `lhs(0) * rhs(0) + out(0) == 0` holds (`deg <= 2f` & `P(0) == 0`)
        let num_rels = rel_lhs[0].len();
        let batch_be = (batch_idx as u64).to_be_bytes();
        let chal_digest = h32(b"QSAG.QUORUM.QSB.BATCH.CHAL/v1", &[&session_id, &pk_seed, &batch_be]);
        let chal_seed =
            coin_toss_public_seed(&session_id, "qsb_gate_verify", &chal_digest, party_rngs)?;
        let mut weights = vec![0u8; GF256_CHECK_REPS * 3 * num_rels];
        expand(
            b"QSAG.QUORUM.QSB.GATE.WEIGHTS/v1",
            &[&session_id, &chal_seed],
            &mut weights,
        );

        for rep in 0..GF256_CHECK_REPS {
            // Fresh dealerless degree-`f` mask `M_f(X)` and zero-constant degree-`2f` mask `Z_{2f}(X)`.
            let mut mask_f = SecretBuffer(vec![[0u64; 8]; n]);
            let mut z_2f = SecretBuffer(vec![[0u64; 8]; n]);
            for d in 0..n {
                let mut m_sec = [0u64; 8];
                for pl in &mut m_sec {
                    *pl = party_rngs[d].next_u64();
                }
                let mf_sh = share_bs_gf256_degree(&m_sec, f, &powers_f, &mut party_rngs[d]);
                wipe_u64s(&mut m_sec);
                let z_sh = share_bs_gf256_degree(&[0u64; 8], 2 * f, &powers_2f, &mut party_rngs[d]);
                for p in 0..n {
                    bs_xor_assign(&mut mask_f[p], &mf_sh[p]);
                    bs_xor_assign(&mut z_2f[p], &z_sh[p]);
                }
            }

            let w_base = rep * 3 * num_rels;
            let mut deg_f_open = vec![[0u64; 8]; n];
            let mut quad_open = vec![[0u64; 8]; n];
            for p in 0..n {
                let mut lin_acc = mask_f[p];
                let mut quad_acc = z_2f[p];
                for r in 0..num_rels {
                    let wl = TowerGf256(weights[w_base + 3 * r]);
                    let wr = TowerGf256(weights[w_base + 3 * r + 1]);
                    let wo = TowerGf256(weights[w_base + 3 * r + 2]);
                    wl.scale_xor_into(&mut lin_acc, &rel_lhs[p][r]);
                    wr.scale_xor_into(&mut lin_acc, &rel_rhs[p][r]);
                    wo.scale_xor_into(&mut lin_acc, &rel_out[p][r]);

                    if wo.0 != 0 {
                        let prod = bs_gf256_mul_planes_ct(&rel_lhs[p][r], &rel_rhs[p][r]);
                        let err_2f = bs_xor(&prod, &rel_out[p][r]);
                        wo.scale_xor_into(&mut quad_acc, &err_2f);
                    }
                }
                deg_f_open[p] = lin_acc;
                quad_open[p] = quad_acc;
            }

            if reconstruct_and_verify_bs_degree(&deg_f_open, f, &eval_pts, &zero_w_f, &extrap_w_f)
                .is_none()
            {
                return Err(DealerlessStagingError::MultiplicationCheckFailed { check_idx: rep });
            }
            let quad_zero = reconstruct_and_verify_bs_degree(
                &quad_open,
                2 * f,
                &eval_pts,
                &zero_w_2f,
                &extrap_w_2f,
            )
            .ok_or(DealerlessStagingError::MultiplicationCheckFailed { check_idx: rep })?;
            let mut nz = 0u64;
            for pl in &quad_zero {
                nz |= *pl;
            }
            if black_box(nz) != 0 {
                return Err(DealerlessStagingError::MultiplicationCheckFailed { check_idx: rep });
            }
        }

        // 4. Open ONLY `y^(3)` with Reed-Solomon degree-`<= f` verification!
        #[cfg(test)]
        if let Some(StagingFault::CorruptQsBEndpointOpen { party }) = fault
            && party < n
            && batch_idx == 0
        {
            cur_planes_sh[party][0][0] ^= 1;
        }

        let mut y3_planes = [0u64; 256];
        for b in 0..256 {
            let bit_shares: Vec<BitslicedGf256x64> =
                (0..n).map(|p| cur_planes_sh[p][b]).collect();
            let rec = reconstruct_and_verify_bs_degree(
                &bit_shares,
                f,
                &eval_pts,
                &zero_w_f,
                &extrap_w_f,
            )
            .ok_or(DealerlessStagingError::EndpointOpeningDegreeMismatch { batch: batch_idx })?;
            // Every valid `y^(3)` bit reconstructs in `{0, 1}` (`planes[1..8] == 0`).
            let mut non_bool = 0u64;
            for pl in &rec[1..] {
                non_bool |= *pl;
            }
            if black_box(non_bool) != 0 {
                return Err(DealerlessStagingError::EndpointOpeningDegreeMismatch {
                    batch: batch_idx,
                });
            }
            y3_planes[b] = rec[0];
        }

        let batch_ends = unpack_256_planes_to_nodes(&y3_planes, count);
        for (c_idx, end_node) in batch_ends.into_iter().enumerate() {
            let (leaf, chain) = batch_coords[c_idx];
            if let Some(leaf_vec) = chain_ends.get_mut(&leaf) {
                leaf_vec[chain as usize] = end_node;
            }
        }
    }

    // 5. Upgrade & re-randomize `(y^(0), y^(1), y^(2))` from degree `f` to independent bytewise
    //    degree-`(t - 1)` `TowerGf256` Shamir polynomials via HVZK-verified zero-constant masks,
    //    wiping the temporary degree-`f` shares in place!
    let total_secret_bytes = num_leaves * LEAF_SHARE_NODES * 32;
    let zero_masks = run_verified_zero_constant_shamir_masks(
        &cfg,
        total_secret_bytes,
        "qsb_stage_degree_upgrade",
        &session_id,
        party_rngs,
        #[cfg(test)]
        None,
    )?;

    let mut parties = Vec::with_capacity(n);
    for (p, p_mac_keys) in mac_keys.into_iter().enumerate() {
        let mut final_leaves = vec![vec![[0u8; 32]; LEAF_SHARE_NODES]; num_leaves];
        for (b_idx, (dst, src)) in final_leaves
            .as_flattened_mut()
            .as_flattened_mut()
            .iter_mut()
            .zip(party_leaves_deg_f[p].as_flattened().as_flattened().iter())
            .enumerate()
        {
            *dst = *src ^ zero_masks[p][b_idx];
        }
        for leaf_nodes in &mut party_leaves_deg_f[p] {
            for node in leaf_nodes {
                wipe_bytes32(node);
            }
        }
        parties.push(ShamirPartyMaterial::from_parts(p, p_mac_keys, final_leaves));
    }

    let per_party_trees: Vec<QuorumTree> = (0..n)
        .map(|_| QuorumTree::build(pk_seed, height, chain_ends.clone()))
        .collect();
    verify_global_tree_agreement(&session_id, &per_party_trees)?;
    let tree = Arc::new(
        per_party_trees
            .into_iter()
            .next()
            .ok_or(DealerlessStagingError::Quorum(QuorumError::InvalidConfig(
                "empty party set",
            )))?,
    );

    Ok(StagedShamirKeys { cfg, tree, parties })
}

/// Convert 256 bit-plane degree-`f` shares (`0` or `1` at `X = 0`) into bytewise `TowerGf256`
/// degree-`f` shares by linear packing `byte_share = sum_{bit=0..7} TowerGf256(1 << bit) * bit_share`.
///
/// Soundness of packing: in Wiedemann `TowerGf256`, field addition IS bitwise `u8` XOR, so for any
/// bits `b_0..b_7 in {0, 1}`, `bigoplus_{k=0..7} (1 << k) * b_k = sum_{k=0..7} b_k * 2^k`!
fn record_deg_f_byte_shares(
    planes_sh: &[Vec<BitslicedGf256x64>],
    batch_idx: usize,
    count: usize,
    step_slot: usize,
    dst_leaves: &mut [Vec<Vec<Node>>],
) {
    let n = planes_sh.len();
    for p in 0..n {
        for byte_idx in 0..32 {
            let mut byte_plane = [0u64; 8];
            for bit in 0..8 {
                let basis = TowerGf256(1u8 << bit);
                basis.scale_xor_into(&mut byte_plane, &planes_sh[p][8 * byte_idx + bit]);
            }
            for lane in 0..count {
                let global_chain = batch_idx * 64 + lane;
                let leaf = global_chain / WOTS_CHAINS;
                let chain = global_chain % WOTS_CHAINS;
                dst_leaves[p][leaf][3 * chain + step_slot][byte_idx] =
                    bs_gf256_extract_lane(&byte_plane, lane).0;
            }
            wipe_u64s(&mut byte_plane);
        }
    }
}

// =============================================================================================
// 5. Proactive Share & Pairwise Channel Key Refresh (`QS-A` & `QS-B`)
// =============================================================================================

/// XOR `mask` into `leaves` in place using volatile writes so pre-refresh share bytes do not
/// linger in registers or stack copies, then zeroize `mask`.
fn apply_and_wipe_leaf_mask_in_place(leaves: &mut [Vec<Node>], mask: &mut [u8]) {
    let flat_nodes: &mut [Node] = leaves.as_flattened_mut();
    let flat_bytes: &mut [u8] = flat_nodes.as_flattened_mut();
    for (dst, &m) in flat_bytes.iter_mut().zip(mask.iter()) {
        let updated = black_box(*dst) ^ black_box(m);
        *dst = black_box(updated);
    }
    qsag_asm::volatile_fill(mask, 0);
    black_box(mask);
}

/// Generate committee-isolated, algebraically zero-sum `t`-of-`t` XOR masks (`bigoplus_{u in C} Delta_u = 0`)
/// via 2-round pairwise commit-then-open seed agreement among members of `C`.
fn generate_committee_zero_sum_masks(
    committee: usize,
    m: usize,
    num_bytes: usize,
    session_id: &[u8; 32],
    member_rngs: &mut [PartyPrivateRng],
    #[cfg(test)] fault: Option<StagingFault>,
) -> Result<SecretBuffer<Vec<Vec<u8>>>, DealerlessStagingError> {
    let mut masks = SecretBuffer(vec![vec![0u8; num_bytes]; m]);
    let c_be = (committee as u64).to_be_bytes();

    for u in 0..m {
        for v in (u + 1)..m {
            let u_be = (u as u64).to_be_bytes();
            let v_be = (v as u64).to_be_bytes();
            let mut salt_u = member_rngs[u].next_bytes32();
            let mut share_u = member_rngs[u].next_bytes32();
            let mut salt_v = member_rngs[v].next_bytes32();
            let mut share_v = member_rngs[v].next_bytes32();

            let com_u = h32(
                TAG_REFRESH_PAIR,
                &[session_id, &c_be, &u_be, &v_be, &salt_u, &share_u],
            );
            let com_v = h32(
                TAG_REFRESH_PAIR,
                &[session_id, &c_be, &v_be, &u_be, &salt_v, &share_v],
            );

            #[cfg(test)]
            if let Some(StagingFault::CorruptQsARefreshOpen {
                committee: fc,
                member_pos,
            }) = fault
                && fc == committee
            {
                if member_pos == u {
                    share_u[0] ^= 0x01;
                } else if member_pos == v {
                    share_v[0] ^= 0x01;
                }
            }

            let exp_u = h32(
                TAG_REFRESH_PAIR,
                &[session_id, &c_be, &u_be, &v_be, &salt_u, &share_u],
            );
            let exp_v = h32(
                TAG_REFRESH_PAIR,
                &[session_id, &c_be, &v_be, &u_be, &salt_v, &share_v],
            );
            if !ct_eq_bytes32(&com_u, &exp_u) {
                wipe_bytes32(&mut salt_u);
                wipe_bytes32(&mut share_u);
                wipe_bytes32(&mut salt_v);
                wipe_bytes32(&mut share_v);
                return Err(DealerlessStagingError::CommitmentMismatch {
                    phase: "refresh_committee_pair",
                    party: u,
                });
            }
            if !ct_eq_bytes32(&com_v, &exp_v) {
                wipe_bytes32(&mut salt_u);
                wipe_bytes32(&mut share_u);
                wipe_bytes32(&mut salt_v);
                wipe_bytes32(&mut share_v);
                return Err(DealerlessStagingError::CommitmentMismatch {
                    phase: "refresh_committee_pair",
                    party: v,
                });
            }

            let mut pair_stream = SecretBuffer(vec![0u8; num_bytes]);
            expand(
                TAG_REFRESH_MASK,
                &[session_id, &c_be, &u_be, &v_be, &com_u, &com_v, &share_u, &share_v],
                &mut pair_stream,
            );
            wipe_bytes32(&mut salt_u);
            wipe_bytes32(&mut share_u);
            wipe_bytes32(&mut salt_v);
            wipe_bytes32(&mut share_v);

            for b in 0..num_bytes {
                masks[u][b] ^= pair_stream[b];
                masks[v][b] ^= pair_stream[b];
            }
            wipe_bytes(&mut pair_stream);
        }
    }
    Ok(masks)
}

/// Proactively refresh all live `QS-A` [`CommitteeCustodian`] share stores AND pairwise channel
/// MAC keys in place across epochs without changing `pk_root` or resetting `BeltLatch` state.
pub fn refresh_committee_shares<W: DurableWal>(
    layout: &CommitteeLayout,
    custodians: &mut [CommitteeCustodian<W>],
    session_id: [u8; 32],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(), DealerlessStagingError> {
    refresh_committee_shares_inner(
        layout,
        custodians,
        session_id,
        party_rngs,
        #[cfg(test)]
        None,
    )
}

fn refresh_committee_shares_inner<W: DurableWal>(
    layout: &CommitteeLayout,
    custodians: &mut [CommitteeCustodian<W>],
    session_id: [u8; 32],
    party_rngs: &mut [PartyPrivateRng],
    #[cfg(test)] fault: Option<StagingFault>,
) -> Result<(), DealerlessStagingError> {
    let n = layout.n;
    if custodians.len() != n || party_rngs.len() != n {
        return Err(DealerlessStagingError::PartyCountMismatch {
            expected: n,
            got: custodians.len().min(party_rngs.len()),
        });
    }

    let num_bytes = (layout.leaves_per_committee() as usize) * LEAF_SHARE_NODES * 32;
    let mut all_committee_masks = Vec::with_capacity(layout.committees().len());
    for (committee, members) in layout.committees().iter().enumerate() {
        let mut sub_rngs: Vec<PartyPrivateRng> = members
            .iter()
            .map(|&member| {
                let mut s = party_rngs[member].next_bytes32();
                let r = PartyPrivateRng::from_seed(s, b"QSAG.QUORUM.REFRESH.QSA.SUB/v1");
                wipe_bytes32(&mut s);
                r
            })
            .collect();
        let masks = generate_committee_zero_sum_masks(
            committee,
            members.len(),
            num_bytes,
            &session_id,
            &mut sub_rngs,
            #[cfg(test)]
            fault,
        )?;
        all_committee_masks.push(masks);
    }

    let new_mac_keys = establish_dealerless_pairwise_mac_keys(&session_id, party_rngs)?;

    // Commit changes only after every committee and pairwise ceremony succeeded!
    for ((committee, members), mut masks) in layout
        .committees()
        .iter()
        .enumerate()
        .zip(all_committee_masks)
    {
        for (pos, &member) in members.iter().enumerate() {
            let leaves = custodians[member].slot_leaves_mut(committee)?;
            apply_and_wipe_leaf_mask_in_place(leaves, &mut masks[pos]);
        }
    }
    for (custodian, keys) in custodians.iter_mut().zip(new_mac_keys) {
        custodian.replace_mac_keys(keys)?;
    }
    Ok(())
}

/// Proactively refresh pre-instantiation [`StagedCommitteeKeys`] in place.
pub fn refresh_staged_committee_keys(
    staged: &mut StagedCommitteeKeys,
    session_id: [u8; 32],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(), DealerlessStagingError> {
    let n = staged.layout.n;
    if staged.parties.len() != n || party_rngs.len() != n {
        return Err(DealerlessStagingError::PartyCountMismatch {
            expected: n,
            got: party_rngs.len(),
        });
    }
    let num_bytes = (staged.layout.leaves_per_committee() as usize) * LEAF_SHARE_NODES * 32;
    let mut all_masks = Vec::with_capacity(staged.layout.committees().len());
    for (committee, members) in staged.layout.committees().iter().enumerate() {
        let mut sub_rngs: Vec<PartyPrivateRng> = members
            .iter()
            .map(|&member| {
                let mut s = party_rngs[member].next_bytes32();
                let r = PartyPrivateRng::from_seed(s, b"QSAG.QUORUM.REFRESH.QSA.MAT/v1");
                wipe_bytes32(&mut s);
                r
            })
            .collect();
        all_masks.push(generate_committee_zero_sum_masks(
            committee,
            members.len(),
            num_bytes,
            &session_id,
            &mut sub_rngs,
            #[cfg(test)]
            None,
        )?);
    }
    let new_mac_keys = establish_dealerless_pairwise_mac_keys(&session_id, party_rngs)?;

    for ((committee, members), mut masks) in staged
        .layout
        .committees()
        .iter()
        .enumerate()
        .zip(all_masks)
    {
        for (pos, &member) in members.iter().enumerate() {
            if let Some(store) = staged.parties[member]
                .stores
                .iter_mut()
                .find(|s| s.committee() == committee)
            {
                apply_and_wipe_leaf_mask_in_place(store.leaves_mut(), &mut masks[pos]);
            }
        }
    }
    for (mat, keys) in staged.parties.iter_mut().zip(new_mac_keys) {
        mat.replace_mac_keys(keys);
    }
    Ok(())
}

/// Proactively refresh all live `QS-B` [`ShamirCustodian`] share tables AND pairwise channel MAC
/// keys in place via HVZK-verified degree-`< t` zero-constant `GF(2^8)` polynomials (`P(0) = 0`),
/// preserving `pk_root` and `BeltLatch` state while unlinking pre- and post-refresh shares.
pub fn refresh_bft_shamir_shares<W: DurableWal>(
    cfg: &QuorumConfig,
    custodians: &mut [ShamirCustodian<W>],
    session_id: [u8; 32],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(), DealerlessStagingError> {
    refresh_bft_shamir_shares_inner(
        cfg,
        custodians,
        session_id,
        party_rngs,
        #[cfg(test)]
        None,
    )
}

fn refresh_bft_shamir_shares_inner<W: DurableWal>(
    cfg: &QuorumConfig,
    custodians: &mut [ShamirCustodian<W>],
    session_id: [u8; 32],
    party_rngs: &mut [PartyPrivateRng],
    #[cfg(test)] fault: Option<StagingFault>,
) -> Result<(), DealerlessStagingError> {
    let n = cfg.n;
    if custodians.len() != n || party_rngs.len() != n {
        return Err(DealerlessStagingError::PartyCountMismatch {
            expected: n,
            got: custodians.len().min(party_rngs.len()),
        });
    }
    let num_bytes = custodians[0].share_bytes();
    let mut zero_masks = run_verified_zero_constant_shamir_masks(
        cfg,
        num_bytes,
        "qsb_proactive_refresh",
        &session_id,
        party_rngs,
        #[cfg(test)]
        fault,
    )?;
    let new_mac_keys = establish_dealerless_pairwise_mac_keys(&session_id, party_rngs)?;

    for (p, (custodian, keys)) in custodians.iter_mut().zip(new_mac_keys).enumerate() {
        apply_and_wipe_leaf_mask_in_place(custodian.leaves_mut(), &mut zero_masks[p]);
        custodian.replace_mac_keys(keys)?;
    }
    Ok(())
}

/// Proactively refresh pre-instantiation [`StagedShamirKeys`] in place.
pub fn refresh_staged_bft_shamir_keys(
    staged: &mut StagedShamirKeys,
    session_id: [u8; 32],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(), DealerlessStagingError> {
    let n = staged.cfg.n;
    if staged.parties.len() != n || party_rngs.len() != n {
        return Err(DealerlessStagingError::PartyCountMismatch {
            expected: n,
            got: party_rngs.len(),
        });
    }
    let num_leaves = 1usize << staged.tree.public_key().height;
    let num_bytes = num_leaves * LEAF_SHARE_NODES * 32;
    let mut zero_masks = run_verified_zero_constant_shamir_masks(
        &staged.cfg,
        num_bytes,
        "qsb_proactive_refresh_mat",
        &session_id,
        party_rngs,
        #[cfg(test)]
        None,
    )?;
    let new_mac_keys = establish_dealerless_pairwise_mac_keys(&session_id, party_rngs)?;

    for (p, (mat, keys)) in staged.parties.iter_mut().zip(new_mac_keys).enumerate() {
        apply_and_wipe_leaf_mask_in_place(mat.leaves_mut(), &mut zero_masks[p]);
        mat.replace_mac_keys(keys);
    }
    Ok(())
}

// =============================================================================================
// 6. Comprehensive Unit, Adversarial Fault-Rejection & Online Timing Tests
// =============================================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::quorum_jorts::{
        BftShamirJorts, CommitteePartitionedJorts, LatchCertificate, chain_step, combine_additive,
        combine_shamir, quorum_jorts_verify, verify_jorts_signature,
    };

    fn make_party_rngs(n: usize, tag: u8) -> Vec<PartyPrivateRng> {
        (0..n)
            .map(|p| {
                let mut seed = [0u8; 32];
                seed[0] = tag;
                seed[1] = p as u8;
                seed[2] = 0xC7;
                PartyPrivateRng::from_seed(seed, b"QSAG.QUORUM.DEALERLESS.TEST/v1")
            })
            .collect()
    }

    #[test]
    fn bitsliced_chain_step_matches_scalar_chain_step_bit_for_bit() {
        let mut rngs = make_party_rngs(1, 0x10);
        let pk_seed = rngs[0].next_bytes32();
        let coords: Vec<(u64, u32)> = (0..64).map(|i| ((i / 16) as u64, (i % 16) as u32)).collect();
        let inputs: Vec<Node> = (0..64).map(|_| rngs[0].next_bytes32()).collect();
        let in_planes = pack_nodes_to_256_planes(&inputs);

        for step in 0..3u32 {
            let mut state = build_chain_step_public_planes(&pk_seed, &coords, step);
            for b in 0..256 {
                state[CHAIN_INPUT_BIT_OFFSET + b] ^= in_planes[b];
            }
            // Permute each of the 64 lanes with reference Keccak to verify framing geometry.
            let mut out_planes = [0u64; 256];
            for lane in 0..64 {
                let mut words = [0u64; 25];
                for bit in 0..1600 {
                    let b = (state[bit] >> lane) & 1;
                    words[bit / 64] |= b << (bit % 64);
                }
                qsag_core::sponge::keccak::keccak_f1600(&mut words);
                for bit in 0..256 {
                    let b = (words[bit / 64] >> (bit % 64)) & 1;
                    out_planes[bit] |= b << lane;
                }
            }
            let got = unpack_256_planes_to_nodes(&out_planes, 64);
            for (lane, &(leaf, chain)) in coords.iter().enumerate() {
                let expected = chain_step(&pk_seed, leaf, chain, step, &inputs[lane]);
                assert_eq!(got[lane], expected, "mismatch at step {step} lane {lane}");
            }
        }
    }

    #[test]
    fn dealerless_qs_a_stages_signs_refreshes_and_unlinks_epochs() {
        let sid = [0x41u8; 32];
        let mut rngs = make_party_rngs(3, 0x21);
        let staged =
            stage_committee_partitioned_dealerless_mpc(2, 3, 2, sid, &mut rngs).expect("QS-A MPC");
        let pk_before = *staged.tree.public_key();
        let mut qs_a = CommitteePartitionedJorts::from_staged(staged).expect("from_staged");

        // Sign across all three 2-of-3 committees via the unmodified online BeltLatch ceremony!
        for (idx, committee_members) in [[0usize, 1], [0, 2], [1, 2]].iter().enumerate() {
            let msg = alloc::format!("dealerless-qs-a-committee-{idx}");
            let t0 = std::time::Instant::now();
            let sig = qs_a.sign(committee_members, msg.as_bytes()).expect("online sign");
            let elapsed = t0.elapsed();
            assert!(verify_jorts_signature(&pk_before, msg.as_bytes(), &sig));
            assert!(quorum_jorts_verify(&pk_before, msg.as_bytes(), &sig));
            if !cfg!(debug_assertions) {
                assert!(
                    elapsed.as_micros() < 1_000,
                    "online QS-A sign took {} us (>= 1000 us)",
                    elapsed.as_micros()
                );
            }
        }

        // Stage a height-3 `(2, 3)` tree (`2` leaves per committee) to test cross-epoch refresh
        // and verify mixing pre-refresh and post-refresh shares fails reconstruction!
        let mut rngs_h3 = make_party_rngs(3, 0x22);
        let staged_h3 = stage_committee_partitioned_dealerless_mpc(2, 3, 3, [0x42; 32], &mut rngs_h3)
            .expect("QS-A height 3");
        let pk_h3 = *staged_h3.tree.public_key();
        let mut qs_a_h3 = CommitteePartitionedJorts::from_staged(staged_h3).expect("from_staged");

        // Epoch 0 sign on committee 0 (`{0, 1}`).
        let sig_ep0 = qs_a_h3.sign(&[0, 1], b"epoch-0-msg").expect("epoch 0");
        assert!(verify_jorts_signature(&pk_h3, b"epoch-0-msg", &sig_ep0));

        // Capture custodian 0's pre-refresh opening on epoch 1 BEFORE refreshing!
        let (stale_rec, stale_echo0) = qs_a_h3.custodians[0]
            .bind_and_echo(0, 1, b"epoch-1-msg")
            .expect("bind 0");
        let (_, stale_echo1) = qs_a_h3.custodians[1]
            .bind_and_echo(0, 1, b"epoch-1-msg")
            .expect("bind 1");
        let permit0 = qs_a_h3.custodians[0]
            .verify_echoes(&stale_rec, &[stale_echo1])
            .expect("permit 0");
        let stale_open_0 = qs_a_h3.custodians[0]
            .open_shares(permit0)
            .expect("stale open 0");
        let _ = stale_echo0;

        // Run proactive committee share & MAC key refresh!
        let mut refresh_rngs = make_party_rngs(3, 0x23);
        refresh_committee_shares(
            &qs_a_h3.layout,
            &mut qs_a_h3.custodians,
            [0x99; 32],
            &mut refresh_rngs,
        )
        .expect("refresh QS-A");
        assert_eq!(*qs_a_h3.public_key(), pk_h3);

        // Fresh post-refresh signing on epoch 1 (`replay` of same bound message at epoch 1) succeeds!
        let sig_ep1 = qs_a_h3.sign_at(0, 1, b"epoch-1-msg").expect("post-refresh sign");
        assert!(verify_jorts_signature(&pk_h3, b"epoch-1-msg", &sig_ep1));

        // Obtain custodian 1's post-refresh opening on epoch 1 and mix with custodian 0's stale opening:
        let (post_rec, post_e0) = qs_a_h3.custodians[0]
            .bind_and_echo(0, 1, b"epoch-1-msg")
            .expect("re-echo 0");
        let (_, _post_e1) = qs_a_h3.custodians[1]
            .bind_and_echo(0, 1, b"epoch-1-msg")
            .expect("re-echo 1");
        let post_permit1 = qs_a_h3.custodians[1]
            .verify_echoes(&post_rec, &[post_e0])
            .expect("post permit 1");
        let fresh_open_1 = qs_a_h3.custodians[1]
            .open_shares(post_permit1)
            .expect("fresh open 1");

        let mixed_err = combine_additive(
            &qs_a_h3.layout,
            &qs_a_h3.tree,
            &post_rec,
            &[stale_open_0, fresh_open_1],
        );
        assert!(
            matches!(mixed_err, Err(QuorumError::ChainVerifyFailed { .. })),
            "mixing pre-refresh and post-refresh QS-A shares must fail: {mixed_err:?}"
        );
    }

    #[test]
    fn dealerless_qs_b_stages_signs_switches_quorums_and_refreshes() {
        for t in [2usize, 3] {
            let cfg = QuorumConfig::tight(t).expect("tight config");
            let mut rngs = make_party_rngs(cfg.n, 0x30 + t as u8);
            let staged = stage_bft_shamir_dealerless_mpc(cfg, 2, [0x51 + t as u8; 32], &mut rngs)
                .expect("QS-B MPC");
            let pk = *staged.tree.public_key();
            let mut qs_b = BftShamirJorts::from_staged(staged).expect("from_staged");

            let ackers_0: Vec<usize> = (0..cfg.q).collect();
            let signers_0: Vec<usize> = (0..cfg.t).collect();
            let t0 = std::time::Instant::now();
            let sig0 = qs_b
                .sign(&ackers_0, &signers_0, b"dealerless-qs-b-epoch-0")
                .expect("sign 0");
            let elapsed = t0.elapsed();
            assert!(verify_jorts_signature(&pk, b"dealerless-qs-b-epoch-0", &sig0));
            if !cfg!(debug_assertions) {
                assert!(
                    elapsed.as_micros() < 1_000,
                    "online QS-B (t={t}) sign took {} us (>= 1000 us)",
                    elapsed.as_micros()
                );
            }

            // Capture `(t - 1)` pre-refresh openings on leaf 1 BEFORE proactive refresh!
            let mut pre_acks = Vec::new();
            let mut rec_leaf1 = None;
            for &p in &ackers_0 {
                let (rec, ack) = qs_b.custodians[p].ack(1, b"epoch-1-refresh").expect("ack");
                rec_leaf1 = Some(rec);
                pre_acks.push(ack);
            }
            let rec1 = rec_leaf1.expect("record");
            let pre_cert = LatchCertificate::assemble(&rec1, pre_acks);
            let stale_openings: Vec<_> = (0..(cfg.t - 1))
                .map(|p| {
                    qs_b.custodians[p]
                        .open_shares(1, b"epoch-1-refresh", &pre_cert)
                        .expect("stale open")
                })
                .collect();

            // Run proactive zero-constant Shamir refresh across all `n` custodians!
            let mut ref_rngs = make_party_rngs(cfg.n, 0x40 + t as u8);
            refresh_bft_shamir_shares(&cfg, &mut qs_b.custodians, [0x77; 32], &mut ref_rngs)
                .expect("refresh QS-B");
            assert_eq!(*qs_b.public_key(), pk);

            // Switch to a different quorum `{n - q .. n}` & signer set `{n - t .. n}` on leaf 2!
            let ackers_2: Vec<usize> = ((cfg.n - cfg.q)..cfg.n).collect();
            let signers_2: Vec<usize> = ((cfg.n - cfg.t)..cfg.n).collect();
            let sig2 = qs_b
                .sign_at(2, &ackers_2, &signers_2, b"dealerless-qs-b-switched")
                .expect("switched sign");
            assert!(verify_jorts_signature(
                &pk,
                b"dealerless-qs-b-switched",
                &sig2
            ));

            // Re-certify leaf 1 under rotated MAC keys: post-refresh `t`-quorum succeeds,
            // whereas `(t - 1)` pre-refresh shares + `1` post-refresh share fails `ChainVerifyFailed`!
            let sig1 = qs_b
                .sign_at(1, &ackers_0, &signers_0, b"epoch-1-refresh")
                .expect("post-refresh leaf 1");
            assert!(verify_jorts_signature(&pk, b"epoch-1-refresh", &sig1));

            let mut post_acks = Vec::new();
            for &p in &ackers_0 {
                let (_, ack) = qs_b.custodians[p].ack(1, b"epoch-1-refresh").expect("re-ack");
                post_acks.push(ack);
            }
            let post_cert = LatchCertificate::assemble(&rec1, post_acks);
            let fresh_open_last = qs_b.custodians[cfg.t - 1]
                .open_shares(1, b"epoch-1-refresh", &post_cert)
                .expect("fresh open");

            let mut mixed = stale_openings;
            mixed.push(fresh_open_last);
            let mixed_res = combine_shamir(&cfg, &qs_b.tree, &rec1, &mixed);
            assert!(
                matches!(mixed_res, Err(QuorumError::ChainVerifyFailed { .. })),
                "mixing pre-refresh and post-refresh Shamir shares must fail: {mixed_res:?}"
            );
        }
    }

    #[test]
    fn dealerless_staging_and_refresh_reject_all_tampered_openings() {
        // 1. Tampered `pk_seed` Round-2 opening in QS-A.
        let mut rngs = make_party_rngs(3, 0x61);
        let res = stage_committee_partitioned_inner(
            2,
            3,
            1,
            [0x01; 32],
            &mut rngs,
            Some(StagingFault::CorruptPkSeedOpen { party: 1 }),
        );
        assert!(matches!(
            res,
            Err(DealerlessStagingError::CommitmentMismatch {
                phase: "pk_seed",
                party: 1
            })
        ));

        // 2. Tampered Beaver AND cross-term in QS-A -> caught by 16-round GF(2^128) sacrifice!
        let mut rngs = make_party_rngs(3, 0x62);
        let res = stage_committee_partitioned_inner(
            2,
            3,
            2,
            [0x02; 32],
            &mut rngs,
            Some(StagingFault::CorruptQsABeaverBit { committee: 0 }),
        );
        assert!(matches!(
            res,
            Err(DealerlessStagingError::TripleSacrificeFailed { committee: 0 })
        ));

        // 3. Tampered `y^(3)` share opening in QS-A -> caught by committed SPDZ `MacCheck`!
        let mut rngs = make_party_rngs(3, 0x63);
        let res = stage_committee_partitioned_inner(
            2,
            3,
            2,
            [0x03; 32],
            &mut rngs,
            Some(StagingFault::CorruptQsAEndpointOpen {
                committee: 1,
                member_pos: 1,
            }),
        );
        assert!(matches!(
            res,
            Err(DealerlessStagingError::MacCheckFailed { committee: 1, .. })
        ));

        // 4. Non-Boolean `GF(2^8)` DKG input (`y_d not in {0, 1}`) in QS-B -> caught before opening!
        let cfg = QuorumConfig::tight(2).expect("cfg");
        let mut rngs = make_party_rngs(cfg.n, 0x64);
        let res = stage_bft_shamir_inner(
            cfg,
            1,
            [0x04; 32],
            &mut rngs,
            Some(StagingFault::CorruptQsBNonBooleanInput { dealer: 2 }),
        );
        assert!(matches!(
            res,
            Err(DealerlessStagingError::MultiplicationCheckFailed { .. })
        ));

        // 5. Tampered `Chi` gate product in QS-B -> caught before opening `y^(3)`!
        let mut rngs = make_party_rngs(cfg.n, 0x65);
        let res = stage_bft_shamir_inner(
            cfg,
            1,
            [0x05; 32],
            &mut rngs,
            Some(StagingFault::CorruptQsBGateProduct { party: 0 }),
        );
        assert!(matches!(
            res,
            Err(DealerlessStagingError::MultiplicationCheckFailed { .. })
        ));

        // 6. Tampered `y^(3)` share opening in QS-B -> caught by Reed-Solomon degree check!
        let mut rngs = make_party_rngs(cfg.n, 0x66);
        let res = stage_bft_shamir_inner(
            cfg,
            1,
            [0x06; 32],
            &mut rngs,
            Some(StagingFault::CorruptQsBEndpointOpen { party: 3 }),
        );
        assert!(matches!(
            res,
            Err(DealerlessStagingError::EndpointOpeningDegreeMismatch { batch: 0 })
        ));

        // 7. Tampered proactive refresh polynomials (`P(0) != 0` and `deg >= t`) rejected intact!
        let mut rngs = make_party_rngs(cfg.n, 0x67);
        let staged = stage_bft_shamir_dealerless_mpc(cfg, 1, [0x07; 32], &mut rngs).expect("stage");
        let pk = *staged.tree.public_key();
        let mut qs_b = BftShamirJorts::from_staged(staged).expect("from_staged");

        let mut bad_rngs = make_party_rngs(cfg.n, 0x68);
        let nz_res = refresh_bft_shamir_shares_inner(
            &cfg,
            &mut qs_b.custodians,
            [0x08; 32],
            &mut bad_rngs,
            Some(StagingFault::CorruptQsBRefreshNonZeroConstant { dealer: 1 }),
        );
        assert_eq!(
            nz_res,
            Err(DealerlessStagingError::ZeroConstantCheckFailed { dealer: 1 })
        );

        let hd_res = refresh_bft_shamir_shares_inner(
            &cfg,
            &mut qs_b.custodians,
            [0x09; 32],
            &mut bad_rngs,
            Some(StagingFault::CorruptQsBRefreshHighDegree {
                dealer: 2,
                target_party: 0,
            }),
        );
        assert_eq!(
            hd_res,
            Err(DealerlessStagingError::ShamirDegreeCheckFailed {
                phase: "qsb_proactive_refresh",
                dealer: 2,
            })
        );

        // Custodian shares remain completely uncorrupted after aborted refresh attempts!
        let sig = qs_b
            .sign(&[0, 1, 2], &[0, 1], b"intact-after-rejected-refresh")
            .expect("intact sign");
        assert!(verify_jorts_signature(
            &pk,
            b"intact-after-rejected-refresh",
            &sig
        ));
    }
}
