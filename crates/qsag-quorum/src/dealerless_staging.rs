#![allow(clippy::chunks_exact_to_as_chunks)]

//! Dealerless distributed MPC subtree staging and proactive share refresh for
//! quorum-switching `Jorts` (`QS-A` [`CommitteePartitionedJorts`] and `QS-B` [`BftShamirJorts`]).
//!
//! Evaluates share-based MPC staging without a single master seed or reconstruction of
//! intermediate chain nodes. The orchestration API owns all participant states in one process;
//! it does not provide separate-host transport or process isolation. Pairwise exchanges assume
//! authenticated confidential channels when implemented across hosts. Refresh preserves the
//! existing latch records; it is an in-memory transition, not a crash-atomic storage transaction.
//!
//! The implemented operations are:
//!
//! 1. **Mode `QS-A` ([`stage_committee_partitioned_dealerless_mpc`]):**
//!    - All `n` custodians run a 2-round commit-then-open coin toss (`TAG_STAGE_PK_SEED`) to
//!      derive `pk_seed` and pairwise commit-then-open ceremonies (`TAG_PAIR_KEY`) to establish
//!      symmetric channel MAC keys, aborting on any commitment mismatch.
//!    - For each `t`-member committee `C`, **only** the `t` members of `C` sample local uniform
//!      256-bit shares `y_i^(0)` (`0` communication for `y^(0)`) and evaluate the three tweaked
//!      `SHAKE256` steps `y^(0) -> y^(1) -> y^(2) -> y^(3)` across all `128 * leaves_per_committee`
//!      chains via authenticated binary `GF(2)` Subfield-SPDZ MPC (post-quantum Ring-LWE Base OTs
//!      via [`OtMesh`], `SoftSpokenOT (n_C = 256, k = 2)` correlated OT extension for inputs, Beaver triples from
//!      qsag-core's `Π_triple_f2` in its additive output mode, and committed SPDZ `MacCheck`).
//!    - Secret chain states `y^(0), y^(1), y^(2)` remain strictly `t`-of-`t` XOR-shared inside `C`
//!      and are never reconstructed by staging; **only** `y^(3)` is released after `MacCheck`
//!      accepts, and all `n` custodians deterministically assemble and cross-verify `pk_root`.
//!
//! 2. **Mode `QS-B` ([`stage_bft_shamir_dealerless_mpc`]):**
//!    - All `n` custodians (`n >= 3f + 1`) run the 2-round `pk_seed` coin toss, pairwise MAC key
//!      agreement, and dealerless degree-`f` 64-way bitsliced chain-start DKG (`y^(0)` is the XOR
//!      of all `n` custodians' Boolean-verified contributions; no `sk_seed` ever exists).
//!    - Custodians evaluate `y^(0) -> y^(1) -> y^(2) -> y^(3)` in batched 64-way bitsliced
//!      `Keccak-f[1600]` over `GF(2^8)` (`TowerGf256`), verify every input bit (`x^2 + x = 0`) and
//!      every `Chi` multiplication gate via 16 HVZK Reed-Solomon degree-`<= 2f`
//!      zero-constant checks with challenges expanded from the joint coin **before** opening `y^(3)`, upgrade and
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
#[cfg(test)]
use qsag_core::field::tower::bs_gf256_insert_lane;
use qsag_core::field::tower::{
    BitslicedGf256x64, PublicGf256Matrix, TowerGf256, bs_gf256_extract_lane,
    bs_gf256_mul_planes_ct, eval_poly_gf256, lagrange_weights_zero_gf256, wipe_gf256,
};
use qsag_core::field::tower::{Tower128, wipe_tower128};
use qsag_core::preprocessing::{
    OT_EXT_F4_SLICES, OT_EXT_SUBSPACE_BITS, OtExtCheckKey, OtMesh, PartyPrivateRng,
    PreprocessError, blind_open_additive_gf128_poly, run_dealerless_pi_triple_f2_additive_with_fault,
    softspoken_f4_slice_setup_receiver, softspoken_f4_slice_setup_sender_ct,
};
use qsag_core::sponge::keccak::{Cshake256Xof, KECCAK_ROUND_CONSTANTS};
use qsag_core::wipe::{
    SecretBuffer, ct_eq_bytes32, wipe_bytes, wipe_bytes32, wipe_u64s, wipe_u128s,
};

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
const TAG_ABIT_COL: &[u8] = b"QSAG.QUORUM.STAGE.ABIT.COL/v1";
const TAG_ABIT_CHI: &[u8] = b"QSAG.QUORUM.STAGE.ABIT.CHI/v1";
const TAG_SAC_CHI: &[u8] = b"QSAG.QUORUM.STAGE.SAC.CHI/v1";
const TAG_TRIPLE_REFILL: &[u8] = b"QSAG.QUORUM.STAGE.TRIPLE.REFILL/v1";
const TAG_SHAMIR_COMMIT: &[u8] = b"QSAG.QUORUM.STAGE.SHAMIR.COMMIT/v1";
const TAG_REFRESH_PAIR: &[u8] = b"QSAG.QUORUM.REFRESH.PAIR/v1";
const TAG_REFRESH_MASK: &[u8] = b"QSAG.QUORUM.REFRESH.MASK/v1";

/// Number of Keccak state bits (`25 * 64`).
const STATE_BITS: usize = 1600;
/// Bit offset of the 32-byte secret chain input inside the framed `TAG_CHAIN` `SHAKE256` block.
const CHAIN_INPUT_BIT_OFFSET: usize = 800;
/// Triple words staged per refill: what one 64-lane `Keccak-f[1600]` evaluation consumes
/// (`24` rounds of `1600` `Chi` gates). At this size the factory's bucket combine reaches its
/// `2^-40` bound with three raw triples per output.
const REFILL_WORDS: usize = 24 * STATE_BITS;
/// Number of independent `GF(2^8)` HVZK checks (a fixed nonzero linear relation survives with probability `2^{-128}`).
const GF256_CHECK_REPS: usize = 16;

const KECCAK_ROTATION_OFFSETS: [u32; 25] = [
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];

/// Errors surfaced during dealerless distributed MPC staging or proactive share refresh.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DealerlessStagingError {
    /// A protected output sink rejected a staged share.
    OutputRejected,
    /// Underlying quorum parameter or custodian error.
    Quorum(QuorumError),
    /// Underlying Ring-LWE Base-OT or `SoftSpokenOT` preprocessing error.
    Preprocess(PreprocessError),
    /// Caller supplied the wrong number of custodian RNGs or custodians.
    PartyCountMismatch { expected: usize, got: usize },
    /// Round-2 decommitment did not match a custodian's Round-1 commitment.
    CommitmentMismatch { phase: &'static str, party: usize },
    /// Pairwise symmetric MAC key agreement failed consistency.
    PairwiseKeyMismatch { party_a: usize, party_b: usize },
    /// `SoftSpokenOT (n_C = 256, k = 2)` correlated-OT consistency check failed inside a
    /// committee. The variant keeps its earlier name.
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
            Self::OutputRejected => f.write_str("staging output sink rejected a share"),
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
                "SoftSpokenOT check failed in committee {committee} ({sender} -> {receiver})"
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
                write!(
                    f,
                    "Shamir degree check failed in {phase} for dealer {dealer}"
                )
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
                write!(
                    f,
                    "global pk_root confirmation mismatch at custodian {party}"
                )
            }
        }
    }
}

impl core::error::Error for DealerlessStagingError {}

/// Fault-injection hooks for adversarial unit tests.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg(test)]
#[allow(clippy::enum_variant_names)]
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

    // Round 2: Verify all peer commitments before deriving `pk_seed`.
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

/// Dealerless pairwise symmetric MAC key derivation over private pairwise channels (`a < b`),
/// plus purely local self-keys `keys[p][p]`, guarded against early-return leakage via [`SecretBuffer`].
fn establish_dealerless_pairwise_mac_keys(
    session_id: &[u8; 32],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<SecretBuffer<Vec<Vec<Node>>>, DealerlessStagingError> {
    let n = party_rngs.len();
    let mut keys = SecretBuffer(vec![vec![[0u8; 32]; n]; n]);
    for p in 0..n {
        keys[p][p] = party_rngs[p].next_bytes32();
    }
    for a in 0..n {
        for b in (a + 1)..n {
            let a_be = (a as u64).to_be_bytes();
            let b_be = (b as u64).to_be_bytes();
            let salt_a = SecretBuffer(party_rngs[a].next_bytes32());
            let contrib_a = SecretBuffer(party_rngs[a].next_bytes32());
            let salt_b = SecretBuffer(party_rngs[b].next_bytes32());
            let contrib_b = SecretBuffer(party_rngs[b].next_bytes32());

            let com_a = h32(
                TAG_PAIR_COMMIT,
                &[session_id, &a_be, &b_be, &*salt_a, &*contrib_a],
            );
            let com_b = h32(
                TAG_PAIR_COMMIT,
                &[session_id, &b_be, &a_be, &*salt_b, &*contrib_b],
            );

            let shared_key = h32(
                TAG_PAIR_KEY,
                &[
                    session_id,
                    &a_be,
                    &b_be,
                    &com_a,
                    &com_b,
                    &*contrib_a,
                    &*contrib_b,
                ],
            );
            keys[a][b] = shared_key;
            keys[b][a] = shared_key;
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
fn bit_mask128(bit: u64) -> u128 {
    0u128.wrapping_sub((black_box(bit) & 1) as u128)
}

fn gf128_mul(a: u128, b: u128) -> u128 {
    // Use the core polynomial-basis kernel, including its CPU feature checks and
    // portable fallback. The Wiedemann Tower128 encoding is a different field basis.
    qsag_asm::gf2_128_dot(core::slice::from_ref(&a), core::slice::from_ref(&b))
}

/// Stream deterministic `u64` words from `SHAKE256` over framed inputs.
/// The byte string [`expand_u64_stream`] absorbs for `(domain, parts)`.
fn stream_message(domain: &[u8], parts: &[&[u8]]) -> SecretBuffer<Vec<u8>> {
    let mut msg = SecretBuffer(Vec::with_capacity(
        8 + domain.len() + parts.iter().map(|p| 8 + p.len()).sum::<usize>(),
    ));
    for part in core::iter::once(&domain).chain(parts.iter()) {
        msg.extend_from_slice(&(part.len() as u64).to_be_bytes());
        msg.extend_from_slice(part);
    }
    msg
}

/// [`expand_u64_stream`] for up to eight inputs of one length at once: `outs[i]` receives the
/// stream of `msgs[i]` (built by [`stream_message`]), all on one eight-way `Keccak-f[1600]`.
/// The column streams of a correlated-OT extension are 384 such streams of equal shape.
fn expand_u64_streams_x8(
    msgs: &[SecretBuffer<Vec<u8>>],
    outs: &mut [&mut [u64]],
    backend: qsag_asm::SimdBackend,
) {
    const RATE: usize = 136;
    let lanes = msgs.len();
    assert!((1..=8).contains(&lanes) && outs.len() == lanes);
    let len = msgs[0].len();
    let words = outs[0].len();
    assert!(msgs.iter().all(|m| m.len() == len) && outs.iter().all(|o| o.len() == words));

    let mut st = qsag_asm::KeccakState8x::default();
    let mut block = SecretBuffer([[0u8; RATE]; 8]);
    let mut offset = 0;
    loop {
        let take = (len - offset).min(RATE);
        for (blk, msg) in block.iter_mut().zip(msgs) {
            *blk = [0u8; RATE];
            blk[..take].copy_from_slice(&msg[offset..offset + take]);
            if take < RATE {
                // SHAKE256 padding in the last block.
                blk[take] ^= 0x1f;
                blk[RATE - 1] ^= 0x80;
            }
        }
        for (w, lane) in st.0.iter_mut().enumerate().take(RATE / 8) {
            for (slot, blk) in lane.iter_mut().zip(block.iter()).take(lanes) {
                *slot ^= u64::from_le_bytes(core::array::from_fn(|i| blk[8 * w + i]));
            }
        }
        qsag_asm::keccak_f1600_x8_with_backend(&mut st, backend);
        offset += take;
        if take < RATE {
            break;
        }
    }
    let mut written = 0;
    while written < words {
        let n = (words - written).min(RATE / 8);
        for (w, lane) in st.0.iter().enumerate().take(n) {
            for (out, &val) in outs.iter_mut().zip(lane.iter()) {
                out[written + w] = val;
            }
        }
        written += n;
        if written < words {
            qsag_asm::keccak_f1600_x8_with_backend(&mut st, backend);
        }
    }
    qsag_asm::volatile_fill(&mut st.0, [0u64; 8]);
}

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
        for (bit_in_u128_half, tile_row) in tile.iter_mut().enumerate() {
            let c_lo = bit_in_u128_half;
            let c_hi = 64 + bit_in_u128_half;
            *tile_row = [
                cols[c_lo][w_pair],
                cols[c_hi][w_pair],
                if has_second {
                    cols[c_lo][w_pair + 1]
                } else {
                    0
                },
                if has_second {
                    cols[c_hi][w_pair + 1]
                } else {
                    0
                },
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

/// Pairwise `SoftSpokenOT (n_C = 256, k = 2)` $\mathbb{F}_4$-VOLE channel seeded from `256` active
/// Ring-LWE Base-OT correlations (`128` 2-bit punctured GGM slices, $2^{-241}$ consistency soundness).
struct PairwiseSubfieldVole {
    holder: usize,
    owner: usize,
    owner_slices: SecretBuffer<[[[u8; 32]; 4]; OT_EXT_F4_SLICES]>,
    holder_punctured: SecretBuffer<[[[u8; 32]; 4]; OT_EXT_F4_SLICES]>,
    delta_holder: [u128; 2],
    ext_ctr: u64,
}

impl Drop for PairwiseSubfieldVole {
    fn drop(&mut self) {
        wipe_u128s(&mut self.delta_holder);
    }
}

type AuthBitRowsPair = (SecretBuffer<Vec<u128>>, SecretBuffer<Vec<u128>>);

/// Run `job` once for every pairwise VOLE instance and return the results in instance
/// order. Each instance gets RNGs split off the private streams of its owner and its
/// holder, so the instances share no state; where threads exist they run concurrently.
/// The pairwise correlated-OT extensions and their hashing are the bulk of triple
/// generation, and a committee of `m` members has `m (m - 1)` of them.
fn run_pairs<T: Send>(
    pair_voles: &mut [PairwiseSubfieldVole],
    party_rngs: &mut [PartyPrivateRng],
    job: &(
         impl Fn(
        &mut PairwiseSubfieldVole,
        &mut PartyPrivateRng,
        &mut PartyPrivateRng,
    ) -> Result<T, DealerlessStagingError>
         + Sync
     ),
) -> Result<Vec<T>, DealerlessStagingError> {
    let mut split = |party: usize| {
        let mut seed = party_rngs[party].next_bytes32();
        let rng = PartyPrivateRng::from_seed(seed, b"QSAG.STAGING.PAIR.RNG/v1");
        wipe_bytes32(&mut seed);
        rng
    };
    let mut work: Vec<(&mut PairwiseSubfieldVole, PartyPrivateRng, PartyPrivateRng)> = pair_voles
        .iter_mut()
        .map(|pv| {
            let (owner, holder) = (split(pv.owner), split(pv.holder));
            (pv, owner, holder)
        })
        .collect();
    #[cfg(any(test, feature = "std"))]
    if work.len() > 1 {
        return std::thread::scope(|scope| {
            let handles: Vec<_> = work
                .iter_mut()
                .map(|(pv, owner, holder)| scope.spawn(move || job(pv, owner, holder)))
                .collect();
            let raw_joins: Vec<_> = handles.into_iter().map(|handle| handle.join()).collect();
            let mut out = Vec::with_capacity(raw_joins.len());
            for joined in raw_joins {
                match joined {
                    Ok(res) => out.push(res?),
                    Err(panic) => std::panic::resume_unwind(panic),
                }
            }
            Ok(out)
        });
    }
    work.iter_mut()
        .map(|(pv, owner, holder)| job(pv, owner, holder))
        .collect()
}

impl PairwiseSubfieldVole {
    /// Authenticate `payload_words` `u64` words owned by `self.owner` under `self.holder`'s
    /// 256-bit `delta_holder = [delta_0, delta_1]` key via `SoftSpokenOT (n_C = 256, k = 2)`
    /// (`128` $\mathbb{F}_4$ GGM slices, `+256` sacrificial bits, `[X | I_256]` per-column check).
    /// Returns lane-0 `(t_rows_for_owner, q_rows_for_holder)` satisfying
    /// `q_rows[k] ^ t_rows[k] = bit_k * delta_holder[0]`.
    fn extend_authenticated_bits(
        &mut self,
        committee: usize,
        session_id: &[u8; 32],
        owner_words: &[u64],
        owner_rng: &mut PartyPrivateRng,
        holder_rng: &mut PartyPrivateRng,
    ) -> Result<AuthBitRowsPair, DealerlessStagingError> {
        let payload_words = owner_words.len();
        let total_words = payload_words + 4; // +256 sacrificial OTP bits for `[X | I_256]`
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

        let mut t_cols = SecretBuffer(vec![vec![0u64; total_words]; OT_EXT_SUBSPACE_BITS]);
        let mut q_cols = SecretBuffer(vec![vec![0u64; total_words]; OT_EXT_SUBSPACE_BITS]);
        let mut u_cols = vec![vec![0u64; total_words]; OT_EXT_F4_SLICES];

        // Expand two 4-leaf `F_4` slices (`8` streams) per `keccak_f1600_x8` permutation on both sides.
        let backend = qsag_asm::detect_backend();
        let mut g_owner = SecretBuffer(vec![vec![0u64; total_words]; 8]);
        let mut g_holder = SecretBuffer(vec![vec![0u64; total_words]; 8]);
        for base_j in (0..OT_EXT_F4_SLICES).step_by(2) {
            let owner_msgs: Vec<SecretBuffer<Vec<u8>>> = (0..8)
                .map(|k| {
                    let leaf = 4 * base_j + k;
                    stream_message(
                        TAG_ABIT_COL,
                        &[
                            session_id,
                            &holder_le,
                            &owner_le,
                            &ctr_le,
                            &(leaf as u64).to_le_bytes(),
                            &self.owner_slices[base_j + (k / 4)][k % 4],
                        ],
                    )
                })
                .collect();
            {
                let mut outs: Vec<&mut [u64]> =
                    g_owner.iter_mut().map(Vec::as_mut_slice).collect();
                expand_u64_streams_x8(&owner_msgs, &mut outs, backend);
            }

            let holder_msgs: Vec<SecretBuffer<Vec<u8>>> = (0..8)
                .map(|k| {
                    let leaf = 4 * base_j + k;
                    stream_message(
                        TAG_ABIT_COL,
                        &[
                            session_id,
                            &holder_le,
                            &owner_le,
                            &ctr_le,
                            &(leaf as u64).to_le_bytes(),
                            &self.holder_punctured[base_j + (k / 4)][k % 4],
                        ],
                    )
                })
                .collect();
            {
                let mut outs: Vec<&mut [u64]> =
                    g_holder.iter_mut().map(Vec::as_mut_slice).collect();
                expand_u64_streams_x8(&holder_msgs, &mut outs, backend);
            }

            for sub in 0..2 {
                let j = base_j + sub;
                let off = 4 * sub;
                for w in 0..total_words {
                    let g0 = g_owner[off][w];
                    let g1 = g_owner[off + 1][w];
                    let g2 = g_owner[off + 2][w];
                    let g3 = g_owner[off + 3][w];
                    t_cols[j][w] = g2 ^ g3;
                    t_cols[OT_EXT_F4_SLICES + j][w] = g1 ^ g3;
                    u_cols[j][w] = g0 ^ g1 ^ g2 ^ g3 ^ full_owner[w];
                }

                let b0 = ((black_box(self.delta_holder[0]) >> j) & 1) as u64;
                let b1 = ((black_box(self.delta_holder[1]) >> j) & 1) as u64;
                let v_star = ((b0 as u8) << 1) | (b1 as u8);
                for v in 0..4usize {
                    let diff = black_box((v as u8) ^ v_star);
                    let is_neq = (((diff | diff.wrapping_neg()) >> 7) & 1) as u64;
                    let keep = 0u64.wrapping_sub(is_neq);
                    for gw in &mut g_holder[off + v] {
                        *gw &= keep;
                    }
                }
                let m0 = 0u64.wrapping_sub(b0);
                let m1 = 0u64.wrapping_sub(b1);
                for w in 0..total_words {
                    let h0 = g_holder[off][w];
                    let h1 = g_holder[off + 1][w];
                    let h2 = g_holder[off + 2][w];
                    let h3 = g_holder[off + 3][w];
                    let w_corr = u_cols[j][w] ^ h0 ^ h1 ^ h2 ^ h3;
                    q_cols[j][w] = h2 ^ h3 ^ (m0 & w_corr);
                    q_cols[OT_EXT_F4_SLICES + j][w] = h1 ^ h3 ^ (m1 & w_corr);
                }
            }
        }
        for s in g_owner.iter_mut() {
            wipe_u64s(s);
        }
        for s in g_holder.iter_mut() {
            wipe_u64s(s);
        }
        for col in &mut u_cols {
            wipe_u64s(col);
        }

        // Holder samples `chi_seed` strictly after `u_cols` is locked, masks it with the
        // pre-challenge `TAG_ABIT_CHI` stream (uniform OTP bijection on `{0, 1}^256`), and
        // verifies all 256 columns individually under `OtExtCheckKey` (`[X | I_256]`, Roy Thm 4.5).
        let chi_seed = holder_rng.next_bytes32();
        let mut chi_mask_words = [0u64; 4];
        expand_u64_stream(
            TAG_ABIT_CHI,
            &[session_id, &holder_le, &owner_le, &ctr_le],
            &mut chi_mask_words,
        );
        let mut check_seed = chi_seed;
        for (i, &w) in chi_mask_words.iter().enumerate() {
            let bytes = w.to_le_bytes();
            for b in 0..8 {
                check_seed[8 * i + b] ^= bytes[b];
            }
        }
        wipe_u64s(&mut chi_mask_words);

        let key = OtExtCheckKey::new(&check_seed, payload_words);
        wipe_bytes32(&mut check_seed);
        let mut x_hash = key.hash(&full_owner);
        wipe_u64s(&mut full_owner);

        let mut diff = 0u128;
        for col in 0..OT_EXT_SUBSPACE_BITS {
            let mut t_hash = key.hash(&t_cols[col]);
            let mut q_hash = key.hash(&q_cols[col]);
            let d_bit =
                ((black_box(self.delta_holder[col / 128]) >> (col % 128)) & 1) as u64;
            let mask = bit_mask128(d_bit);
            for lane in 0..2 {
                diff |= q_hash[lane] ^ t_hash[lane] ^ (mask & x_hash[lane]);
            }
            wipe_u128s(&mut t_hash);
            wipe_u128s(&mut q_hash);
        }
        wipe_u128s(&mut x_hash);

        let mut t_rows =
            SecretBuffer(transpose_128_cols_to_u128_rows(&t_cols[..128], payload_words));
        let mut q_rows =
            SecretBuffer(transpose_128_cols_to_u128_rows(&q_cols[..128], payload_words));
        for col in t_cols.iter_mut() {
            wipe_u64s(col);
        }
        for col in q_cols.iter_mut() {
            wipe_u64s(col);
        }
        if black_box(diff) != 0 {
            wipe_u128s(&mut t_rows);
            wipe_u128s(&mut q_rows);
            return Err(DealerlessStagingError::KosOtCheckFailed {
                committee,
                sender: self.holder,
                receiver: self.owner,
            });
        }
        Ok((t_rows, q_rows))
    }
}

/// Multiplicatively blinded SPDZ `GF(2^128)` batch `MacCheck` on opened `u64` words
/// `(opened_words, party_word_macs)` routed through `qsag_core`'s sender-residual OLE
/// (`w = (Σ r_i) · (Σ sigma_u)` over `ot_mesh`), never opening raw `sigmas[u]` (`C1-P0-1`).
#[expect(
    clippy::too_many_arguments,
    reason = "Committee context, MAC key shares, opened words, per-party MAC shares, OT mesh, and private RNGs are distinct protocol inputs"
)]
fn run_committed_spdz_mac_check_words(
    committee: usize,
    step_id: usize,
    session_id: &[u8; 32],
    deltas: &[u128],
    opened_words: &[u64],
    party_macs: &[Vec<[u128; 64]>],
    ot_mesh: &mut OtMesh,
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

    let chal_seed =
        coin_toss_public_seed(session_id, "qsa_mac_check", &transcript_digest, party_rngs)?;
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

    let mut sigmas = SecretBuffer(vec![0u128; m]);
    for u in 0..m {
        let flat_macs: &[u128] = party_macs[u].as_flattened();
        let mac_comb = qsag_asm::gf2_128_dot(flat_macs, &chis);
        sigmas[u] = mac_comb ^ gf128_mul(val_comb, deltas[u]);
    }

    let check_sid = h32(
        b"QSAG.QUORUM.QSA.BLIND_MAC/v1",
        &[
            session_id,
            &(committee as u64).to_be_bytes(),
            &(step_id as u64).to_be_bytes(),
            &transcript_digest,
            &chal_seed,
        ],
    );
    let blinded_residual = blind_open_additive_gf128_poly(
        &check_sid,
        "qsa_mac_check",
        &sigmas,
        Some(ot_mesh),
        party_rngs,
    )?;
    wipe_u128s(&mut sigmas);

    if black_box(blinded_residual) != 0 {
        return Err(DealerlessStagingError::MacCheckFailed {
            committee,
            step: step_id,
        });
    }
    Ok(())
}

/// Authenticated `u64`-bitsliced Boolean Beaver reservoir for one `t`-member committee.
struct CommitteeBeaverReservoir {
    committee: usize,
    session_id: [u8; 32],
    m: usize,
    deltas: SecretBuffer<Vec<u128>>,
    /// Each member's share of the second MAC lane the triple factory checks its own openings
    /// under. Staging consumes lane 0 (`deltas`) only.
    factory_lane: SecretBuffer<Vec<u128>>,
    ot_mesh: OtMesh,
    pair_voles: Vec<PairwiseSubfieldVole>,
    chunk_ctr: u64,
    /// Buffered verified triples: `[party][word]` (`REFILL_WORDS` words per refill).
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
        let mut factory_lane = SecretBuffer(vec![0u128; m]);
        for u in 0..m {
            let mut d = party_rngs[u].next_u128();
            if d == 0 {
                d = 1;
            }
            deltas[u] = d;
            factory_lane[u] = party_rngs[u].next_u128();
        }

        let mut pair_voles = Vec::with_capacity(m * (m - 1));
        for holder in 0..m {
            let d_lo = deltas[holder];
            let d_hi = factory_lane[holder];
            let mut choice = [
                d_lo as u64,
                (d_lo >> 64) as u64,
                d_hi as u64,
                (d_hi >> 64) as u64,
            ];
            for owner in 0..m {
                if owner == holder {
                    continue;
                }
                let (send, recv) =
                    ot_mesh.run_correlated_ot_words(owner, holder, &choice, party_rngs)?;
                let mut owner_slices = SecretBuffer([[[0u8; 32]; 4]; OT_EXT_F4_SLICES]);
                let mut holder_punctured = SecretBuffer([[[0u8; 32]; 4]; OT_EXT_F4_SLICES]);
                for j in 0..OT_EXT_F4_SLICES {
                    let mut r_seed = [0u8; 32];
                    let mut l_seed = [0u8; 32];
                    let mut k1_0 = [0u8; 32];
                    let mut k1_1 = [0u8; 32];
                    let mut sub_known = [0u8; 32];
                    let mut k1_known = [0u8; 32];
                    r_seed.copy_from_slice(&send[j].0[..32]);
                    l_seed.copy_from_slice(&send[j].1[..32]);
                    k1_0.copy_from_slice(&send[OT_EXT_F4_SLICES + j].0[..32]);
                    k1_1.copy_from_slice(&send[OT_EXT_F4_SLICES + j].1[..32]);
                    sub_known.copy_from_slice(&recv[j][..32]);
                    k1_known.copy_from_slice(&recv[OT_EXT_F4_SLICES + j][..32]);
                    let (leaves, sib2) = softspoken_f4_slice_setup_receiver(
                        &session_id,
                        j,
                        &r_seed,
                        &l_seed,
                        &k1_0,
                        &k1_1,
                    );
                    let b0 = ((black_box(d_lo) >> j) & 1) as u8;
                    let b1 = ((black_box(d_hi) >> j) & 1) as u8;
                    owner_slices[j] = leaves;
                    holder_punctured[j] = softspoken_f4_slice_setup_sender_ct(
                        &session_id,
                        j,
                        b0,
                        b1,
                        &sub_known,
                        &k1_known,
                        &sib2,
                    );
                    wipe_bytes32(&mut r_seed);
                    wipe_bytes32(&mut l_seed);
                    wipe_bytes32(&mut k1_0);
                    wipe_bytes32(&mut k1_1);
                    wipe_bytes32(&mut sub_known);
                    wipe_bytes32(&mut k1_known);
                }
                pair_voles.push(PairwiseSubfieldVole {
                    holder,
                    owner,
                    owner_slices,
                    holder_punctured,
                    delta_holder: [d_lo, d_hi],
                    ext_ctr: 0,
                });
            }
            wipe_u64s(&mut choice);
        }

        Ok(Self {
            committee,
            session_id,
            m,
            deltas,
            factory_lane,
            ot_mesh,
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

        let (committee, session_id) = (self.committee, self.session_id);
        let rows = run_pairs(
            &mut self.pair_voles,
            party_rngs,
            &|pv, owner_rng, holder_rng| {
                let (t_rows, q_rows) = pv.extend_authenticated_bits(
                    committee,
                    &session_id,
                    &words_per_party[pv.owner],
                    owner_rng,
                    holder_rng,
                )?;
                Ok((pv.owner, pv.holder, t_rows, q_rows))
            },
        )?;
        for (owner, holder, t_rows, q_rows) in rows {
            for k in 0..nbits {
                macs[owner][k / 64][k % 64] ^= t_rows[k];
                macs[holder][k / 64][k % 64] ^= q_rows[k];
            }
        }
        Ok(macs)
    }

    /// Stage `REFILL_WORDS` fresh triple words from qsag-core's `Π_triple_f2` in its additive
    /// output mode, under this committee's key: lane 0 of the factory's two-lane MAC is
    /// `deltas`, which also authenticates the committee's inputs.
    fn refill(&mut self, party_rngs: &mut [PartyPrivateRng]) -> Result<(), DealerlessStagingError> {
        let m = self.m;
        let chunk_ctr = self.chunk_ctr;
        self.chunk_ctr = self.chunk_ctr.wrapping_add(1);
        let session = h32(
            TAG_TRIPLE_REFILL,
            &[&self.session_id, &chunk_ctr.to_be_bytes()],
        );
        let mut alpha: Vec<[Tower128; 2]> = (0..m)
            .map(|u| [Tower128(self.deltas[u]), Tower128(self.factory_lane[u])])
            .collect();
        #[cfg(test)]
        let inject = core::mem::take(&mut self.inject_beaver_fault);
        #[cfg(not(test))]
        let inject = false;
        let staged = run_dealerless_pi_triple_f2_additive_with_fault(
            session,
            REFILL_WORDS,
            &alpha,
            &mut self.ot_mesh,
            party_rngs,
            |party, product_words| {
                if inject && party == 0 {
                    product_words[0] ^= 1;
                }
            },
        );
        for key in &mut alpha {
            wipe_tower128(key);
        }
        let mut staged = staged.map_err(|err| match err {
            PreprocessError::SacrificeResidualNonZero { .. } => {
                DealerlessStagingError::TripleSacrificeFailed {
                    committee: self.committee,
                }
            }
            other => other.into(),
        })?;

        let regroup_take = |macs: &mut [Vec<u128>; 2]| -> Vec<[u128; 64]> {
            // Wipe and release the unused second factory MAC lane immediately before
            // allocating the regrouped lane-0 buffer, avoiding a 2x heap spike.
            wipe_u128s(&mut macs[1]);
            macs[1] = Vec::new();
            let out = macs[0].as_chunks::<64>().0.to_vec();
            wipe_u128s(&mut macs[0]);
            macs[0] = Vec::new();
            out
        };
        for (u, shares) in staged.iter_mut().enumerate() {
            for (buf, words) in [
                (&mut self.buf_a[u], &mut shares.a),
                (&mut self.buf_b[u], &mut shares.b),
                (&mut self.buf_c[u], &mut shares.c),
            ] {
                wipe_u64s(buf);
                *buf = core::mem::take(words);
            }
            for (buf, macs) in [
                (&mut self.buf_mac_a[u], &mut shares.a_mac),
                (&mut self.buf_mac_b[u], &mut shares.b_mac),
                (&mut self.buf_mac_c[u], &mut shares.c_mac),
            ] {
                for word in buf.iter_mut() {
                    wipe_u128s(word);
                }
                *buf = Vec::new();
                *buf = regroup_take(macs);
            }
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
                        d_theta_sh[x * 64 + z] = col_sh[prev] ^ col_sh[next];
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
                    let not_u_sh = if p == 0 {
                        !b_sh[p][u_idx]
                    } else {
                        b_sh[p][u_idx]
                    };
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
                        for mac_word in &mut out_mac {
                            *mac_word ^= delta_p;
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
            &mut self.ot_mesh,
            party_rngs,
        )
    }
}

type StagedCommitteeSubtreeOutcome =
    Result<(Vec<CommitteeShareStore>, Vec<(u64, Vec<Node>)>), DealerlessStagingError>;

/// Stage one `t`-member committee's assigned leaves in complete isolation from non-members.
fn stage_single_committee_subtree_mpc(
    committee: usize,
    leaf_indices: &[u64],
    pk_seed: &Node,
    committee_sid: [u8; 32],
    committee_rngs: &mut [PartyPrivateRng],
    #[cfg(test)] fault: Option<StagingFault>,
) -> StagedCommitteeSubtreeOutcome {
    let mut stores_leaves = SecretBuffer(
        (0..committee_rngs.len())
            .map(|_| vec![vec![[0u8; 32]; LEAF_SHARE_NODES]; leaf_indices.len()])
            .collect::<Vec<Vec<Vec<Node>>>>(),
    );
    let leaf_ends = stage_single_committee_into(
        committee,
        StagingSlice {
            leaves: leaf_indices,
            chains: 0..WOTS_CHAINS,
        },
        pk_seed,
        committee_sid,
        committee_rngs,
        &mut |party, epoch, position, share| {
            stores_leaves[party][epoch][position] = *share;
            Ok(())
        },
        #[cfg(test)]
        fault,
    )?;
    let stores = core::mem::take(&mut stores_leaves.0)
        .into_iter()
        .map(|leaves| CommitteeShareStore::from_parts(committee, leaves))
        .collect();
    Ok((stores, leaf_ends))
}

struct StagingSlice<'a> {
    leaves: &'a [u64],
    chains: core::ops::Range<usize>,
}

/// Shared authenticated MPC implementation. The caller chooses the destination;
/// retain intermediate shares in wiping buffers until every endpoint MAC check succeeds.
/// Only then publish pages to the caller's sink.
fn stage_single_committee_into(
    committee: usize,
    slice: StagingSlice<'_>,
    pk_seed: &Node,
    committee_sid: [u8; 32],
    committee_rngs: &mut [PartyPrivateRng],
    sink: &mut impl FnMut(usize, usize, usize, &Node) -> Result<(), DealerlessStagingError>,
    #[cfg(test)] fault: Option<StagingFault>,
) -> Result<Vec<(u64, Vec<Node>)>, DealerlessStagingError> {
    let leaf_indices = slice.leaves;
    let chains_per_leaf = slice.chains.len();
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
    let total_chains = num_leaves * chains_per_leaf;
    let mut coords = Vec::with_capacity(total_chains);
    for &leaf in leaf_indices {
        for chain in slice.chains.start as u32..slice.chains.end as u32 {
            coords.push((leaf, chain));
        }
    }

    let mut pending = SecretBuffer(vec![vec![vec![[0u8; 32]; LEAF_SHARE_NODES]; num_leaves]; m]);
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
                let epoch = global_chain / chains_per_leaf;
                let chain = slice.chains.start + global_chain % chains_per_leaf;
                pending[u][epoch][3 * chain] = share;
            }
            y0_planes[u] = pack_nodes_to_256_planes(&local_y0);
            for n_ref in local_y0.iter_mut() {
                wipe_bytes32(n_ref);
            }
        }

        let y0_vec = SecretBuffer(
            (0..m)
                .map(|u| y0_planes[u].to_vec())
                .collect::<Vec<Vec<u64>>>(),
        );
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
                        let epoch = global_chain / chains_per_leaf;
                        let chain = slice.chains.start + global_chain % chains_per_leaf;
                        pending[u][epoch][3 * chain + next_step_slot] = *node_sh;
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
            &mut reservoir.ot_mesh,
            committee_rngs,
        )?;

        let batch_ends = unpack_256_planes_to_nodes(&y3_opened_planes, count);
        for (c_idx, end_node) in batch_ends.into_iter().enumerate() {
            let global_chain = batch_idx * 64 + c_idx;
            let epoch = global_chain / chains_per_leaf;
            let chain = slice.chains.start + global_chain % chains_per_leaf;
            opened_ends[epoch][chain] = end_node;
        }
    }

    // This barrier covers ALL batches, not just the first endpoint that passed.
    for (party, epochs) in pending.iter().enumerate() {
        for (epoch, pages) in epochs.iter().enumerate() {
            for chain in slice.chains.clone() {
                for step in 0..WOTS_STEPS {
                    let position = 3 * chain + step;
                    sink(party, epoch, position, &pages[position])?;
                }
            }
        }
    }
    Ok(leaf_indices.iter().copied().zip(opened_ends).collect())
}

/// Volatile caller supplies a protected sink and fresh per-party randomness.
/// Unlike committee layout staging, this evaluates only the requested subset.
#[cfg(all(
    any(test, feature = "std"),
    target_os = "linux",
    target_pointer_width = "64"
))]
pub(crate) fn stage_volatile_subset_into(
    leaves: &[u64],
    pk_seed: &Node,
    session: Node,
    rngs: &mut [PartyPrivateRng],
    sink: &mut (impl FnMut(usize, usize, usize, &Node) -> Result<(), DealerlessStagingError> + Send),
) -> Result<Vec<(u64, Vec<Node>)>, DealerlessStagingError> {
    stage_volatile_subset_into_inner(
        leaves,
        pk_seed,
        session,
        rngs,
        sink,
        #[cfg(test)]
        None,
    )
}

#[cfg(all(
    any(test, feature = "std"),
    target_os = "linux",
    target_pointer_width = "64"
))]
fn stage_volatile_subset_into_inner(
    leaves: &[u64],
    pk_seed: &Node,
    session: Node,
    rngs: &mut [PartyPrivateRng],
    sink: &mut (impl FnMut(usize, usize, usize, &Node) -> Result<(), DealerlessStagingError> + Send),
    #[cfg(test)] fault: Option<(usize, StagingFault)>,
) -> Result<Vec<(u64, Vec<Node>)>, DealerlessStagingError> {
    // Two independent 64-chain sessions: disjoint secret coordinates, independent
    // per-party private randomness, distinct public transcript domains. Both MAC
    // barriers must succeed before any descriptor can be certified.
    let mut jobs = Vec::with_capacity(2);
    for half in 0..2 {
        let sid = h32(
            b"QSAG.VOLATILE.MINT.HALF/v1",
            &[&session, &(half as u64).to_be_bytes()],
        );
        let private: Vec<_> = rngs
            .iter_mut()
            .map(|rng| {
                let mut seed = rng.next_bytes32();
                let private = PartyPrivateRng::from_seed(seed, b"QSAG.VOLATILE.MINT.HALF.RNG/v1");
                wipe_bytes(&mut seed);
                private
            })
            .collect();
        jobs.push((half, sid, private));
    }
    // Both halves must pass before the external sink sees any intermediate share.
    // Evaluate the two 64-chain halves sequentially: each half already parallelizes across
    // all CPU cores inside `run_pairs` and `Π_triple_f2`, so sequential execution halves peak RSS.
    let mut pending = SecretBuffer(vec![
        vec![vec![[0u8; 32]; LEAF_SHARE_NODES]; leaves.len()];
        rngs.len()
    ]);
    let mut parts = Vec::with_capacity(jobs.len());
    for (half, sid, mut private) in jobs {
        let part = stage_single_committee_into(
            0,
            StagingSlice {
                leaves,
                chains: half * 64..(half + 1) * 64,
            },
            pk_seed,
            sid,
            &mut private,
            &mut |party, epoch, position, share| {
                pending[party][epoch][position] = *share;
                Ok(())
            },
            #[cfg(test)]
            fault
                .filter(|&(target, _)| target == half)
                .map(|(_, fault)| fault),
        )?;
        parts.push(part);
    }
    let mut ends: Vec<_> = leaves
        .iter()
        .map(|&leaf| (leaf, vec![[0; 32]; WOTS_CHAINS]))
        .collect();
    for (half, part) in parts.into_iter().enumerate() {
        for ((_, dest), (_, source)) in ends.iter_mut().zip(part) {
            dest[half * 64..(half + 1) * 64].copy_from_slice(&source[half * 64..(half + 1) * 64]);
        }
    }
    for (party, epochs) in pending.iter().enumerate() {
        for (epoch, pages) in epochs.iter().enumerate() {
            for (position, share) in pages.iter().enumerate() {
                sink(party, epoch, position, share)?;
            }
        }
    }
    Ok(ends)
}

/// Dealerless distributed MPC staging for Mode `QS-A` ([`CommitteePartitionedJorts`]).
///
/// Custodians jointly coin-toss `pk_seed` and pairwise channel MAC keys, each `t`-member committee
/// stages its assigned subtree using only that committee's shares via authenticated binary `Keccak-f[1600]` MPC
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
        result: Option<StagedCommitteeSubtreeOutcome>,
    }

    let mut jobs = Vec::with_capacity(layout.committees().len());
    for (committee, members) in layout.committees().iter().enumerate() {
        let c_be = (committee as u64).to_be_bytes();
        let committee_sid = h32(
            b"QSAG.QUORUM.QSA.COMMITTEE.SID/v1",
            &[&session_id, &pk_seed, &c_be],
        );
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

    // Stage one committee at a time: each committee's `OtMesh::try_establish`, `run_pairs`
    // and `Π_triple_f2` already saturate available CPU cores internally, so staging committees
    // sequentially avoids multiplying peak `DeltaCotPool` RSS across four concurrent committees.
    for job in &mut jobs {
        let out = stage_single_committee_subtree_mpc(
            job.committee,
            &job.leaf_indices,
            &pk_seed,
            job.committee_sid,
            &mut job.member_rngs,
            #[cfg(test)]
            fault,
        )?;
        job.result = Some(Ok(out));
    }

    let mut stores_by_party: Vec<Vec<CommitteeShareStore>> = (0..n).map(|_| Vec::new()).collect();
    let mut chain_ends = BTreeMap::new();
    for job in jobs {
        let (stores, ends) =
            job.result
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
    let tree = Arc::new(per_party_trees.into_iter().next().ok_or(
        DealerlessStagingError::Quorum(QuorumError::InvalidConfig("empty party set")),
    )?);

    let parties = stores_by_party
        .into_iter()
        .zip(mac_keys.into_inner())
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
) -> SecretBuffer<Vec<BitslicedGf256x64>> {
    let n = powers.len();
    let mut coeffs = SecretBuffer(vec![[0u64; 8]; deg]);
    for c in coeffs.iter_mut() {
        for plane in c.iter_mut() {
            *plane = rng.next_u64();
        }
    }
    let mut shares = SecretBuffer(vec![*secret; n]);
    for (p, p_pows) in powers.iter().enumerate() {
        for k in 0..deg {
            let term = PublicGf256Matrix::from_public_scalar(p_pows[k]).scale_planes(&coeffs[k]);
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
            let term = PublicGf256Matrix::from_public_scalar(w).scale_planes(&shares[i]);
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
        let term = PublicGf256Matrix::from_public_scalar(w).scale_planes(&shares[i]);
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
/// custodians (`Z(0) = 0`, `deg(Z) <= t - 1`). Each fixed nonzero linear error
/// has ideal-challenge acceptance probability `2^{-128}`; aggregate protocol
/// bounds must also account for all dealers, checks and hash/PRG assumptions.
fn run_verified_zero_constant_shamir_masks(
    cfg: &QuorumConfig,
    num_bytes: usize,
    phase: &'static str,
    session_id: &[u8; 32],
    party_rngs: &mut [PartyPrivateRng],
    #[cfg(test)] fault: Option<StagingFault>,
) -> Result<SecretBuffer<Vec<Vec<u8>>>, DealerlessStagingError> {
    let n = cfg.parties();
    let t = cfg.threshold();
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
                let poly = SecretBuffer(
                    mask_coeffs[d][rep]
                        .iter()
                        .map(|&c| TowerGf256(c))
                        .collect::<Vec<_>>(),
                );
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

    let commit_digest = h32(
        TAG_SHAMIR_COMMIT,
        &[session_id, phase.as_bytes(), commits.as_flattened()],
    );
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
            let mut poly_coeffs = SecretBuffer(vec![TowerGf256(mask_coeffs[d][rep][0]); t]);
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
/// Custodians jointly coin-toss `pk_seed` and pairwise channel MAC keys, run dealerless degree-`f`
/// chain-start DKG and 64-way bitsliced `Keccak-f[1600]` MPC without ever reconstructing `sk_seed`
/// or `(y^(0), y^(1), y^(2))`, re-share `(y^(0), y^(1), y^(2))` into independent
/// bytewise degree-`(t - 1)` `TowerGf256` polynomials, open **only** `y^(3)`, and cross-verify `pk_root`.
/// The circuit privacy threshold is `cfg.max_faults()`; final stored shares use
/// `cfg.threshold()`. These thresholds can differ for non-tight configurations.
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
    let n = cfg.parties();
    let f = cfg.max_faults();
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

    let (zero_w_f, extrap_w_f) =
        precompute_rs_check_weights(&eval_pts, f).ok_or(DealerlessStagingError::Quorum(
            QuorumError::InvalidConfig("Reed-Solomon degree-f check weights unavailable"),
        ))?;
    let (zero_w_2f, extrap_w_2f) =
        precompute_rs_check_weights(&eval_pts, 2 * f).ok_or(DealerlessStagingError::Quorum(
            QuorumError::InvalidConfig("Reed-Solomon degree-2f check weights unavailable"),
        ))?;

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
        record_deg_f_byte_shares(&cur_planes_sh, batch_idx, count, 0, &mut party_leaves_deg_f);

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
            let mut col_sh = SecretBuffer(vec![[0u64; 8]; 320]);
            let mut d_theta_sh = SecretBuffer(vec![[0u64; 8]; 320]);

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
                            b_sh[p][target * 64 + z] = bs_xor(
                                &states_sh[p][source * 64 + src_z],
                                &d_theta_sh[x * 64 + src_z],
                            );
                        }
                    }
                }

                // Dealerless random double-sharings `([r]_f, [r]_{2f})` summed across all `n` custodians.
                let mut r_f = SecretBuffer(vec![vec![[0u64; 8]; STATE_BITS]; n]);
                let mut r_2f = SecretBuffer(vec![vec![[0u64; 8]; STATE_BITS]; n]);
                for idx in 0..STATE_BITS {
                    for dealer_rng in party_rngs.iter_mut().take(n) {
                        let mut sec = [0u64; 8];
                        for pl in &mut sec {
                            *pl = dealer_rng.next_u64();
                        }
                        let sh_f = share_bs_gf256_degree(&sec, f, &powers_f, dealer_rng);
                        let sh_2f = share_bs_gf256_degree(&sec, 2 * f, &powers_2f, dealer_rng);
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
                    .ok_or(
                        DealerlessStagingError::MultiplicationCheckFailed {
                            check_idx: rnd_idx * STATE_BITS + idx,
                        },
                    )?;

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

        // 3. Active 16-instance Reed-Solomon verification (16 independent field challenges) BEFORE opening `y^(3)`!
        //    Verifies BOTH:
        //      (a) Every relation wire `(lhs, rhs, out)` has degree `<= f`
        //      (b) Every quadratic relation `lhs(0) * rhs(0) + out(0) == 0` holds (`deg <= 2f` & `P(0) == 0`)
        let num_rels = rel_lhs[0].len();
        // Fix the proof masks before any challenge is sampled. These local polynomial
        // dealings construct their stated degree and zero-constant invariants; a wire
        // transport must preserve those same dealing checks at each recipient.
        let mut check_masks_f = SecretBuffer(vec![vec![[0u64; 8]; n]; GF256_CHECK_REPS]);
        let mut check_masks_2f = SecretBuffer(vec![vec![[0u64; 8]; n]; GF256_CHECK_REPS]);
        for rep in 0..GF256_CHECK_REPS {
            for dealer_rng in party_rngs.iter_mut().take(n) {
                let mut m_sec = [0u64; 8];
                for pl in &mut m_sec {
                    *pl = dealer_rng.next_u64();
                }
                let mf_sh = share_bs_gf256_degree(&m_sec, f, &powers_f, dealer_rng);
                wipe_u64s(&mut m_sec);
                let z_sh = share_bs_gf256_degree(&[0u64; 8], 2 * f, &powers_2f, dealer_rng);
                for p in 0..n {
                    bs_xor_assign(&mut check_masks_f[rep][p], &mf_sh[p]);
                    bs_xor_assign(&mut check_masks_2f[rep][p], &z_sh[p]);
                }
            }
        }

        // Salted participant commitments bind every relation and proof mask to this
        // batch. No participant's secret wire is reconstructed to compute its digest.
        let batch_be = (batch_idx as u64).to_be_bytes();
        let mut relation_commits = vec![[0u8; 32]; n];
        for p in 0..n {
            let mut salt = party_rngs[p].next_bytes32();
            let mut xof = Cshake256Xof::new_shake256();
            xof.absorb(b"QSAG.QUORUM.QSB.RELATIONS/v1");
            xof.absorb(&session_id);
            xof.absorb(&batch_be);
            xof.absorb(&(p as u64).to_be_bytes());
            xof.absorb(&(num_rels as u64).to_be_bytes());
            xof.absorb(&salt);
            for rows in [&rel_lhs[p], &rel_rhs[p], &rel_out[p]] {
                for row in rows {
                    for word in row {
                        xof.absorb(&word.to_le_bytes());
                    }
                }
            }
            for rep in 0..GF256_CHECK_REPS {
                for row in [&check_masks_f[rep][p], &check_masks_2f[rep][p]] {
                    for word in row {
                        xof.absorb(&word.to_le_bytes());
                    }
                }
            }
            xof.squeeze(&mut relation_commits[p]);
            wipe_bytes32(&mut salt);
        }
        let chal_digest = h32(
            b"QSAG.QUORUM.QSB.BATCH.CHAL/v1",
            &[
                &session_id,
                &pk_seed,
                &batch_be,
                relation_commits.as_flattened(),
            ],
        );
        let chal_seed =
            coin_toss_public_seed(&session_id, "qsb_gate_verify", &chal_digest, party_rngs)?;
        let mut weights = vec![0u8; GF256_CHECK_REPS * 3 * num_rels];
        expand(
            b"QSAG.QUORUM.QSB.GATE.WEIGHTS/v1",
            &[&session_id, &chal_seed],
            &mut weights,
        );

        for rep in 0..GF256_CHECK_REPS {
            let mask_f = &check_masks_f[rep];
            let z_2f = &check_masks_2f[rep];
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
                    PublicGf256Matrix::from_public_scalar(wl)
                        .scale_xor_into(&mut lin_acc, &rel_lhs[p][r]);
                    PublicGf256Matrix::from_public_scalar(wr)
                        .scale_xor_into(&mut lin_acc, &rel_rhs[p][r]);
                    PublicGf256Matrix::from_public_scalar(wo)
                        .scale_xor_into(&mut lin_acc, &rel_out[p][r]);

                    if wo.0 != 0 {
                        let prod = bs_gf256_mul_planes_ct(&rel_lhs[p][r], &rel_rhs[p][r]);
                        let err_2f = bs_xor(&prod, &rel_out[p][r]);
                        PublicGf256Matrix::from_public_scalar(wo)
                            .scale_xor_into(&mut quad_acc, &err_2f);
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
            let bit_shares: Vec<BitslicedGf256x64> = (0..n).map(|p| cur_planes_sh[p][b]).collect();
            let rec =
                reconstruct_and_verify_bs_degree(&bit_shares, f, &eval_pts, &zero_w_f, &extrap_w_f)
                    .ok_or(DealerlessStagingError::EndpointOpeningDegreeMismatch {
                        batch: batch_idx,
                    })?;
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
    for (p, p_mac_keys) in mac_keys.into_inner().into_iter().enumerate() {
        let mut final_leaves = vec![vec![[0u8; 32]; LEAF_SHARE_NODES]; num_leaves];
        for (b_idx, (dst, src)) in final_leaves
            .iter_mut()
            .flatten()
            .flatten()
            .zip(party_leaves_deg_f[p].iter().flatten().flatten())
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
    let tree = Arc::new(per_party_trees.into_iter().next().ok_or(
        DealerlessStagingError::Quorum(QuorumError::InvalidConfig("empty party set")),
    )?);

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
                PublicGf256Matrix::from_public_scalar(basis)
                    .scale_xor_into(&mut byte_plane, &planes_sh[p][8 * byte_idx + bit]);
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

fn validate_leaf_table(
    leaves: &[Vec<Node>],
    expected_leaves: usize,
) -> Result<(), DealerlessStagingError> {
    if leaves.len() != expected_leaves || leaves.iter().any(|leaf| leaf.len() != LEAF_SHARE_NODES) {
        return Err(QuorumError::InvalidConfig("refresh share table shape mismatch").into());
    }
    Ok(())
}

/// Check the rotated MAC key table before any custodian state changes, so the commit phase
/// of a live refresh cannot stop between two custodians.
fn validate_mac_key_table(keys: &mut [Vec<Node>], n: usize) -> Result<(), DealerlessStagingError> {
    if keys.len() != n || keys.iter().any(|row| row.len() != n) {
        for row in keys.iter_mut() {
            for key in row.iter_mut() {
                wipe_bytes32(key);
            }
        }
        return Err(QuorumError::InvalidConfig("refresh MAC key table shape mismatch").into());
    }
    Ok(())
}

/// Replace each old share byte in place and erase the consumed mask. This wipes
/// owned memory, not compiler copies, registers or external snapshots.
fn apply_and_wipe_leaf_mask_in_place(leaves: &mut [Vec<Node>], mask: &mut [u8]) {
    assert_eq!(
        leaves.iter().map(|l| l.len() * 32).sum::<usize>(),
        mask.len()
    );
    for (dst, &m) in leaves.iter_mut().flatten().flatten().zip(mask.iter()) {
        let updated = black_box(*dst) ^ black_box(m);
        qsag_asm::volatile_fill(core::slice::from_mut(dst), updated);
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
                &[
                    session_id, &c_be, &u_be, &v_be, &com_u, &com_v, &share_u, &share_v,
                ],
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

    if *layout != CommitteeLayout::new(layout.t, layout.n, layout.height)? {
        return Err(QuorumError::InvalidConfig("inconsistent committee layout").into());
    }
    let expected_pk = *custodians[0].tree().public_key();
    for (p, custodian) in custodians.iter_mut().enumerate() {
        if custodian.party() != p
            || custodian.layout() != layout
            || *custodian.tree().public_key() != expected_pk
        {
            return Err(QuorumError::InvalidConfig("refresh custodian context mismatch").into());
        }
        for (committee, members) in layout.committees().iter().enumerate() {
            if members.contains(&p) {
                validate_leaf_table(
                    custodian.slot_leaves_mut(committee)?,
                    layout.leaves_per_committee() as usize,
                )?;
            }
        }
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

    let mut new_mac_keys = establish_dealerless_pairwise_mac_keys(&session_id, party_rngs)?;
    validate_mac_key_table(&mut new_mac_keys, n)?;

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
    for (custodian, keys) in custodians.iter_mut().zip(new_mac_keys.into_inner()) {
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
    if staged.layout
        != CommitteeLayout::new(staged.layout.t, staged.layout.n, staged.layout.height)?
        || staged.tree.public_key().height != staged.layout.height
    {
        return Err(QuorumError::InvalidConfig("inconsistent committee layout").into());
    }
    for (p, mat) in staged.parties.iter_mut().enumerate() {
        let expected: Vec<usize> = staged
            .layout
            .committees()
            .iter()
            .enumerate()
            .filter_map(|(c, members)| members.contains(&p).then_some(c))
            .collect();
        let mut actual: Vec<usize> = mat
            .stores
            .iter()
            .map(CommitteeShareStore::committee)
            .collect();
        actual.sort_unstable();
        if mat.party != p || actual != expected {
            return Err(QuorumError::InvalidConfig("refresh material membership mismatch").into());
        }
        for store in &mut mat.stores {
            validate_leaf_table(
                store.leaves_mut(),
                staged.layout.leaves_per_committee() as usize,
            )?;
        }
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

    for ((committee, members), mut masks) in
        staged.layout.committees().iter().enumerate().zip(all_masks)
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
    for (mat, keys) in staged.parties.iter_mut().zip(new_mac_keys.into_inner()) {
        mat.replace_mac_keys(keys);
    }
    Ok(())
}

/// Proactively refresh all live `QS-B` [`ShamirCustodian`] share tables AND pairwise channel MAC
/// keys in place via HVZK-verified degree-`< t` zero-constant `GF(2^8)` polynomials (`P(0) = 0`),
/// preserving `pk_root` and `BeltLatch` state while re-randomizing the stored sharings.
/// Mobile-adversary secrecy additionally requires erasure and a corruption schedule
/// that does not expose enough refresh masks to translate shares between epochs.
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
    let n = cfg.parties();
    if custodians.len() != n || party_rngs.len() != n {
        return Err(DealerlessStagingError::PartyCountMismatch {
            expected: n,
            got: custodians.len().min(party_rngs.len()),
        });
    }
    let expected_pk = *custodians[0].tree().public_key();
    for (p, custodian) in custodians.iter_mut().enumerate() {
        if custodian.party() != p
            || custodian.config() != cfg
            || *custodian.tree().public_key() != expected_pk
        {
            return Err(QuorumError::InvalidConfig("refresh custodian context mismatch").into());
        }
        validate_leaf_table(custodian.leaves_mut(), 1usize << expected_pk.height)?;
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
    let mut new_mac_keys = establish_dealerless_pairwise_mac_keys(&session_id, party_rngs)?;
    validate_mac_key_table(&mut new_mac_keys, n)?;

    // Every share table moves to the new sharing before any key is replaced: a partially
    // applied zero-constant mask would leave no quorum able to reconstruct.
    for (p, custodian) in custodians.iter_mut().enumerate() {
        apply_and_wipe_leaf_mask_in_place(custodian.leaves_mut(), &mut zero_masks[p]);
    }
    for (custodian, keys) in custodians.iter_mut().zip(new_mac_keys.into_inner()) {
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
    let n = staged.cfg.parties();
    if staged.parties.len() != n || party_rngs.len() != n {
        return Err(DealerlessStagingError::PartyCountMismatch {
            expected: n,
            got: party_rngs.len(),
        });
    }
    let num_leaves = 1usize << staged.tree.public_key().height;
    for (p, mat) in staged.parties.iter_mut().enumerate() {
        if mat.party != p {
            return Err(QuorumError::InvalidConfig("refresh material membership mismatch").into());
        }
        validate_leaf_table(mat.leaves_mut(), num_leaves)?;
    }
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

    for (p, (mat, keys)) in staged
        .parties
        .iter_mut()
        .zip(new_mac_keys.into_inner())
        .enumerate()
    {
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

    #[test]
    fn eight_way_stream_expansion_equals_the_scalar_stream() {
        let backend = qsag_asm::detect_backend();
        // Message lengths around the 136-byte block boundary, outputs around the 17-word one.
        for extra in [0usize, 1, 60, 97, 98, 99, 233, 234, 235] {
            for words in [1usize, 16, 17, 18, 34, 35, 300] {
                for lanes in [1usize, 3, 8] {
                    let tails: Vec<Vec<u8>> = (0..lanes)
                        .map(|l| {
                            (0..extra)
                                .map(|i| (i as u8).wrapping_mul(31) ^ l as u8)
                                .collect()
                        })
                        .collect();
                    let lane_ids: Vec<[u8; 8]> =
                        (0..lanes).map(|l| (l as u64).to_le_bytes()).collect();
                    let msgs: Vec<SecretBuffer<Vec<u8>>> = (0..lanes)
                        .map(|l| stream_message(b"x8-test", &[&lane_ids[l], &tails[l]]))
                        .collect();
                    let mut got = vec![vec![0u64; words]; lanes];
                    let mut outs: Vec<&mut [u64]> = got.iter_mut().map(Vec::as_mut_slice).collect();
                    expand_u64_streams_x8(&msgs, &mut outs, backend);
                    for l in 0..lanes {
                        let mut want = vec![0u64; words];
                        expand_u64_stream(b"x8-test", &[&lane_ids[l], &tails[l]], &mut want);
                        assert_eq!(got[l], want, "extra {extra} words {words} lane {l}");
                    }
                }
            }
        }
    }
    use crate::party_node::{IsolatedJortsParty, IsolatedQuorumParty};
    use crate::quorum_jorts::{
        BftShamirJorts, CommitteePartitionedJorts, LatchCertificate, QuorumJortsSig, chain_step,
        combine_additive, combine_shamir, quorum_jorts_verify, verify_jorts_signature,
    };
    use crate::wire_channel::InMemoryWireMesh;
    use qsag_core::belt_latch::MemoryWal;

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
    fn refresh_rejects_misordered_or_mismatched_custodians_before_mutation() {
        use crate::quorum_jorts::{stage_bft_shamir, stage_committee_partitioned};
        let cfg = QuorumConfig::tight(2).unwrap();
        let mut qsb =
            BftShamirJorts::from_staged(stage_bft_shamir(cfg, 1, &[0x91; 32]).unwrap()).unwrap();
        let mut rngs = make_party_rngs(cfg.parties(), 0x92);
        qsb.custodians.swap(0, 1);
        assert!(
            refresh_bft_shamir_shares(&cfg, &mut qsb.custodians, [0x93; 32], &mut rngs).is_err()
        );
        qsb.custodians.swap(0, 1);
        let wrong_cfg = QuorumConfig::new(3, 4, 1).unwrap();
        assert!(
            refresh_bft_shamir_shares(&wrong_cfg, &mut qsb.custodians, [0x94; 32], &mut rngs)
                .is_err()
        );
        let sig = qsb
            .sign(&[0, 1, 2], b"unchanged after rejected context")
            .unwrap();
        assert!(verify_jorts_signature(
            qsb.public_key(),
            b"unchanged after rejected context",
            &sig
        ));

        let mut qsa = CommitteePartitionedJorts::from_staged(
            stage_committee_partitioned(2, 3, 2, &[0x95; 32]).unwrap(),
        )
        .unwrap();
        let mut rngs = make_party_rngs(3, 0x96);
        qsa.custodians.swap(0, 1);
        assert!(
            refresh_committee_shares(&qsa.layout, &mut qsa.custodians, [0x97; 32], &mut rngs)
                .is_err()
        );
        qsa.custodians.swap(0, 1);
        assert!(matches!(
            refresh_committee_shares_inner(
                &qsa.layout,
                &mut qsa.custodians,
                [0x98; 32],
                &mut rngs,
                Some(StagingFault::CorruptQsARefreshOpen {
                    committee: 0,
                    member_pos: 1
                }),
            ),
            Err(DealerlessStagingError::CommitmentMismatch { .. })
        ));
        let sig = qsa
            .sign(&[0, 1], b"unchanged after rejected refresh")
            .unwrap();
        assert!(verify_jorts_signature(
            qsa.public_key(),
            b"unchanged after rejected refresh",
            &sig
        ));
    }

    #[test]
    fn staged_refresh_rejects_missing_committee_or_misordered_party() {
        use crate::quorum_jorts::{stage_bft_shamir, stage_committee_partitioned};
        let mut qsa = stage_committee_partitioned(2, 3, 2, &[0xa1; 32]).unwrap();
        let saved = qsa.parties[0].stores.pop().unwrap();
        let mut rngs = make_party_rngs(3, 0xa2);
        assert!(refresh_staged_committee_keys(&mut qsa, [0xa3; 32], &mut rngs).is_err());
        qsa.parties[0].stores.push(saved);
        refresh_staged_committee_keys(&mut qsa, [0xa4; 32], &mut rngs).unwrap();
        let mut qsa = CommitteePartitionedJorts::from_staged(qsa).unwrap();
        let sig = qsa.sign(&[0, 1], b"refreshed staged committee").unwrap();
        assert!(verify_jorts_signature(
            qsa.public_key(),
            b"refreshed staged committee",
            &sig
        ));

        let cfg = QuorumConfig::tight(2).unwrap();
        let mut qsb = stage_bft_shamir(cfg, 1, &[0xa5; 32]).unwrap();
        let mut rngs = make_party_rngs(cfg.parties(), 0xa6);
        qsb.parties.swap(0, 1);
        assert!(refresh_staged_bft_shamir_keys(&mut qsb, [0xa7; 32], &mut rngs).is_err());
        qsb.parties.swap(0, 1);
        refresh_staged_bft_shamir_keys(&mut qsb, [0xa8; 32], &mut rngs).unwrap();
        let mut qsb = BftShamirJorts::from_staged(qsb).unwrap();
        let sig = qsb.sign(&[0, 1, 2], b"refreshed staged shamir").unwrap();
        assert!(verify_jorts_signature(
            qsb.public_key(),
            b"refreshed staged shamir",
            &sig
        ));
    }

    #[test]
    fn bitsliced_chain_step_matches_scalar_chain_step_bit_for_bit() {
        let mut rngs = make_party_rngs(1, 0x10);
        let pk_seed = rngs[0].next_bytes32();
        let coords: Vec<(u64, u32)> = (0..64)
            .map(|i| ((i / 16) as u64, (i % 16) as u32))
            .collect();
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
        let _memory = crate::test_budget::reserve_mb(2200);
        let mut rngs = make_party_rngs(3, 0x21);
        let staged = stage_committee_partitioned_dealerless_mpc(2, 3, 2, [0x41; 32], &mut rngs)
            .expect("QS-A MPC");
        let pk = *staged.tree.public_key();
        let mut qsa = CommitteePartitionedJorts::from_staged(staged).unwrap();
        let msg = b"committee zero across refresh";
        let before = qsa.sign(&[0, 1], msg).expect("pre-refresh sign");
        assert!(verify_jorts_signature(&pk, msg, &before));

        let old_echo = qsa.custodians[1].echo_for(0, 0).unwrap();
        let old_permit = qsa.custodians[0].verify_echoes(0, &[old_echo]).unwrap();
        let stale = qsa.custodians[0].open(&old_permit).unwrap();
        let mut refresh_rngs = make_party_rngs(3, 0x23);
        refresh_committee_shares(
            &qsa.layout,
            &mut qsa.custodians,
            [0x99; 32],
            &mut refresh_rngs,
        )
        .expect("refresh QS-A");
        assert_eq!(*qsa.public_key(), pk);
        let after = qsa.sign_at(0, 0, msg).expect("post-refresh replay");
        assert!(verify_jorts_signature(&pk, msg, &after));
        assert_eq!(
            before, after,
            "refresh preserves the canonical signature bytes"
        );

        let record = qsa.custodians[0].bind(0, 0, msg).unwrap();
        let echo = qsa.custodians[0].echo_for(0, 1).unwrap();
        let permit = qsa.custodians[1].verify_echoes(0, &[echo]).unwrap();
        let fresh = qsa.custodians[1].open(&permit).unwrap();
        assert!(matches!(
            combine_additive(&qsa.tree, &record, &[0, 1], &[stale, fresh]),
            Err(QuorumError::ChainVerifyFailed { .. })
        ));

        // The other two committees sign previously unused leaves after refresh.
        for (idx, members) in [[0usize, 2], [1, 2]].iter().enumerate() {
            let msg = alloc::format!("refreshed-committee-{idx}");
            let start = std::time::Instant::now();
            let sig = qsa
                .sign(members, msg.as_bytes())
                .expect("post-refresh new signature");
            std::eprintln!("QS-A online signature: {} us", start.elapsed().as_micros());
            assert!(verify_jorts_signature(&pk, msg.as_bytes(), &sig));
            assert!(quorum_jorts_verify(&pk, msg.as_bytes(), &sig));
        }
    }

    #[test]
    fn dealerless_qs_b_stages_signs_switches_quorums_and_refreshes() {
        let _memory = crate::test_budget::reserve_mb(250);
        for t in [2usize, 3] {
            let cfg = QuorumConfig::tight(t).expect("tight config");
            let mut rngs = make_party_rngs(cfg.parties(), 0x30 + t as u8);
            let staged = stage_bft_shamir_dealerless_mpc(cfg, 2, [0x51 + t as u8; 32], &mut rngs)
                .expect("QS-B MPC");
            let pk = *staged.tree.public_key();
            let mut qs_b = BftShamirJorts::from_staged(staged).expect("from_staged");

            let ackers_0: Vec<usize> = (0..cfg.quorum()).collect();
            let signers_0: Vec<usize> = (0..cfg.threshold()).collect();
            let t0 = std::time::Instant::now();
            let sig0 = qs_b
                .sign_at(&ackers_0, &signers_0, 0, b"dealerless-qs-b-epoch-0")
                .expect("sign 0");
            let elapsed = t0.elapsed();
            assert!(verify_jorts_signature(
                &pk,
                b"dealerless-qs-b-epoch-0",
                &sig0
            ));
            std::eprintln!("QS-B t={t} online signature: {} us", elapsed.as_micros());

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
            let stale_openings: Vec<_> = (0..(cfg.threshold() - 1))
                .map(|p| {
                    qs_b.custodians[p]
                        .open(1, b"epoch-1-refresh", &pre_cert)
                        .expect("stale open")
                })
                .collect();

            // Run proactive zero-constant Shamir refresh across all `n` custodians!
            let mut ref_rngs = make_party_rngs(cfg.parties(), 0x40 + t as u8);
            refresh_bft_shamir_shares(&cfg, &mut qs_b.custodians, [0x77; 32], &mut ref_rngs)
                .expect("refresh QS-B");
            assert_eq!(*qs_b.public_key(), pk);

            // Re-certify leaf 1 under rotated MAC keys: post-refresh `t`-quorum succeeds,
            // whereas `(t - 1)` pre-refresh shares + `1` post-refresh share fails `ChainVerifyFailed`!
            let sig1 = qs_b
                .sign_at(&ackers_0, &signers_0, 1, b"epoch-1-refresh")
                .expect("post-refresh leaf 1");
            assert!(verify_jorts_signature(&pk, b"epoch-1-refresh", &sig1));

            let mut post_acks = Vec::new();
            for &p in &ackers_0 {
                let (_, ack) = qs_b.custodians[p]
                    .ack(1, b"epoch-1-refresh")
                    .expect("re-ack");
                post_acks.push(ack);
            }
            let post_cert = LatchCertificate::assemble(&rec1, post_acks);
            let fresh_open_last = qs_b.custodians[cfg.threshold() - 1]
                .open(1, b"epoch-1-refresh", &post_cert)
                .expect("fresh open");

            let mut mixed = stale_openings;
            mixed.push(fresh_open_last);
            let mixed_res = combine_shamir(&cfg, &qs_b.tree, &rec1, &mixed);
            assert!(
                matches!(mixed_res, Err(QuorumError::ChainVerifyFailed { .. })),
                "mixing pre-refresh and post-refresh Shamir shares must fail: {mixed_res:?}"
            );

            // Switch to a different quorum `{n - q .. n}` & signer set `{n - t .. n}` on leaf 2!
            let ackers_2: Vec<usize> = ((cfg.parties() - cfg.quorum())..cfg.parties()).collect();
            let signers_2: Vec<usize> =
                ((cfg.parties() - cfg.threshold())..cfg.parties()).collect();
            let sig2 = qs_b
                .sign_at(&ackers_2, &signers_2, 2, b"dealerless-qs-b-switched")
                .expect("switched sign");
            assert!(verify_jorts_signature(
                &pk,
                b"dealerless-qs-b-switched",
                &sig2
            ));
        }
    }

    #[test]
    fn dealerless_staging_rejects_pk_seed_opening() {
        // 1. Tampered `pk_seed` Round-2 opening in QS-A.
        let mut rngs = make_party_rngs(3, 0x61);
        let res = stage_committee_partitioned_inner(
            2,
            3,
            2,
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
    }

    #[test]
    fn dealerless_qsa_rejects_beaver_corruption() {
        let _memory = crate::test_budget::reserve_mb(550);
        let mut rngs = make_party_rngs(2, 0x62);
        let result = stage_single_committee_subtree_mpc(
            0,
            &[0],
            &[0x32; 32],
            [0x02; 32],
            &mut rngs,
            Some(StagingFault::CorruptQsABeaverBit { committee: 0 }),
        );
        assert!(matches!(
            result,
            Err(DealerlessStagingError::TripleSacrificeFailed { committee: 0 })
        ));
    }

    #[test]
    fn dealerless_qsa_rejects_endpoint_corruption() {
        let _memory = crate::test_budget::reserve_mb(1800);
        let mut rngs = make_party_rngs(2, 0x63);
        let mut writes = 0;
        let res = stage_single_committee_into(
            1,
            StagingSlice {
                leaves: &[0],
                chains: 0..1,
            },
            &[0x31; 32],
            [0x03; 32],
            &mut rngs,
            &mut |_, _, _, _| {
                writes += 1;
                Ok(())
            },
            Some(StagingFault::CorruptQsAEndpointOpen {
                committee: 1,
                member_pos: 1,
            }),
        );
        assert!(matches!(
            res,
            Err(DealerlessStagingError::MacCheckFailed { committee: 1, .. })
        ));
        assert_eq!(
            writes, 0,
            "unauthenticated intermediate pages reached the sink"
        );
    }

    #[cfg(all(target_os = "linux", target_pointer_width = "64"))]
    #[test]
    fn volatile_subset_second_half_abort_publishes_no_pages() {
        let _memory = crate::test_budget::reserve_mb(3800);
        let mut rngs = make_party_rngs(2, 0x6f);
        let mut writes = 0;
        let result = stage_volatile_subset_into_inner(
            &[0],
            &[0x31; 32],
            [0x51; 32],
            &mut rngs,
            &mut |_, _, _, _| {
                writes += 1;
                Ok(())
            },
            Some((
                1,
                StagingFault::CorruptQsAEndpointOpen {
                    committee: 0,
                    member_pos: 1,
                },
            )),
        );
        assert!(matches!(
            result,
            Err(DealerlessStagingError::MacCheckFailed { .. })
        ));
        assert_eq!(
            writes, 0,
            "a successful half escaped before the other half's MAC barrier"
        );
    }

    #[test]
    fn dealerless_qsb_rejects_input_gate_and_endpoint_corruption() {
        // 4. Non-Boolean `GF(2^8)` DKG input (`y_d not in {0, 1}`) in QS-B -> caught before opening!
        let cfg = QuorumConfig::tight(2).expect("cfg");
        let mut rngs = make_party_rngs(cfg.parties(), 0x64);
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
        let mut rngs = make_party_rngs(cfg.parties(), 0x65);
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
        let mut rngs = make_party_rngs(cfg.parties(), 0x66);
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
    }

    #[test]
    fn dealerless_qsb_rejects_refresh_corruption() {
        let cfg = QuorumConfig::tight(2).expect("cfg");
        // 7. Tampered proactive refresh polynomials (`P(0) != 0` and `deg >= t`) rejected intact!
        let mut rngs = make_party_rngs(cfg.parties(), 0x67);
        let staged = stage_bft_shamir_dealerless_mpc(cfg, 1, [0x07; 32], &mut rngs).expect("stage");
        let pk = *staged.tree.public_key();
        let mut qs_b = BftShamirJorts::from_staged(staged).expect("from_staged");

        let mut bad_rngs = make_party_rngs(cfg.parties(), 0x68);
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
            .sign_at(&[0, 1, 2], &[0, 1], 0, b"intact-after-rejected-refresh")
            .expect("intact sign");
        assert!(verify_jorts_signature(
            &pk,
            b"intact-after-rejected-refresh",
            &sig
        ));
    }

    /// Run one QS-A wire session: the members of `committee` sign on their own threads over
    /// a fresh in-memory mesh, the other custodians stay idle. Custodians come back in
    /// party order.
    fn wire_sign_committee(
        custodians: Vec<CommitteeCustodian<MemoryWal>>,
        members: &[usize],
        epoch: u64,
        session: [u8; 32],
        msg: &[u8],
    ) -> (Vec<CommitteeCustodian<MemoryWal>>, QuorumJortsSig) {
        let committee = custodians[0].layout().committee_index(members).unwrap();
        let (endpoints, _stats) = InMemoryWireMesh::connect(custodians.len(), session);
        let mut idle = Vec::new();
        let mut nodes = Vec::new();
        for (custodian, endpoint) in custodians.into_iter().zip(endpoints) {
            if members.contains(&custodian.party()) {
                nodes.push(IsolatedJortsParty::new(custodian, endpoint).unwrap());
            } else {
                idle.push((custodian, endpoint));
            }
        }
        // Nodes are returned from their threads so no link closes before every thread joined.
        let finished: Vec<_> = std::thread::scope(|scope| {
            let handles: Vec<_> = nodes
                .into_iter()
                .map(|mut node| {
                    scope.spawn(move || {
                        let result = node.sign(committee, epoch, msg);
                        (result, node)
                    })
                })
                .collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        });
        let mut signatures = Vec::new();
        let mut custodians: Vec<_> = idle.into_iter().map(|(custodian, _)| custodian).collect();
        for (result, node) in finished {
            signatures.push(result.expect("wire signature"));
            custodians.push(node.into_parts().0);
        }
        custodians.sort_by_key(CommitteeCustodian::party);
        assert!(signatures.iter().all(|s| *s == signatures[0]));
        (custodians, signatures.swap_remove(0))
    }

    /// Dealerless QS-A material drives the isolated wire parties, and a refresh applied
    /// between wire sessions (including a rejected one) keeps them signing under one key.
    #[test]
    fn dealerless_qs_a_material_signs_over_the_wire_across_refresh() {
        let _memory = crate::test_budget::reserve_mb(2200);
        let mut rngs = make_party_rngs(3, 0xb1);
        let staged = stage_committee_partitioned_dealerless_mpc(2, 3, 2, [0xb2; 32], &mut rngs)
            .expect("QS-A MPC");
        let pk = *staged.tree.public_key();
        let layout = staged.layout.clone();
        let tree = staged.tree.clone();
        let custodians: Vec<CommitteeCustodian<MemoryWal>> = staged
            .parties
            .into_iter()
            .map(|material| {
                let wals = vec![MemoryWal::new(); material.stores.len()];
                CommitteeCustodian::new(layout.clone(), tree.clone(), material, wals).unwrap()
            })
            .collect();

        // Height 2 gives each of the three committees exactly one leaf.
        let (mut custodians, before) =
            wire_sign_committee(custodians, &[0, 1], 0, [0xc1; 32], b"wire before refresh");
        assert!(verify_jorts_signature(&pk, b"wire before refresh", &before));

        // A refresh that aborts leaves shares and channel keys usable over the wire.
        let mut bad_rngs = make_party_rngs(3, 0xb3);
        assert!(matches!(
            refresh_committee_shares_inner(
                &layout,
                &mut custodians,
                [0xc2; 32],
                &mut bad_rngs,
                Some(StagingFault::CorruptQsARefreshOpen {
                    committee: 0,
                    member_pos: 0
                }),
            ),
            Err(DealerlessStagingError::CommitmentMismatch { .. })
        ));
        let (mut custodians, sig) = wire_sign_committee(
            custodians,
            &[0, 2],
            0,
            [0xc3; 32],
            b"wire after aborted refresh",
        );
        assert!(verify_jorts_signature(
            &pk,
            b"wire after aborted refresh",
            &sig
        ));

        let mut refresh_rngs = make_party_rngs(3, 0xb4);
        refresh_committee_shares(&layout, &mut custodians, [0xc4; 32], &mut refresh_rngs)
            .expect("refresh QS-A");

        // Rotated shares and rotated MAC keys sign a leaf that was never opened before.
        let (custodians, sig) =
            wire_sign_committee(custodians, &[1, 2], 0, [0xc5; 32], b"wire after refresh");
        assert!(verify_jorts_signature(&pk, b"wire after refresh", &sig));
        // The already bound leaf re-opens to the same signature from the rotated shares.
        let (_custodians, replay) =
            wire_sign_committee(custodians, &[0, 1], 0, [0xc6; 32], b"wire before refresh");
        assert_eq!(replay, before);
    }

    /// Run one QS-B wire session with the custodians in `online`; the rest stay idle.
    fn wire_sign_quorum(
        custodians: Vec<ShamirCustodian<MemoryWal>>,
        online: &[usize],
        openers: &[usize],
        leaf: u64,
        session: [u8; 32],
        msg: &[u8],
    ) -> (Vec<ShamirCustodian<MemoryWal>>, QuorumJortsSig) {
        let (endpoints, _stats) = InMemoryWireMesh::connect(custodians.len(), session);
        let mut idle = Vec::new();
        let mut nodes = Vec::new();
        for (custodian, endpoint) in custodians.into_iter().zip(endpoints) {
            if online.contains(&custodian.party()) {
                nodes.push(IsolatedQuorumParty::new(custodian, endpoint).unwrap());
            } else {
                idle.push((custodian, endpoint));
            }
        }
        let finished: Vec<_> = std::thread::scope(|scope| {
            let handles: Vec<_> = nodes
                .into_iter()
                .map(|mut node| {
                    scope.spawn(move || {
                        let result = node.sign(online, openers, leaf, msg);
                        (result, node)
                    })
                })
                .collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        });
        let mut signatures = Vec::new();
        let mut custodians: Vec<_> = idle.into_iter().map(|(custodian, _)| custodian).collect();
        for (result, node) in finished {
            let outcome = result.expect("wire signature");
            assert!(outcome.blamed.is_empty());
            signatures.push(outcome.signature);
            custodians.push(node.into_parts().0);
        }
        custodians.sort_by_key(ShamirCustodian::party);
        assert!(signatures.iter().all(|s| *s == signatures[0]));
        (custodians, signatures.swap_remove(0))
    }

    /// Dealerless QS-B material drives the isolated wire parties across a rejected and an
    /// accepted refresh, with a different quorum and opener set afterwards.
    #[test]
    fn dealerless_qs_b_material_signs_over_the_wire_across_refresh() {
        let cfg = QuorumConfig::tight(2).expect("cfg");
        let n = cfg.parties();
        let mut rngs = make_party_rngs(n, 0xd1);
        let staged = stage_bft_shamir_dealerless_mpc(cfg, 2, [0xd2; 32], &mut rngs).expect("QS-B");
        let pk = *staged.tree.public_key();
        let tree = staged.tree.clone();
        let custodians: Vec<ShamirCustodian<MemoryWal>> = staged
            .parties
            .into_iter()
            .map(|material| {
                ShamirCustodian::new(cfg, tree.clone(), material, MemoryWal::new()).unwrap()
            })
            .collect();

        let first: Vec<usize> = (0..cfg.quorum()).collect();
        let first_openers: Vec<usize> = (0..cfg.threshold()).collect();
        let (mut custodians, sig) = wire_sign_quorum(
            custodians,
            &first,
            &first_openers,
            0,
            [0xe1; 32],
            b"wire before refresh",
        );
        assert!(verify_jorts_signature(&pk, b"wire before refresh", &sig));

        let mut bad_rngs = make_party_rngs(n, 0xd3);
        assert_eq!(
            refresh_bft_shamir_shares_inner(
                &cfg,
                &mut custodians,
                [0xe2; 32],
                &mut bad_rngs,
                Some(StagingFault::CorruptQsBRefreshNonZeroConstant { dealer: 0 }),
            ),
            Err(DealerlessStagingError::ZeroConstantCheckFailed { dealer: 0 })
        );
        let (mut custodians, sig) = wire_sign_quorum(
            custodians,
            &first,
            &first_openers,
            1,
            [0xe3; 32],
            b"wire after aborted refresh",
        );
        assert!(verify_jorts_signature(
            &pk,
            b"wire after aborted refresh",
            &sig
        ));

        let mut refresh_rngs = make_party_rngs(n, 0xd4);
        refresh_bft_shamir_shares(&cfg, &mut custodians, [0xe4; 32], &mut refresh_rngs)
            .expect("refresh QS-B");

        let second: Vec<usize> = ((n - cfg.quorum())..n).collect();
        let second_openers: Vec<usize> = ((n - cfg.threshold())..n).collect();
        let (_custodians, sig) = wire_sign_quorum(
            custodians,
            &second,
            &second_openers,
            2,
            [0xe5; 32],
            b"wire after refresh",
        );
        assert!(verify_jorts_signature(&pk, b"wire after refresh", &sig));
    }

    #[cfg(feature = "std")]
    #[test]
    #[ignore = "retained mesh online MAC latency benchmark"]
    fn bench_qsa_retained_mesh_mac_latency() {
        let mut rngs = make_party_rngs(3, 0x5b);
        let sid = [0xa9; 32];
        let setup = std::time::Instant::now();
        let mut mesh = OtMesh::try_establish(sid, &mut rngs).unwrap();
        let setup_ms = setup.elapsed().as_secs_f64() * 1000.0;
        let deltas = [0x11u128, 0x22, 0x33];
        let opened = [0xdead_beefu64];
        let macs: Vec<_> = deltas
            .iter()
            .map(|&d| {
                vec![core::array::from_fn(|b| {
                    if opened[0] >> b & 1 == 1 { d } else { 0 }
                })]
            })
            .collect();
        // Offline: stage single-use blinding triples for every timed check. Online: the
        // check itself, which pops two triples and never touches the OT channels.
        const CHECKS: usize = 64;
        let refill = std::time::Instant::now();
        mesh.prestage_blinded_checks(CHECKS, &mut rngs).unwrap();
        let refill_ms = refill.elapsed().as_secs_f64() * 1000.0;
        assert_eq!(mesh.staged_blinded_checks(), CHECKS);
        let mut times = Vec::new();
        for step in 0..CHECKS {
            let before = std::time::Instant::now();
            run_committed_spdz_mac_check_words(
                0, step, &sid, &deltas, &opened, &macs, &mut mesh, &mut rngs,
            )
            .unwrap();
            times.push(before.elapsed().as_secs_f64() * 1000.0);
        }
        assert_eq!(mesh.staged_blinded_checks(), 0);
        times.sort_by(f64::total_cmp);
        let online_mean = times.iter().sum::<f64>() / CHECKS as f64;
        // Unstaged use: every eighth check pays an automatic refill inline.
        let mut inline = Vec::new();
        for step in CHECKS..2 * CHECKS {
            let before = std::time::Instant::now();
            run_committed_spdz_mac_check_words(
                0, step, &sid, &deltas, &opened, &macs, &mut mesh, &mut rngs,
            )
            .unwrap();
            inline.push(before.elapsed().as_secs_f64() * 1000.0);
        }
        let inline_mean = inline.iter().sum::<f64>() / CHECKS as f64;
        inline.sort_by(f64::total_cmp);
        std::eprintln!(
            "[BENCH retained QS-A mesh] setup={setup_ms:.3} ms; offline refill of {CHECKS} checks={refill_ms:.3} ms \
             ({:.3} ms amortized per check); online check n={CHECKS} min={:.3} median={:.3} max={:.3} mean={online_mean:.3} ms; \
             online + amortized refill={:.3} ms per check; unstaged (auto-refill inline) n={CHECKS} \
             median={:.3} max={:.3} mean={inline_mean:.3} ms",
            refill_ms / CHECKS as f64,
            times[0],
            times[CHECKS / 2],
            times[CHECKS - 1],
            online_mean + refill_ms / CHECKS as f64,
            inline[CHECKS / 2],
            inline[CHECKS - 1],
        );
    }

    #[test]
    fn qsa_pooled_mac_check_rejects_corrupt_lanes_and_fails_closed() {
        let m = 3usize;
        let sid = [0x93; 32];
        let mut rngs = make_party_rngs(m, 0xa7);
        let mut mesh = OtMesh::try_establish(sid, &mut rngs).expect("establish mesh");
        let deltas = [0x1357_9bdf_0246_8aceu128 << 64 | 0x77, 0x99, 0xaa];
        let opened = [0x0123_4567_89ab_cdefu64, 0xfeed_face_cafe_f00d];
        let mut macs = vec![vec![[0u128; 64]; opened.len()]; m];
        for (u, party_macs) in macs.iter_mut().enumerate() {
            for (w, word) in party_macs.iter_mut().enumerate() {
                for (bit, slot) in word.iter_mut().enumerate() {
                    if (opened[w] >> bit) & 1 == 1 {
                        *slot = deltas[u];
                    }
                }
            }
        }
        mesh.prestage_blinded_checks(2, &mut rngs)
            .expect("prestage");
        let mut step = 0usize;
        let mut check = |opened: &[u64],
                         macs: &[Vec<[u128; 64]>],
                         mesh: &mut OtMesh,
                         rngs: &mut [PartyPrivateRng]| {
            step += 1;
            run_committed_spdz_mac_check_words(0, step, &sid, &deltas, opened, macs, mesh, rngs)
                .map_err(|e| (step, e))
        };
        // Honest checks pass from the staged pool and across an automatic refill.
        for _ in 0..4 {
            check(&opened, &macs, &mut mesh, &mut rngs).expect("honest pooled check");
        }
        // A flipped opened bit in either word, and a shifted MAC share at any party.
        for w in 0..opened.len() {
            let mut bad = opened;
            bad[w] ^= 1 << 17;
            let (step, err) = check(&bad, &macs, &mut mesh, &mut rngs).unwrap_err();
            assert_eq!(
                err,
                DealerlessStagingError::MacCheckFailed { committee: 0, step }
            );
        }
        for u in 0..m {
            let mut bad = macs.clone();
            bad[u][1][5] ^= 1;
            let (step, err) = check(&opened, &bad, &mut mesh, &mut rngs).unwrap_err();
            assert_eq!(
                err,
                DealerlessStagingError::MacCheckFailed { committee: 0, step }
            );
        }
        check(&opened, &macs, &mut mesh, &mut rngs).expect("honest check after rejections");
        assert!(!mesh.blinding_poisoned());
    }

    #[test]
    fn qsa_mac_check_blinds_nonzero_residual_against_delta_leakage() {
        let m = 3usize;
        let sid = [0x91; 32];
        let mut rngs_a = make_party_rngs(m, 0xa1);
        let mut mesh_a = OtMesh::try_establish(sid, &mut rngs_a).expect("establish mesh a");
        let deltas_a = [0x1111_2222_3333_4444_5555_6666_7777_8888u128, 0x99, 0xaa];
        let delta_sum_a = deltas_a.iter().fold(0u128, |acc, &d| acc ^ d);

        // Honest zero residual passes cleanly without revealing raw `sigmas[u]`.
        let opened = [0xdead_beef_cafe_babeu64];
        let mut honest_macs = vec![vec![[0u128; 64]; 1]; m];
        for (u, party_macs) in honest_macs.iter_mut().enumerate() {
            for (bit, slot) in party_macs[0].iter_mut().enumerate() {
                if ((opened[0] >> bit) & 1) == 1 {
                    *slot = deltas_a[u];
                }
            }
        }
        run_committed_spdz_mac_check_words(
            0,
            1,
            &sid,
            &deltas_a,
            &opened,
            &honest_macs,
            &mut mesh_a,
            &mut rngs_a,
        )
        .expect("honest blinded QS-A MAC check must pass");

        // Corrupting bit 0 of `opened` induces a non-zero residual `d = chi_0 * Δ != 0`:
        // the blinded check rejects AND two independent randomizer tapes produce uniform,
        // distinct non-zero `w = R · d` openings independent of `Δ`.
        let bad_opened = [opened[0] ^ 1];
        assert_eq!(
            run_committed_spdz_mac_check_words(
                0,
                2,
                &sid,
                &deltas_a,
                &bad_opened,
                &honest_macs,
                &mut mesh_a,
                &mut rngs_a,
            ),
            Err(DealerlessStagingError::MacCheckFailed {
                committee: 0,
                step: 2,
            })
        );

        let residual_shares = SecretBuffer(vec![delta_sum_a ^ 0x55, 0x55, 0]);
        let mut rngs_1 = make_party_rngs(m, 0xb1);
        let mut rngs_2 = make_party_rngs(m, 0xb2);
        let w1 =
            blind_open_additive_gf128_poly(&sid, "test_blind", &residual_shares, None, &mut rngs_1)
                .expect("blind open 1");
        let w2 =
            blind_open_additive_gf128_poly(&sid, "test_blind", &residual_shares, None, &mut rngs_2)
                .expect("blind open 2");
        assert_ne!(w1, 0);
        assert_ne!(w2, 0);
        assert_ne!(w1, w2);
        assert_ne!(w1, delta_sum_a);
    }
}
