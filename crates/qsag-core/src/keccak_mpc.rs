//! Actively secure distributed `Keccak-f[1600]`, `SHAKE256` / `cSHAKE256`, and sealed
//! NIST FIPS 205 / `Corduroy` / `Baggy` cut-boundary MPC engines:
//!
//! 1. **Active 2-of-3 Replicated Secret Sharing (`RSS`, Araki et al. CCS 2016 + Furukawa–Lindell CCS 2017)**:
//!    64-way cross-instance bitsliced `Keccak-f[1600]` (`64` parallel sponges per permutation) backed by
//!    two-pass polynomial-field verified RSS AND relations and per-cut commit-before-open replicated
//!    share-equality checks (inconsistent replicas emit [`RssSlashingReceipt`]; AND relations
//!    use the statistical field proof).
//! 2. **Dishonest-Majority $t$-of-$n$ SPDZ Shamir `Keccak-f[1600]` (`SpdzSlhMpcCluster`)**:
//!    `BitslicedGf256x64` (`PublicGf256Matrix` Four-Russians Lagrange/extrapolation scaling) paired with
//!    exact 2-lane `Tower128` SPDZ Shamir MAC propagation (`2^{-256}` soundness), single-block FIPS 205
//!    `PRF` / `F` sponge fast path, mandatory pre-cut `MacCheck` **strictly before** revealing cut-boundary
//!    shares (`[P0-08]`), and permanent `vault.poison_and_wipe()` on abort (`[P0-07]`).
//! 3. **Distributed `Corduroy` / `Baggy` Custody & `DkgCachedSubtrees::build_distributed`**:
//!    Zero `PqSecretKey` / `SlhSecretKey` reconstruction anywhere (`0` central RAM shortcuts).

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;
use core::hint::black_box;
use core::sync::atomic::{AtomicBool, AtomicU8, AtomicU64, Ordering};

use crate::dkg::ShamirSeedShare256;
use crate::field::tower::{
    BitslicedGf256x64, Tower128, TowerGf256, bs_gf256_extract_lane, bs_gf256_insert_lane,
    bs_gf256_mul_planes_ct, bs_gf256_xor, bs_gf256_xor_assign, lagrange_weights_zero_gf256,
    wipe_tower128,
};
use crate::fips205::{
    CutBoundaryMacToken, Fips205Adrs, Fips205AdrsType, Fips205Error, Fips205Params, SlhBlock,
    SlhMpcOracles, sealed_mpc_oracles, try_wots_base16_digits_and_csum,
};
use crate::preprocessing::{
    OtMesh, PartyPrivateRng, PreprocessError, PreprocessedKeccakPartyVault,
    commit_and_open_spdz_bs_gf256_batch_quorum, run_commit_and_open_coin,
    spdz_authenticate_bs_gf256_words, validate_all_eval_points_gf256,
};
use crate::sponge::keccak::{
    Cshake256WordStream4, Cshake256Xof, KECCAK_ROTATION_OFFSETS, KECCAK_ROUND_CONSTANTS,
    SHAKE256_RATE_BYTES, cshake256_32, cshake256_32_multi_frame, encode_multi_frame,
};
use crate::tsw_baggy::{
    AdrsKind, Cshake256Suite, ForsTreeOpening, HashAdrs, LayerXmssSig, PQ_CSHAKE_SUITE_CUSTOM,
    PqHashParams, PqHashSig, TAG_PRF, TAG_TH_F, build_single_secret32_template,
    PqPublicKey, TweakableHashSuite, build_merkle_from_leaves_topdown, canonical_target_sum,
    check_target_sum,
    derive_stateless_leaf_and_fors_indices, extract_base_w_digits_checked, th_chain_f,
    th_hash_internal_node,
    th_pre_hash, th_tweak_tl, verify_pq_hash_sig, walk_merkle_auth_path,
};
use crate::wipe::{
    SecretBuffer, ct_eq_bytes, ct_eq_bytes32, ct_eq_u64, secret_vec_extend_from_slice,
    secret_vec_push, wipe_bytes, wipe_bytes32, wipe_u64s,
};

/// Overflow-safe active-lane bitmask for 64-way bitsliced batches (`batch_len == 64 -> u64::MAX`,
/// `batch_len == 0 -> 0`, never executing `1u64 << 64`).
#[inline]
pub const fn batch_active_mask(batch_len: usize) -> u64 {
    if batch_len == 0 {
        0
    } else if batch_len >= 64 {
        u64::MAX
    } else {
        (1u64 << batch_len) - 1
    }
}

/// Errors emitted by distributed `Keccak-f[1600]` MPC execution (RSS and SPDZ Shamir).
type RssCutShares = ([[u64; 256]; 3], [[u64; 256]; 3]);
/// Lane-0 and lane-1 `Tower128` MAC shares of the 64 values packed in one word.
type SpdzMacWord = [[Tower128; 64]; 2];
/// Per-party instance-bitsliced shares and MAC shares, one word per bit position.
type SpdzBitShares = (Vec<Vec<BitslicedGf256x64>>, Vec<Vec<SpdzMacWord>>);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KeccakMpcError {
    InvalidBatchSize(usize),
    InvalidParameters,
    Preprocess(PreprocessError),
    RssCommitMismatch {
        accused_party: usize,
    },
    RssShareEqualityFailed(RssSlashingReceipt),
    RssSacrificeFailed,
    SpdzMacAbort,
    SubtreeCacheCapExceeded {
        requested: usize,
        max_allowed: usize,
    },
    GrindExhausted,
    PostVerifyFailed,
    /// An earlier verification, coin flip, commitment or replica check of this engine or
    /// relation accumulator failed. The state is permanent: nothing is evaluated, verified
    /// or opened afterwards.
    Poisoned,
    /// The key shares are not bound to the supplied public key and parameter set (or are
    /// not bound at all, or disagree with each other).
    KeyBindingMismatch,
}

impl From<PreprocessError> for KeccakMpcError {
    fn from(e: PreprocessError) -> Self {
        Self::Preprocess(e)
    }
}

impl fmt::Display for KeccakMpcError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidBatchSize(n) => write!(f, "invalid Keccak MPC batch size {}", n),
            Self::InvalidParameters => write!(f, "invalid Keccak MPC threshold/key parameters"),
            Self::Preprocess(e) => write!(f, "preprocessing/SPDZ error: {}", e),
            Self::RssCommitMismatch { accused_party } => {
                write!(
                    f,
                    "RSS share opening commitment mismatch from party {}",
                    accused_party
                )
            }
            Self::RssShareEqualityFailed(rec) => write!(
                f,
                "RSS replicated share mismatch on slot {} between primary party {} and secondary party {}",
                rec.share_slot, rec.primary_party, rec.secondary_party
            ),
            Self::RssSacrificeFailed => write!(f, "RSS Boolean-product consistency proof failed"),
            Self::SpdzMacAbort => write!(
                f,
                "SPDZ 2-lane Tower128 MacCheck aborted before cut opening"
            ),
            Self::SubtreeCacheCapExceeded {
                requested,
                max_allowed,
            } => write!(
                f,
                "distributed subtree cache leaf count {} exceeds cap {}",
                requested, max_allowed
            ),
            Self::GrindExhausted => write!(f, "TSW target-sum grind budget exhausted"),
            Self::PostVerifyFailed => write!(f, "post-MPC signature verification failed"),
            Self::Poisoned => write!(f, "RSS engine poisoned by an earlier failed check"),
            Self::KeyBindingMismatch => write!(
                f,
                "RSS key shares are not bound to this public key and parameter set"
            ),
        }
    }
}

impl core::error::Error for KeccakMpcError {}

/// Attributable fault receipt when two replicated holders of share slot `j in 0..3` broadcast
/// conflicting values after commitment lock.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RssSlashingReceipt {
    pub share_slot: usize,
    pub primary_party: usize,
    pub secondary_party: usize,
}

// ============================================================================
// 1. Active 2-of-3 Replicated Secret Sharing (`RSS`) 64-Way `Keccak-f[1600]`
// ============================================================================

/// Isolated 2-of-3 RSS custody share for party `party_id in 0..3`:
/// holds ONLY `(s_{party_id}, s_{(party_id + 1) % 3})` (`!Clone`, redacted `Debug`, wiped on `Drop`).
pub struct RssKeyShare256 {
    pub party_id: usize,
    pub key_len: usize,
    pub pk_seed: [u8; 32],
    sk_seed_primary: [u8; 32],
    sk_seed_secondary: [u8; 32],
    sk_prf_primary: [u8; 32],
    sk_prf_secondary: [u8; 32],
    prg_seed_primary: [u8; 32],
    prg_seed_secondary: [u8; 32],
    /// Stateless hash-signature key this share belongs to, recorded by
    /// [`DkgCachedSubtrees::build_distributed_rss`] when the public root is first computed
    /// from the shares. `None` until then.
    tsw_binding: Option<TswKeyBinding>,
    /// Identity of the hash-signature key and parameter set this share was generated for,
    /// recorded once by the scheme's key generation (see [`Self::bind_scheme_identity`]).
    scheme_identity: Option<[u8; 32]>,
    slh_params: Option<Fips205Params>,
}

/// Parameter-set digest and public root that a set of RSS key shares was generated for.
#[derive(Clone, Copy, PartialEq, Eq)]
struct TswKeyBinding {
    params_digest: [u8; 32],
    pk_root: [u8; 32],
}

/// Digest of every field of a stateless hash-signature parameter set.
fn tsw_params_digest(params: &PqHashParams) -> [u8; 32] {
    let fields = [
        params.w,
        params.ell1,
        params.subtree_height,
        params.num_layers,
        params.fors_trees,
        params.fors_height,
        params.max_sigs_log2,
        usize::from(params.stateful),
    ];
    let mut bytes = [0u8; 64];
    for (i, field) in fields.into_iter().enumerate() {
        bytes[8 * i..8 * i + 8].copy_from_slice(&(field as u64).to_be_bytes());
    }
    cshake256_32(b"QSAG.TSW.RSS.PARAMS.DIGEST/v1", &bytes)
}

impl fmt::Debug for RssKeyShare256 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "RssKeyShare256(party={}, n={}, [REDACTED])",
            self.party_id, self.key_len
        )
    }
}

impl Drop for RssKeyShare256 {
    fn drop(&mut self) {
        wipe_bytes32(&mut self.sk_seed_primary);
        wipe_bytes32(&mut self.sk_seed_secondary);
        wipe_bytes32(&mut self.sk_prf_primary);
        wipe_bytes32(&mut self.sk_prf_secondary);
        wipe_bytes32(&mut self.prg_seed_primary);
        wipe_bytes32(&mut self.prg_seed_secondary);
    }
}

impl RssKeyShare256 {
    /// The identity recorded by [`Self::bind_scheme_identity`], if any.
    #[inline]
    pub fn scheme_identity(&self) -> Option<&[u8; 32]> {
        self.scheme_identity.as_ref()
    }

    /// Record the identity (a digest of the public key and the full parameter set) of the
    /// hash-signature key this share belongs to. It is recorded once: recording the same
    /// identity again changes nothing, and a different one is refused, so a share cannot be
    /// re-pointed at another parameter set or root. The record lives in this value; a caller
    /// that persists key shares must persist it with them.
    pub fn bind_scheme_identity(&mut self, identity: &[u8; 32]) -> Result<(), KeccakMpcError> {
        if self.slh_params.is_some() { return Err(KeccakMpcError::KeyBindingMismatch); }
        match &self.scheme_identity {
            None => {
                self.scheme_identity = Some(*identity);
                Ok(())
            }
            Some(bound) if ct_eq_bytes32(bound, identity) => Ok(()),
            Some(_) => Err(KeccakMpcError::KeyBindingMismatch),
        }
    }

    #[inline]
    pub(crate) fn sk_seed_shares(&self) -> (&[u8], &[u8]) {
        (
            &self.sk_seed_primary[..self.key_len],
            &self.sk_seed_secondary[..self.key_len],
        )
    }

    #[inline]
    pub(crate) fn sk_prf_shares(&self) -> (&[u8], &[u8]) {
        (
            &self.sk_prf_primary[..self.key_len],
            &self.sk_prf_secondary[..self.key_len],
        )
    }
}

/// Dealerless 2-of-3 RSS key ceremony (`0` central dealer):
/// each party `i in 0..3` samples private additive share `(sk_seed_i, sk_prf_i, prg_seed_i)` and
/// commits-then-opens `pk_seed_i`, delivering share `i` ONLY to parties `i` and `(i + 2) % 3`.
pub fn run_dealerless_rss_dkg_2of3(
    session_id: [u8; 32],
    key_len: usize,
    party_rngs: &mut [PartyPrivateRng; 3],
) -> Result<([RssKeyShare256; 3], [u8; 32]), KeccakMpcError> {
    if key_len != 16 && key_len != 24 && key_len != 32 {
        return Err(KeccakMpcError::InvalidParameters);
    }
    // Round 1: Commit `pk_seed` contributions before any party reveals its contribution
    let mut pk_contribs = [[0u8; 32]; 3];
    let mut pk_salts = SecretBuffer([[0u8; 32]; 3]);
    let mut pk_coms = [[0u8; 32]; 3];
    for i in 0..3 {
        pk_contribs[i] = party_rngs[i].next_bytes32();
        pk_salts[i] = party_rngs[i].next_bytes32();
        let i_be = (i as u64).to_be_bytes();
        pk_coms[i] = cshake256_32_multi_frame(
            b"QSAG.RSS.DKG.PK.COM/v1",
            &[&session_id, &i_be, &pk_salts[i], &pk_contribs[i]],
        );
    }
    // Round 2: Verify `pk_seed` openings
    let mut pk_seed = [0u8; 32];
    for i in 0..3 {
        let i_be = (i as u64).to_be_bytes();
        let exp = cshake256_32_multi_frame(
            b"QSAG.RSS.DKG.PK.COM/v1",
            &[&session_id, &i_be, &pk_salts[i], &pk_contribs[i]],
        );
        wipe_bytes32(&mut pk_salts[i]);
        if !ct_eq_bytes32(&exp, &pk_coms[i]) {
            return Err(KeccakMpcError::RssCommitMismatch { accused_party: i });
        }
        for b in 0..key_len {
            pk_seed[b] ^= pk_contribs[i][b];
        }
    }

    // Pairwise point-to-point share delivery: share `i` goes ONLY to `i` (primary) and `(i + 2) % 3` (secondary)
    let mut sk_seeds = SecretBuffer([[0u8; 32]; 3]);
    let mut sk_prfs = SecretBuffer([[0u8; 32]; 3]);
    let mut prg_seeds = SecretBuffer([[0u8; 32]; 3]);
    for i in 0..3 {
        party_rngs[i].fill_bytes(&mut sk_seeds[i][..key_len]);
        party_rngs[i].fill_bytes(&mut sk_prfs[i][..key_len]);
        prg_seeds[i] = party_rngs[i].next_bytes32();
    }

    let shares = core::array::from_fn(|p| {
        let next = (p + 1) % 3;
        RssKeyShare256 {
            party_id: p,
            key_len,
            pk_seed,
            sk_seed_primary: sk_seeds[p],
            sk_seed_secondary: sk_seeds[next],
            sk_prf_primary: sk_prfs[p],
            sk_prf_secondary: sk_prfs[next],
            prg_seed_primary: prg_seeds[p],
            prg_seed_secondary: prg_seeds[next],
            tsw_binding: None,
            scheme_identity: None,
            slh_params: None,
        }
    });
    for i in 0..3 {
        wipe_bytes32(&mut sk_seeds[i]);
        wipe_bytes32(&mut sk_prfs[i]);
        wipe_bytes32(&mut prg_seeds[i]);
    }
    Ok((shares, pk_seed))
}

/// Sticky failure latch of an RSS engine or relation accumulator.
///
/// It is set through a shared reference, so the code that detects a failure latches it at the
/// point of detection, before any buffer is wiped and before the error propagates. Nothing
/// resets it.
struct RssPoisonLatch(AtomicBool);

impl RssPoisonLatch {
    const fn new() -> Self {
        Self(AtomicBool::new(false))
    }

    fn set(&self) {
        self.0.store(true, Ordering::Relaxed);
    }

    fn is_set(&self) -> bool {
        self.0.load(Ordering::Relaxed)
    }

    /// Latches and returns `err`.
    fn fail<T>(&self, err: KeccakMpcError) -> Result<T, KeccakMpcError> {
        self.set();
        Err(err)
    }
}

/// Commit-before-open + replicated share-equality check across 3 RSS parties on `words_len` `u64` words.
///
/// Every error latches `poison` before the scratch buffer is wiped: a mismatching opening
/// must end the session that produced it.
///
/// Guarantees:
/// 1. No party can adapt its share after seeing an honest party's share (Round-1 `cSHAKE256` commitment).
/// 2. Every share slot `j in 0..3` is cross-checked between `party j` (`primary`) and `party (j + 2) % 3`
///    (`secondary`), catching ANY deviation with **probability 1** when $\le 1$ party is corrupt!
fn rss_commit_and_open_u64_batch(
    session_id: &[u8; 32],
    phase: &'static str,
    primary_shares: &[Vec<u64>; 3],
    secondary_shares: &[Vec<u64>; 3],
    party_rngs: &mut [PartyPrivateRng; 3],
    poison: &RssPoisonLatch,
) -> Result<Vec<u64>, KeccakMpcError> {
    let len = primary_shares[0].len();
    for p in 0..3 {
        if primary_shares[p].len() != len || secondary_shares[p].len() != len {
            return poison.fail(KeccakMpcError::InvalidParameters);
        }
    }
    if len == 0 {
        return Ok(Vec::new());
    }

    let mut salts = [[0u8; 32]; 3];
    let mut coms = [[0u8; 32]; 3];
    let mut packed_buf = vec![0u8; 16 * len];
    for p in 0..3 {
        salts[p] = party_rngs[p].next_bytes32();
        for k in 0..len {
            let o = 16 * k;
            packed_buf[o..o + 8].copy_from_slice(&primary_shares[p][k].to_le_bytes());
            packed_buf[o + 8..o + 16].copy_from_slice(&secondary_shares[p][k].to_le_bytes());
        }
        let mut xof = Cshake256Xof::new(b"QSAG.RSS.U64.OPEN.COM/v1");
        xof.absorb(session_id);
        xof.absorb(&(phase.len() as u64).to_be_bytes());
        xof.absorb(phase.as_bytes());
        xof.absorb(&(p as u64).to_be_bytes());
        xof.absorb(&salts[p]);
        xof.absorb(&packed_buf);
        xof.squeeze(&mut coms[p]);
    }

    for p in 0..3 {
        for k in 0..len {
            let o = 16 * k;
            packed_buf[o..o + 8].copy_from_slice(&primary_shares[p][k].to_le_bytes());
            packed_buf[o + 8..o + 16].copy_from_slice(&secondary_shares[p][k].to_le_bytes());
        }
        let mut xof = Cshake256Xof::new(b"QSAG.RSS.U64.OPEN.COM/v1");
        xof.absorb(session_id);
        xof.absorb(&(phase.len() as u64).to_be_bytes());
        xof.absorb(phase.as_bytes());
        xof.absorb(&(p as u64).to_be_bytes());
        xof.absorb(&salts[p]);
        xof.absorb(&packed_buf);
        wipe_bytes32(&mut salts[p]);
        let mut exp = [0u8; 32];
        xof.squeeze(&mut exp);
        if !ct_eq_bytes32(&exp, &coms[p]) {
            poison.set();
            wipe_bytes(&mut packed_buf);
            for salt in &mut salts {
                wipe_bytes32(salt);
            }
            return Err(KeccakMpcError::RssCommitMismatch { accused_party: p });
        }
    }
    wipe_bytes(&mut packed_buf);

    // Replicated share equality check: `primary_shares[next][k] == secondary_shares[p][k]`
    let mut p = 0;
    while p < 3 {
        let next = (p + 1) % 3;
        for k in 0..len {
            if black_box(primary_shares[next][k] ^ secondary_shares[p][k]) != 0 {
                return poison.fail(KeccakMpcError::RssShareEqualityFailed(RssSlashingReceipt {
                    share_slot: next,
                    primary_party: next,
                    secondary_party: p,
                }));
            }
        }
        p += 1;
    }

    let mut opened = Vec::with_capacity(len);
    let mut k = 0;
    while k < len {
        opened.push(primary_shares[0][k] ^ primary_shares[1][k] ^ primary_shares[2][k]);
        k += 1;
    }
    Ok(opened)
}

/// Session-hedged pairwise stream keys for the 2-of-3 RSS engine.
///
/// Slot `j` is held by party `j` (primary) and party `(j + 2) % 3` (secondary). Every mask or
/// proof stream of slot `j` is keyed by
/// `cSHAKE256(session_id || joint_coin || j || prg_seed_j || sk_seed_j || sk_prf_j)`, where
/// `joint_coin` is a commit-then-open coin to which every party contributes fresh private
/// entropy. Two sessions therefore share a stream key only if they share the session identifier
/// AND every party repeats its private entropy; binding the replicated secret shares makes the
/// key specific to the custody share it protects. Both holders of a slot derive the same key
/// because they hold the same replicated material.
pub(crate) struct RssMaskSession {
    pub(crate) prim: [[u8; 32]; 3],
    pub(crate) sec: [[u8; 32]; 3],
    /// True when every secondary key equals the next party's primary key. The in-process
    /// engine then expands each pairwise stream once instead of once per holder.
    shared: bool,
}

impl Drop for RssMaskSession {
    fn drop(&mut self) {
        for p in 0..3 {
            wipe_bytes32(&mut self.prim[p]);
            wipe_bytes32(&mut self.sec[p]);
        }
    }
}

impl RssMaskSession {
    fn derive(
        session_id: &[u8; 32],
        keys: &[RssKeyShare256; 3],
        party_rngs: &mut [PartyPrivateRng; 3],
    ) -> Result<Self, KeccakMpcError> {
        let coin =
            run_commit_and_open_coin(session_id, b"RSS_MASK_HEDGE_COIN", &[0u8; 32], party_rngs)?;
        let hedge = |slot: usize, prg: &[u8; 32], seed: &[u8; 32], prf: &[u8; 32]| {
            let slot_be = (slot as u64).to_be_bytes();
            cshake256_32_multi_frame(
                b"QSAG.RSS.MASK.HEDGE/v1",
                &[session_id, &coin, &slot_be, prg, seed, prf],
            )
        };
        let prim: [[u8; 32]; 3] = core::array::from_fn(|p| {
            hedge(
                p,
                &keys[p].prg_seed_primary,
                &keys[p].sk_seed_primary,
                &keys[p].sk_prf_primary,
            )
        });
        let sec: [[u8; 32]; 3] = core::array::from_fn(|p| {
            hedge(
                (p + 1) % 3,
                &keys[p].prg_seed_secondary,
                &keys[p].sk_seed_secondary,
                &keys[p].sk_prf_secondary,
            )
        });
        let mut shared = true;
        for p in 0..3 {
            shared &= ct_eq_bytes32(&sec[p], &prim[(p + 1) % 3]);
        }
        Ok(Self { prim, sec, shared })
    }

    /// Rekey both replicas identically before signing a new message. This prevents
    /// a VM snapshot from repeating pairwise masks on a different transcript.
    fn hedge_transcript(&mut self, transcript: &[u8]) {
        for slots in [&mut self.prim, &mut self.sec] {
            for key in slots {
                let mut next = [0; 32];
                crate::preprocessing::HedgedTranscriptRng::derive(key, 0, &[], transcript, &mut next);
                wipe_bytes32(key);
                *key = next;
                wipe_bytes32(&mut next);
            }
        }
    }

    fn stream_seed(key: &[u8; 32], session_id: &[u8; 32], batch_ctr: u64) -> [u8; 72] {
        let mut seed = [0u8; 72];
        seed[..32].copy_from_slice(key);
        seed[32..64].copy_from_slice(session_id);
        seed[64..].copy_from_slice(&batch_ctr.to_le_bytes());
        seed
    }

    /// Chi mask word streams: three primary streams, plus three secondary streams only when a
    /// holder pair disagrees on its key.
    fn chi_streams(
        &self,
        session_id: &[u8; 32],
        batch_ctr: u64,
    ) -> ([Cshake256WordStream4; 3], Option<[Cshake256WordStream4; 3]>) {
        const MID: [u64; 25] =
            const { crate::sponge::keccak::cshake256_static_midstate(b"QSAG.RSS.CHI.MASK/v3") };
        let make = |key: &[u8; 32]| {
            let mut seed = Self::stream_seed(key, session_id, batch_ctr);
            let stream = Cshake256WordStream4::new(&MID, &seed);
            wipe_bytes(&mut seed);
            stream
        };
        let prim = core::array::from_fn(|p| make(&self.prim[p]));
        let sec = if self.shared {
            None
        } else {
            Some(core::array::from_fn(|p| make(&self.sec[p])))
        };
        (prim, sec)
    }
}

/// Pairwise proof-randomness streams. Each draw advances all streams by one field element, so
/// a secondary element equals the next party's primary element whenever the keys agree.
struct RssProofStreams {
    prim: [Cshake256Xof; 3],
    sec: Option<[Cshake256Xof; 3]>,
}

impl RssProofStreams {
    fn new(mask: &RssMaskSession, session_id: &[u8; 32], batch_ctr: u64) -> Self {
        let make = |key: &[u8; 32]| {
            let mut xof = Cshake256Xof::new(b"QSAG.RSS.DZK.ZPRG.POLY/v3");
            let mut seed = RssMaskSession::stream_seed(key, session_id, batch_ctr);
            xof.absorb(&seed);
            wipe_bytes(&mut seed);
            xof
        };
        Self {
            prim: core::array::from_fn(|p| make(&mask.prim[p])),
            sec: if mask.shared {
                None
            } else {
                Some(core::array::from_fn(|p| make(&mask.sec[p])))
            },
        }
    }

    /// `(prim, sec)`: `prim[p]` is party `p`'s element for slot `p`, `sec[p]` its element for
    /// slot `(p + 1) % 3`.
    fn draw(&mut self) -> ([RssProofField; 3], [RssProofField; 3]) {
        let one = |xof: &mut Cshake256Xof| {
            let mut bytes = [0u8; 16];
            xof.squeeze(&mut bytes);
            let v = RssProofField(u128::from_le_bytes(bytes));
            wipe_bytes(&mut bytes);
            v
        };
        let prim: [RssProofField; 3] = core::array::from_fn(|p| one(&mut self.prim[p]));
        let sec = match &mut self.sec {
            Some(streams) => core::array::from_fn(|p| one(&mut streams[p])),
            None => core::array::from_fn(|p| prim[(p + 1) % 3]),
        };
        (prim, sec)
    }

    /// Additive sharing of zero: party `p` contributes `prim[p] + sec[p]`.
    fn zero_share(&mut self) -> [RssProofField; 3] {
        let (prim, sec) = self.draw();
        core::array::from_fn(|p| prim[p].add(sec[p]))
    }
}

/// Recorded 2-of-3 RSS Boolean AND relations awaiting [`verify_rss_boolean_triples_bbcggi19`].
///
/// Index `[s][k]` is the slot-`s` share of relation word `k`; bit `i` of a word belongs to
/// sponge instance `i`, so one word carries 64 relations `a & b == c`. Inactive instances are
/// stored as zero bits, which satisfy the relation trivially (`!Clone`, wiped on `Drop`).
pub(crate) struct RssPendingDzkTriples {
    pub(crate) a: [Vec<u64>; 3],
    pub(crate) b: [Vec<u64>; 3],
    pub(crate) c: [Vec<u64>; 3],
    /// Lane-permutations recorded over the lifetime of this accumulator (never reset).
    lane_perms: u64,
    /// Set when a verification of this accumulator failed. A poisoned accumulator records
    /// nothing and never verifies again, so an emptied relation set cannot pass for a
    /// verified one.
    poison: RssPoisonLatch,
}

impl RssPendingDzkTriples {
    pub(crate) fn new() -> Self {
        Self {
            a: [Vec::new(), Vec::new(), Vec::new()],
            b: [Vec::new(), Vec::new(), Vec::new()],
            c: [Vec::new(), Vec::new(), Vec::new()],
            lane_perms: 0,
            poison: RssPoisonLatch::new(),
        }
    }

    /// True once a verification of this accumulator has failed.
    pub(crate) fn is_poisoned(&self) -> bool {
        self.poison.is_set()
    }

    pub(crate) fn len_words(&self) -> usize {
        self.a[0].len()
    }

    fn clear_and_wipe(&mut self) {
        for s in 0..3 {
            for words in [&mut self.a[s], &mut self.b[s], &mut self.c[s]] {
                wipe_u64s(words);
                words.clear();
            }
        }
    }

    fn pad_to_group(&mut self) {
        let padded = self.len_words().div_ceil(RSS_DZK_GROUP_WORDS) * RSS_DZK_GROUP_WORDS;
        for s in 0..3 {
            self.a[s].resize(padded, 0);
            self.b[s].resize(padded, 0);
            self.c[s].resize(padded, 0);
        }
    }
}

impl Drop for RssPendingDzkTriples {
    fn drop(&mut self) {
        self.clear_and_wipe();
    }
}

// The proof only embeds Boolean values, so it can use the polynomial field
// GF(2)[t]/(t^128 + t^7 + t^2 + t + 1) directly. No conversion of Keccak shares or
// FIPS 205 outputs is involved.
#[derive(Clone, Copy)]
struct RssProofField(u128);

impl RssProofField {
    const ZERO: Self = Self(0);
    const ONE: Self = Self(1);

    fn add(self, rhs: Self) -> Self {
        Self(self.0 ^ rhs.0)
    }

    fn mul(self, rhs: Self) -> Self {
        RssFieldMultiplier::new(rhs).mul(self)
    }

    /// Multiply by the public monomial `t^shift`, `shift < 64`.
    fn mul_t_pow(self, shift: u32) -> Self {
        if shift == 0 {
            return self;
        }
        let lo = self.0 << shift;
        // Fewer than 64 overflow bits, so their reduction has degree below 71.
        let hi = self.0 >> (128 - shift);
        Self(lo ^ hi ^ (hi << 1) ^ (hi << 2) ^ (hi << 7))
    }

    /// Inverse of a public nonzero element: `x^(2^128 - 2)`.
    fn inv_public(self) -> Self {
        let mut acc = Self::ONE;
        let mut sq = self;
        for _ in 1..128 {
            sq = sq.mul(sq);
            acc = acc.mul(sq);
        }
        acc
    }

    fn from_coin(coin: &[u8; 32]) -> Self {
        let mut bytes = [0u8; 16];
        bytes.copy_from_slice(&coin[..16]);
        Self(u128::from_le_bytes(bytes))
    }

    fn nonzero(self) -> Self {
        if self.0 == 0 { Self::ONE } else { self }
    }

    fn ct_eq(self, rhs: Self) -> bool {
        black_box(self.0 ^ rhs.0) == 0
    }
}

/// Fixed operand in the polynomial field used by the active RSS proof.
/// Share the hardware-dispatched arithmetic with the 256-bit RSS engine.
struct RssFieldMultiplier { operand: [u64; 2] }

impl RssFieldMultiplier {
    #[inline]
    fn new(v: RssProofField) -> Self {
        Self { operand: [v.0 as u64, (v.0 >> 64) as u64] }
    }

    #[inline]
    fn mul(&self, x: RssProofField) -> RssProofField {
        let mut out = [0; 2];
        qsag_asm::gf2_128_mul_acc_batch(&mut out,
            &[[x.0 as u64, (x.0 >> 64) as u64]], &[self.operand]);
        RssProofField(u128::from(out[0]) | (u128::from(out[1]) << 64))
    }
}

impl crate::wipe::SecretWipe for RssProofField {
    fn secret_wipe(&mut self) { self.0 = 0; core::hint::black_box(self); }
}

fn wipe_rss_proof_field(values: &mut [RssProofField]) {
    qsag_asm::volatile_fill(values, RssProofField::ZERO);
}

/// Word-index bits bound by the packed sumcheck rounds.
const RSS_DZK_TENSOR_BITS: usize = 6;
/// Relation words per group, `2^RSS_DZK_TENSOR_BITS`.
const RSS_DZK_GROUP_WORDS: usize = 1 << RSS_DZK_TENSOR_BITS;
/// Evaluation points `{0, 1, slope}^RSS_DZK_TENSOR_BITS` per group, `3^RSS_DZK_TENSOR_BITS`.
const RSS_DZK_TERNARY: usize = 3usize.pow(RSS_DZK_TENSOR_BITS as u32);
/// Bit lanes (sponge instances) per relation word.
const RSS_DZK_LANES: usize = 64;
/// Four-word groups whose subset XORs are tabulated when binding a group.
const RSS_DZK_NIBBLES: usize = RSS_DZK_GROUP_WORDS / 4;

/// Expand the `2^r` words of a group indexed by `u` into `3^r` words indexed by
/// `e = sum_l e_l * 3^l`: digit `0` keeps the `u_l = 0` half, digit `1` the `u_l = 1` half,
/// digit `2` their XOR. Works in place: each stage rewrites blocks from the top down, so a
/// block's destination never covers sources that are still unread.
fn rss_ternary_expand(src: &[u64], out: &mut [u64; RSS_DZK_TERNARY]) {
    out[..RSS_DZK_GROUP_WORDS].copy_from_slice(&src[..RSS_DZK_GROUP_WORDS]);
    let mut pow3 = 1usize;
    let mut high = RSS_DZK_GROUP_WORDS;
    for _ in 0..RSS_DZK_TENSOR_BITS {
        let half = high / 2;
        for uh in (0..half).rev() {
            let src0 = pow3 * (2 * uh);
            let dst = 3 * pow3 * uh;
            for el in 0..pow3 {
                let x0 = out[src0 + el];
                let x1 = out[src0 + pow3 + el];
                out[dst + el] = x0;
                out[dst + pow3 + el] = x1;
                out[dst + 2 * pow3 + el] = x0 ^ x1;
            }
        }
        pow3 *= 3;
        high = half;
    }
}

/// Transpose a 64x64 bit matrix in place: afterwards bit `i` of row `j` is the former bit `j`
/// of row `i`.
fn rss_transpose64(rows: &mut [u64; 64]) {
    let mut j = 32usize;
    let mut mask = 0x0000_0000_ffff_ffffu64;
    while j != 0 {
        let mut k = 0usize;
        while k < 64 {
            let t = ((rows[k] >> j) ^ rows[k + j]) & mask;
            rows[k + j] ^= t;
            rows[k] ^= t << j;
            k = (k + j + 1) & !j;
        }
        j >>= 1;
        mask ^= mask << j;
    }
}

/// For the secret words `w_u` of a group and public coefficients `beta_u`, compute the 64 field elements
/// `out[i] = sum_u beta_u * bit_i(w_u)`. `pattern[bit][g]` is the public nibble of coefficient
/// bit `bit` over words `4g..4g+4`; only public values index memory.
fn rss_bind_group(
    words: &[u64],
    pattern: &[[u8; RSS_DZK_NIBBLES]; 128],
    planes: &mut [[u64; 64]; 2],
    out: &mut [u128],
) {
    let mut tables = [[0u64; 16]; RSS_DZK_NIBBLES];
    for g in 0..RSS_DZK_NIBBLES {
        for n in 1..16usize {
            tables[g][n] = tables[g][n & (n - 1)] ^ words[4 * g + n.trailing_zeros() as usize];
        }
    }
    for (bit, nibbles) in pattern.iter().enumerate() {
        let mut acc = 0u64;
        for g in 0..RSS_DZK_NIBBLES {
            acc ^= tables[g][nibbles[g] as usize];
        }
        planes[bit / 64][bit % 64] = acc;
    }
    rss_transpose64(&mut planes[0]);
    rss_transpose64(&mut planes[1]);
    for i in 0..64 {
        out[i] = u128::from(planes[0][i]) | (u128::from(planes[1][i]) << 64);
    }
    qsag_asm::volatile_fill(&mut tables, [0; 16]);
}

/// Public per-pass weights. Relation word `k = 64 * g + u` has weight
/// `nu[g] * prod_{l in bits(u)} mu[l]`, with `nu[g] = prod_{l in bits(g)} nu_bits[l]`.
struct RssDzkWeights {
    mu: [RssProofField; RSS_DZK_TENSOR_BITS],
    nu: Vec<RssProofField>,
}

struct RssDzkCtx<'a> {
    session_id: &'a [u8; 32],
    batch_ctr: u64,
    groups: usize,
    /// Latch of the accumulator under verification.
    poison: &'a RssPoisonLatch,
}

impl RssDzkCtx<'_> {
    fn coin(
        &self,
        label: &[u8],
        pass: usize,
        step: usize,
        party_rngs: &mut [PartyPrivateRng; 3],
    ) -> Result<RssProofField, KeccakMpcError> {
        let mut bind = [0u8; 32];
        bind[0] = pass as u8;
        bind[4..8].copy_from_slice(&(step as u32).to_le_bytes());
        bind[8..16].copy_from_slice(&self.batch_ctr.to_le_bytes());
        bind[16..24].copy_from_slice(&(self.groups as u64).to_le_bytes());
        match run_commit_and_open_coin(self.session_id, label, &bind, party_rngs) {
            Ok(coin) => Ok(RssProofField::from_coin(&coin)),
            Err(e) => self.poison.fail(e.into()),
        }
    }
}

/// Party `p`'s additive share of `sum x * y` over replicated sharings, as carryless
/// dot-product operands: `x_p * (y_p + y_q) + x_q * y_p` with `q = p + 1`.
/// Each tuple is `(lane 0, lane 1)`; index 0 is slot `p`, index 1 is slot `q`.
#[inline]
fn rss_cross_pairs(
    lhs: &mut [[u128; 2]],
    rhs: &mut [[u128; 2]],
    x: [(u128, u128); 2],
    y: [(u128, u128); 2],
) {
    lhs[0] = [x[0].0, x[0].1];
    rhs[0] = [y[0].0 ^ y[1].0, y[0].1 ^ y[1].1];
    lhs[1] = [x[1].0, x[1].1];
    rhs[1] = [y[0].0, y[0].1];
}

/// Proof tables of one pass: slot shares of the bound `a` (weighted by `t^lane`) and `b`
/// vectors, plus dot-product operand scratch. Wiped on `Drop`.
struct RssDzkTables {
    x: [Vec<u128>; 3],
    y: [Vec<u128>; 3],
    lhs: Vec<[u128; 2]>,
    rhs: Vec<[u128; 2]>,
}

impl Drop for RssDzkTables {
    fn drop(&mut self) {
        for s in 0..3 {
            qsag_asm::volatile_fill(&mut self.x[s], 0);
            qsag_asm::volatile_fill(&mut self.y[s], 0);
        }
        qsag_asm::volatile_fill(&mut self.lhs, [0; 2]);
        qsag_asm::volatile_fill(&mut self.rhs, [0; 2]);
    }
}

/// One halving round of the weighted inner-product argument over tables of blocks of `unit`
/// elements (`x` already carries the per-group public weights `w_g`); `hi_groups` blocks exist
/// in the upper half, which starts at block `half`. The invariant `claim = sum_g <x_g, y_g>` is
/// preserved by `x' = x_lo + gamma * x_hi`, `y' = y_lo + gamma^-1 * y_hi`,
/// `claim' = claim + gamma^-1 * L + gamma * R`, where `L = sum_g <x_lo, y_hi>` and
/// `R = sum_g <x_hi, y_lo>` are sent as masked additive shares before `gamma` is drawn.
#[expect(
    clippy::too_many_arguments,
    reason = "One protocol round: tables, dimensions, claim, randomness and challenge context"
)]
fn rss_dzk_fold_round(
    ctx: &RssDzkCtx<'_>,
    pass: usize,
    step: usize,
    tables: &mut RssDzkTables,
    unit: usize,
    hi_groups: usize,
    half: usize,
    claim: &mut [RssProofField; 3],
    streams: &mut RssProofStreams,
    party_rngs: &mut [PartyPrivateRng; 3],
) -> Result<(), KeccakMpcError> {
    let mut l_msg = SecretBuffer(streams.zero_share());
    let mut r_msg = SecretBuffer(streams.zero_share());
    let RssDzkTables { x, y, lhs, rhs } = tables;
    let need = 2 * unit * hi_groups;
    if lhs.len() < need {
        lhs.resize(need, [0; 2]);
        rhs.resize(need, [0; 2]);
    }
    for p in 0..3 {
        let q = (p + 1) % 3;
        let mut filled = 0usize;
        for g in 0..hi_groups {
            for j in 0..unit {
                let lo = g * unit + j;
                let hi = (g + half) * unit + j;
                // Lane 0 accumulates <x_lo, y_hi>, lane 1 accumulates <x_hi, y_lo>.
                rss_cross_pairs(
                    &mut lhs[filled..filled + 2],
                    &mut rhs[filled..filled + 2],
                    [(x[p][lo], x[p][hi]), (x[q][lo], x[q][hi])],
                    [(y[p][hi], y[p][lo]), (y[q][hi], y[q][lo])],
                );
                filled += 2;
            }
        }
        let out = rss_poly_dot(&lhs[..filled], &rhs[..filled]);
        l_msg[p] = l_msg[p].add(RssProofField(out[0]));
        r_msg[p] = r_msg[p].add(RssProofField(out[1]));
    }

    let gamma = ctx
        .coin(b"RSS_DZK_POLY_FOLD_COIN/v3", pass, step, party_rngs)?
        .nonzero();
    let gamma_inv = gamma.inv_public();
    let scale_x = RssFieldMultiplier::new(gamma);
    let scale_y = RssFieldMultiplier::new(gamma_inv);
    for s in 0..3 {
        claim[s] = claim[s]
            .add(gamma_inv.mul(l_msg[s]))
            .add(gamma.mul(r_msg[s]));
        for idx in 0..hi_groups * unit {
            let hi = idx + half * unit;
            x[s][idx] ^= scale_x.mul(RssProofField(x[s][hi])).0;
            y[s][idx] ^= scale_y.mul(RssProofField(y[s][hi])).0;
        }
    }
    Ok(())
}

// Keep polynomial-field operands in the batch kernel's native word layout.
// Chunking bounds scratch space and amortizes dispatch over 256 products.
fn rss_poly_dot(lhs: &[[u128; 2]], rhs: &[[u128; 2]]) -> [u128; 2] {
    assert_eq!(lhs.len(), rhs.len());
    let used = lhs.len().min(256);
    let mut a = [[0u64; 2]; 256];
    let mut b = [[0u64; 2]; 256];
    let mut out = [0u128; 2];
    for (lane, value) in out.iter_mut().enumerate() {
        let mut acc = [0u64; 2];
        for (lc, rc) in lhs.chunks(256).zip(rhs.chunks(256)) {
            for ((dst, src), (other, rsrc)) in a.iter_mut().zip(lc).zip(b.iter_mut().zip(rc)) {
                *dst = [src[lane] as u64, (src[lane] >> 64) as u64];
                *other = [rsrc[lane] as u64, (rsrc[lane] >> 64) as u64];
            }
            qsag_asm::gf2_128_mul_acc_batch(&mut acc, &a[..lc.len()], &b[..lc.len()]);
        }
        *value = u128::from(acc[0]) | (u128::from(acc[1]) << 64);
        wipe_u64s(&mut acc);
    }
    qsag_asm::volatile_fill(&mut a[..used], [0; 2]);
    qsag_asm::volatile_fill(&mut b[..used], [0; 2]);
    out
}

/// Per-party additive shares of the packed sumcheck tables for both passes.
///
/// For every group `g` and every point `e in {0, 1, slope}^6`, the 64 words of the group are
/// combined over GF(2) into one word per operand (`a_e`, `b_e`); party `p` forms its share
/// `T = a_e,p & (b_e,p ^ b_e,q) ^ a_e,q & b_e,p` of the 64 products with word operations, and
/// accumulates `sum_g nu[g] * T(t)`, where `T(t)` reads the word as a polynomial of degree
/// below 64. Lane 0 uses the pass-0 weights and lane 1 the pass-1 weights. Nothing here depends
/// on a round challenge, so all six packed rounds read these `729` sums.
fn rss_dzk_tensor_tables(
    pending: &RssPendingDzkTriples,
    groups: usize,
    nu_pairs: &[[u128; 2]],
) -> [Vec<[u128; 2]>; 3] {
    #[cfg(feature = "std")]
    if groups >= 128 {
        let workers = std::thread::available_parallelism().map_or(1, usize::from).min(16);
        let chunk = groups.div_ceil(workers);
        return std::thread::scope(|scope| {
            let handles: Vec<_> = nu_pairs.chunks(chunk).enumerate().map(|(i, weights)| {
                scope.spawn(move || rss_dzk_tensor_tables_range(pending, i * chunk, weights))
            }).collect();
            let mut total: [Vec<[u128; 2]>; 3] =
                core::array::from_fn(|_| vec![[0; 2]; RSS_DZK_TERNARY]);
            for handle in handles {
                let mut part = handle.join().expect("RSS tensor worker failed");
                for (dst, src) in total.iter_mut().zip(&mut part) {
                    for (dst, src) in dst.iter_mut().zip(src.iter()) {
                        dst[0] ^= src[0];
                        dst[1] ^= src[1];
                    }
                    qsag_asm::volatile_fill(src, [0; 2]);
                }
            }
            total
        });
    }
    debug_assert_eq!(groups, nu_pairs.len());
    rss_dzk_tensor_tables_range(pending, 0, nu_pairs)
}

fn rss_dzk_tensor_tables_range(
    pending: &RssPendingDzkTriples,
    first_group: usize,
    nu_pairs: &[[u128; 2]],
) -> [Vec<[u128; 2]>; 3] {
    let groups = nu_pairs.len();
    /// Points gathered per sweep over the group-major product table.
    const POINT_BLOCK: usize = 27;
    let mut tabs = [
        vec![[0u128; 2]; RSS_DZK_TERNARY],
        vec![[0u128; 2]; RSS_DZK_TERNARY],
        vec![[0u128; 2]; RSS_DZK_TERNARY],
    ];
    // `prod[p][g * 729 + e]`: party `p`'s product-share word for point `e` of group `g`.
    let mut prod: [Vec<u64>; 3] = core::array::from_fn(|_| vec![0u64; RSS_DZK_TERNARY * groups]);
    let mut ea = [[0u64; RSS_DZK_TERNARY]; 3];
    let mut eb = [[0u64; RSS_DZK_TERNARY]; 3];
    for g in 0..groups {
        let w0 = (first_group + g) * RSS_DZK_GROUP_WORDS;
        for s in 0..3 {
            rss_ternary_expand(&pending.a[s][w0..], &mut ea[s]);
            rss_ternary_expand(&pending.b[s][w0..], &mut eb[s]);
        }
        for p in 0..3 {
            let q = (p + 1) % 3;
            let dst = &mut prod[p][g * RSS_DZK_TERNARY..(g + 1) * RSS_DZK_TERNARY];
            for e in 0..RSS_DZK_TERNARY {
                dst[e] = (ea[p][e] & (eb[p][e] ^ eb[q][e])) ^ (ea[q][e] & eb[p][e]);
            }
        }
    }
    // One dot product per party and point: few large kernel calls. Points are gathered in
    // blocks so that both the product table and the operand rows are read sequentially.
    let mut lhs = vec![[0u128; 2]; POINT_BLOCK * groups];
    for p in 0..3 {
        for e0 in (0..RSS_DZK_TERNARY).step_by(POINT_BLOCK) {
            for g in 0..groups {
                let row = &prod[p][g * RSS_DZK_TERNARY + e0..g * RSS_DZK_TERNARY + e0 + POINT_BLOCK];
                for (j, word) in row.iter().enumerate() {
                    lhs[j * groups + g] = [u128::from(*word); 2];
                }
            }
            for j in 0..POINT_BLOCK {
                tabs[p][e0 + j] = rss_poly_dot(
                    &lhs[j * groups..(j + 1) * groups],
                    nu_pairs,
                );
            }
        }
    }
    for s in 0..3 {
        wipe_u64s(&mut prod[s]);
        wipe_u64s(&mut ea[s]);
        wipe_u64s(&mut eb[s]);
    }
    qsag_asm::volatile_fill(&mut lhs, [0; 2]);
    tabs
}

/// Slot shares of the weighted claims `sum_k weight(k) * c_k(t)` for both passes.
fn rss_dzk_initial_claims(
    pending: &RssPendingDzkTriples,
    groups: usize,
    weights: &[RssDzkWeights; 2],
    nu_pairs: &[[u128; 2]],
) -> [[RssProofField; 3]; 2] {
    let mut mu_tab = [[RssProofField::ONE; RSS_DZK_GROUP_WORDS]; 2];
    for pass in 0..2 {
        for u in 1..RSS_DZK_GROUP_WORDS {
            mu_tab[pass][u] =
                mu_tab[pass][u & (u - 1)].mul(weights[pass].mu[u.trailing_zeros() as usize]);
        }
    }
    let mut claims = [[RssProofField::ZERO; 3]; 2];
    let mut lhs = vec![[0u128; 2]; groups];
    for (s, words) in pending.c.iter().enumerate() {
        for u in 0..RSS_DZK_GROUP_WORDS {
            for (g, pair) in lhs.iter_mut().enumerate() {
                *pair = [u128::from(words[g * RSS_DZK_GROUP_WORDS + u]); 2];
            }
            let out = rss_poly_dot(&lhs, nu_pairs);
            for pass in 0..2 {
                claims[pass][s] =
                    claims[pass][s].add(mu_tab[pass][u].mul(RssProofField(out[pass])));
            }
        }
    }
    qsag_asm::volatile_fill(&mut lhs, [0; 2]);
    claims
}

/// One complete proof pass. See [`verify_rss_boolean_triples_bbcggi19`].
#[expect(
    clippy::too_many_arguments,
    reason = "One proof pass: relations, weights, claims, randomness and challenge context"
)]
fn rss_dzk_pass(
    ctx: &RssDzkCtx<'_>,
    pass: usize,
    pending: &RssPendingDzkTriples,
    weights: &RssDzkWeights,
    tabs: &[Vec<[u128; 2]>; 3],
    mut claim: [RssProofField; 3],
    streams: &mut RssProofStreams,
    party_rngs: &mut [PartyPrivateRng; 3],
) -> Result<(), KeccakMpcError> {
    let groups = ctx.groups;
    let tab: [Vec<RssProofField>; 3] =
        core::array::from_fn(|p| tabs[p].iter().map(|v| RssProofField(v[pass])).collect());
    let mut tab = SecretBuffer(tab);
    let mut gammas = [RssProofField::ZERO; RSS_DZK_TENSOR_BITS];
    let mut bound_weight = RssProofField::ONE;
    let mut scratch = SecretBuffer(vec![RssProofField::ZERO; RSS_DZK_TERNARY]);

    // Packed sumcheck over the six low word-index bits. Round `i` treats bit `i` as the
    // variable `X`; its weight is `w_i(X) = 1 + X * (1 + mu_i)` and the round polynomial is
    // `w_i(X) * s(X)` with `s(X) = (1 + X) s(0) + X s(1) + (X + X^2) s_2`.
    for (i, gamma_slot) in gammas.iter_mut().enumerate() {
        let mut s1 = SecretBuffer(streams.zero_share());
        let mut s2 = SecretBuffer(streams.zero_share());
        let len = tab[0].len();
        for p in 0..3 {
            scratch[..len].copy_from_slice(&tab[p]);
            let mut len3 = len / 3;
            for l in (i + 1..RSS_DZK_TENSOR_BITS).rev() {
                for idx in 0..len3 {
                    scratch[idx] = scratch[idx].add(weights.mu[l].mul(scratch[idx + len3]));
                }
                len3 /= 3;
            }
            s1[p] = s1[p].add(scratch[1]);
            s2[p] = s2[p].add(scratch[2]);
        }
        let gamma = ctx.coin(b"RSS_DZK_POLY_SUMCHECK_COIN/v3", pass, i, party_rngs)?;
        let mu = weights.mu[i];
        let w = RssProofField::ONE.add(gamma.mul(RssProofField::ONE.add(mu)));
        let c0 = w.mul(RssProofField::ONE.add(gamma));
        let c1 = w.mul(gamma);
        let c2 = w.mul(gamma.add(gamma.mul(gamma)));
        for p in 0..3 {
            let s0 = claim[p].add(mu.mul(s1[p]));
            claim[p] = c0.mul(s0).add(c1.mul(s1[p])).add(c2.mul(s2[p]));
            let next = len / 3;
            for idx in 0..next {
                tab[p][idx] = c0
                    .mul(tab[p][3 * idx])
                    .add(c1.mul(tab[p][3 * idx + 1]))
                    .add(c2.mul(tab[p][3 * idx + 2]));
            }
            wipe_rss_proof_field(&mut tab[p][next..]);
            tab[p].truncate(next);
        }
        *gamma_slot = gamma;
        bound_weight = bound_weight.mul(w);
    }
    wipe_rss_proof_field(&mut scratch);
    for t in tab.iter_mut() {
        wipe_rss_proof_field(t);
    }

    // Bind the six bits in the relation vectors themselves: element `(g, lane)` of the bound
    // `a` is `sum_u beta(u) * a[64 g + u][lane]` with `beta(u) = prod_i (u_i ? gamma_i : 1 + gamma_i)`.
    let mut beta = [RssProofField::ONE; RSS_DZK_GROUP_WORDS];
    for (i, gamma) in gammas.iter().copied().enumerate() {
        let bit = 1usize << i;
        let one_plus = RssProofField::ONE.add(gamma);
        for u in 0..bit {
            beta[u | bit] = beta[u].mul(gamma);
            beta[u] = beta[u].mul(one_plus);
        }
    }
    let mut pattern = [[0u8; RSS_DZK_NIBBLES]; 128];
    for (bit, nibbles) in pattern.iter_mut().enumerate() {
        for g in 0..RSS_DZK_NIBBLES {
            for d in 0..4 {
                nibbles[g] |= (((beta[4 * g + d].0 >> bit) & 1) as u8) << d;
            }
        }
    }
    let block_weights: Vec<RssProofField> =
        weights.nu.iter().map(|v| bound_weight.mul(*v)).collect();
    let total = groups * RSS_DZK_LANES;
    let mut tables = RssDzkTables {
        x: [vec![0u128; total], vec![0u128; total], vec![0u128; total]],
        y: [vec![0u128; total], vec![0u128; total], vec![0u128; total]],
        lhs: Vec::new(),
        rhs: Vec::new(),
    };
    // Groups are independent linear maps under public coefficients. Partition only
    // this arithmetic and absorb `block_weights[g]` directly into `x`; challenges,
    // proof messages and verification stay in exact sequential order.
    for s in 0..3 {
        let bind = |start: usize, x: &mut [u128], y: &mut [u128]| {
            let mut planes = [[0u64; 64]; 2];
            for (g, (x, y)) in x.chunks_mut(RSS_DZK_LANES)
                .zip(y.chunks_mut(RSS_DZK_LANES)).enumerate()
            {
                let offset = (start + g) * RSS_DZK_GROUP_WORDS;
                let w_mul = RssFieldMultiplier::new(block_weights[start + g]);
                rss_bind_group(&pending.a[s][offset..], &pattern, &mut planes, x);
                for (lane, value) in x.iter_mut().enumerate() {
                    *value = w_mul.mul(RssProofField(*value).mul_t_pow(lane as u32)).0;
                }
                rss_bind_group(&pending.b[s][offset..], &pattern, &mut planes, y);
            }
            qsag_asm::volatile_fill(&mut planes, [0; 64]);
        };
        #[cfg(feature = "std")]
        {
            let workers = std::thread::available_parallelism().map_or(1, usize::from)
                .min(16).min(groups.div_ceil(64)).max(1);
            let chunk_groups = groups.div_ceil(workers);
            std::thread::scope(|scope| {
                for (chunk, (x, y)) in tables.x[s].chunks_mut(chunk_groups * RSS_DZK_LANES)
                    .zip(tables.y[s].chunks_mut(chunk_groups * RSS_DZK_LANES)).enumerate()
                {
                    let bind = &bind;
                    scope.spawn(move || bind(chunk * chunk_groups, x, y));
                }
            });
        }
        #[cfg(not(feature = "std"))]
        bind(0, &mut tables.x[s], &mut tables.y[s]);
    }

    // Halve the group index, then halve the 64 lanes (`block_weights` already absorbed in `x`).
    let mut step = 0usize;
    let mut size = groups.next_power_of_two();
    let mut cur = groups;
    while size > 1 {
        let half = size / 2;
        let hi_groups = cur.saturating_sub(half);
        rss_dzk_fold_round(
            ctx,
            pass,
            step,
            &mut tables,
            RSS_DZK_LANES,
            hi_groups,
            half,
            &mut claim,
            streams,
            party_rngs,
        )?;
        cur = cur.min(half);
        size = half;
        step += 1;
    }
    let mut half = RSS_DZK_LANES / 2;
    while half >= 1 {
        rss_dzk_fold_round(
            ctx,
            pass,
            step,
            &mut tables,
            1,
            half,
            half,
            &mut claim,
            streams,
            party_rngs,
        )?;
        half /= 2;
        step += 1;
    }

    // Masked product check of the single remaining relation `x * y == claim`.
    let x: [RssProofField; 3] = core::array::from_fn(|s| RssProofField(tables.x[s][0]));
    let y: [RssProofField; 3] = core::array::from_fn(|s| RssProofField(tables.y[s][0]));
    let (rx_p, rx_s) = streams.draw();
    let (ry_p, ry_s) = streams.draw();
    let mut c0 = SecretBuffer(streams.zero_share());
    let mut c1 = SecretBuffer(streams.zero_share());
    for p in 0..3 {
        let q = (p + 1) % 3;
        c0[p] = c0[p]
            .add(rx_p[p].mul(ry_p[p].add(ry_s[p])))
            .add(rx_s[p].mul(ry_p[p]));
        c1[p] = c1[p]
            .add(rx_p[p].mul(y[p].add(y[q])))
            .add(rx_s[p].mul(y[p]))
            .add(ry_p[p].mul(x[p].add(x[q])))
            .add(ry_s[p].mul(x[p]));
    }
    let tau = ctx.coin(b"RSS_DZK_POLY_BASE_TAU/v3", pass, 0, party_rngs)?;
    let tau_sq = tau.mul(tau);
    let limbs = |v: RssProofField| [v.0 as u64, (v.0 >> 64) as u64];
    let mut open_prim: [Vec<u64>; 3] = [Vec::new(), Vec::new(), Vec::new()];
    let mut open_sec: [Vec<u64>; 3] = [Vec::new(), Vec::new(), Vec::new()];
    for p in 0..3 {
        let q = (p + 1) % 3;
        let pe = |s: usize| c0[s].add(tau.mul(c1[s])).add(tau_sq.mul(claim[s]));
        for v in [rx_p[p].add(tau.mul(x[p])), ry_p[p].add(tau.mul(y[p])), pe(p)] {
            open_prim[p].extend_from_slice(&limbs(v));
        }
        for v in [rx_s[p].add(tau.mul(x[q])), ry_s[p].add(tau.mul(y[q])), pe(q)] {
            open_sec[p].extend_from_slice(&limbs(v));
        }
    }
    let opened = rss_commit_and_open_u64_batch(
        ctx.session_id,
        "rss_dzk_base_eval",
        &open_prim,
        &open_sec,
        party_rngs,
        ctx.poison,
    )?;
    let elem = |i: usize| RssProofField(u128::from(opened[i]) | (u128::from(opened[i + 1]) << 64));
    if !elem(0).mul(elem(2)).ct_eq(elem(4)) {
        return ctx.poison.fail(KeccakMpcError::RssSacrificeFailed);
    }
    Ok(())
}

/// Batch verification of all recorded 2-of-3 RSS Boolean AND relations, in the style of the
/// Boneh–Boyle–Corrigan-Gibbs–Gilboa–Ishai (`CRYPTO 2019`) distributed zero-knowledge proofs:
/// a sumcheck/inner-product compression over $\mathbb{F} = \mathbb{F}_2[t]/(t^{128}+t^7+t^2+t+1)$
/// run jointly on the replicated shares, with every prover message additively masked by a
/// pairwise zero sharing and nothing opened except the final masked product check.
///
/// **Statement.** Relation word `k` carries 64 relations `a_k[i] & b_k[i] == c_k[i]`. With
/// `G` groups of 64 words, `kappa = ceil(log2 G)` and public weights
/// `weight(64 g + u) = prod_{l in bits(g)} nu_l * prod_{l in bits(u)} mu_l`, the proof shows
/// `sum_k weight(k) * sum_i t^i a_k[i] b_k[i] == sum_k weight(k) * c_k(t)`, where `c_k(t)`
/// reads the 64-bit word as a polynomial of degree below 64. The `6 + kappa` weight elements
/// are drawn by a joint commit-then-open coin after all relation shares are fixed.
///
/// **Packing.** A word is never split into 64 field elements on the weighted side: `c_k(t)`
/// and every per-group product word enter through one carryless multiplication by a 128-bit
/// weight. The six low word-index bits are bound by a sumcheck whose round messages are public
/// linear combinations of `3^6` challenge-independent sums of word ANDs
/// ([`rss_dzk_tensor_tables`]). Only then are the relation vectors bound, by GF(2) linear
/// combinations of whole words selected by public coefficient bits, leaving `64 G` field
/// elements per vector for the halving rounds ([`rss_dzk_fold_round`]). No per-relation
/// coefficient is ever stored.
///
/// **Soundness of one pass**, for an adversary controlling one party (so its deviations are
/// additive errors on the masked messages, chosen before the next challenge):
/// 1. Weights. If some relation fails, the error words `e_k(t) = a_k b_k + c_k` are not all
///    zero and `e_k(t) != 0` in the field because its degree is below 64. The weighted error is
///    a nonzero multilinear polynomial in the `6 + kappa` weight elements, so it vanishes with
///    probability at most `(6 + kappa) / 2^128` (Schwartz–Zippel).
/// 2. Packed rounds (6). A false claim stays false unless the challenge is a root of
///    `w_i(X) * D(X)` with `deg D <= 2` and `D != 0`: at most `3 / 2^128` each.
/// 3. Halving rounds (`kappa` over groups, 6 over lanes). The claim error becomes
///    `Delta + gamma^-1 e_L + gamma e_R`; times `gamma` this is a nonzero polynomial of degree
///    at most 2 over the `2^128 - 1` nonzero challenges: at most `2 / (2^128 - 1)` each.
/// 4. Final product check. `x_e * y_e - p_e` is a polynomial of degree 2 in `tau` whose leading
///    coefficient is the remaining claim error: at most `2 / 2^128`.
///
/// One pass therefore accepts a false batch with probability at most
/// `(3 kappa + 38) / (2^128 - 1)`; `kappa <= 58` for any batch that fits in memory, so this is
/// below `2^-120`. Two passes with independent weights and challenges are run and both must
/// accept: the error is below `2^-240`, and in particular below `2^-126`. A Keccak batch has
/// `G = 600`, `kappa = 10`: at most `(68 / (2^128 - 1))^2 < 2^-243`.
///
/// **Privacy.** Round messages are masked by fresh pairwise zero sharings and the only opened
/// values are `r_x + tau x`, `r_y + tau y` and the matching masked product, with `r_x`, `r_y`
/// uniform. An abort reveals nothing beyond the fact that the check failed.
fn verify_rss_boolean_triples_bbcggi19(
    session_id: &[u8; 32],
    batch_ctr: u64,
    pending: &mut RssPendingDzkTriples,
    mask: &RssMaskSession,
    party_rngs: &mut [PartyPrivateRng; 3],
) -> Result<(), KeccakMpcError> {
    verify_rss_boolean_triples_seeded(session_id, batch_ctr, pending, mask, party_rngs, None)
}

/// [`verify_rss_boolean_triples_bbcggi19`] with the relation weights of both passes expanded
/// from `weight_seed` instead of from a coin drawn here. The caller must have produced the
/// seed by a commit-then-open coin flip that was bound to every transmitted gate message and
/// opened only after all of them were fixed; the weights are then exactly as unpredictable
/// as the internally drawn ones. Every later round challenge is still a fresh joint coin.
///
/// A failure is permanent for `pending`: its latch is set where the failure is detected,
/// before the relation shares are wiped, and every later call on the same accumulator
/// returns [`KeccakMpcError::Poisoned`], including when it holds no relations. The owner of
/// the accumulator must treat that as the end of the session (see
/// [`RssPendingDzkTriples::is_poisoned`]).
pub(crate) fn verify_rss_boolean_triples_seeded(
    session_id: &[u8; 32],
    batch_ctr: u64,
    pending: &mut RssPendingDzkTriples,
    mask: &RssMaskSession,
    party_rngs: &mut [PartyPrivateRng; 3],
    weight_seed: Option<&[u8; 32]>,
) -> Result<(), KeccakMpcError> {
    if pending.poison.is_set() {
        pending.clear_and_wipe();
        return Err(KeccakMpcError::Poisoned);
    }
    if pending.len_words() == 0 {
        return Ok(());
    }
    pending.pad_to_group();
    let result =
        rss_dzk_verify_padded(session_id, batch_ctr, pending, mask, party_rngs, weight_seed);
    if result.is_err() {
        // Every failure site has already latched; this covers any error added later.
        pending.poison.set();
    }
    pending.clear_and_wipe();
    result
}

fn rss_dzk_verify_padded(
    session_id: &[u8; 32],
    batch_ctr: u64,
    pending: &RssPendingDzkTriples,
    mask: &RssMaskSession,
    party_rngs: &mut [PartyPrivateRng; 3],
    weight_seed: Option<&[u8; 32]>,
) -> Result<(), KeccakMpcError> {
    let groups = pending.len_words() / RSS_DZK_GROUP_WORDS;
    let ctx = RssDzkCtx {
        session_id,
        batch_ctr,
        groups,
        poison: &pending.poison,
    };
    let kappa = groups.next_power_of_two().trailing_zeros() as usize;

    // Joint weight coin, drawn only now that every relation share is fixed.
    let mut bind = [0u8; 32];
    bind[8..16].copy_from_slice(&batch_ctr.to_le_bytes());
    bind[16..24].copy_from_slice(&(groups as u64).to_le_bytes());
    let coin = match weight_seed {
        Some(seed) => *seed,
        None => match run_commit_and_open_coin(
            session_id,
            b"RSS_DZK_POLY_WEIGHT_COIN/v3",
            &bind,
            party_rngs,
        ) {
            Ok(coin) => coin,
            Err(e) => return pending.poison.fail(e.into()),
        },
    };
    let mut xof = Cshake256Xof::new(b"QSAG.RSS.DZK.WEIGHTS.POLY/v3");
    xof.absorb(&coin);
    xof.absorb(&bind);
    let mut next_elem = || {
        let mut bytes = [0u8; 16];
        xof.squeeze(&mut bytes);
        RssProofField(u128::from_le_bytes(bytes))
    };
    let weights: [RssDzkWeights; 2] = core::array::from_fn(|_| {
        let mu = core::array::from_fn(|_| next_elem());
        let nu_bits: Vec<RssProofField> = (0..kappa).map(|_| next_elem()).collect();
        let mut nu = vec![RssProofField::ONE; groups];
        for g in 1..groups {
            nu[g] = nu[g & (g - 1)].mul(nu_bits[g.trailing_zeros() as usize]);
        }
        RssDzkWeights { mu, nu }
    });
    let nu_pairs: Vec<[u128; 2]> = (0..groups)
        .map(|g| [weights[0].nu[g].0, weights[1].nu[g].0])
        .collect();

    let mut claims = rss_dzk_initial_claims(pending, groups, &weights, &nu_pairs);
    let mut tabs = rss_dzk_tensor_tables(pending, groups, &nu_pairs);
    let mut streams = RssProofStreams::new(mask, session_id, batch_ctr);
    let mut result = Ok(());
    for pass in 0..2 {
        result = rss_dzk_pass(
            &ctx,
            pass,
            pending,
            &weights[pass],
            &tabs,
            claims[pass],
            &mut streams,
            party_rngs,
        );
        if result.is_err() {
            break;
        }
    }
    for tab in &mut tabs {
        qsag_asm::volatile_fill(tab, [0; 2]);
    }
    for claim in &mut claims {
        wipe_rss_proof_field(claim);
    }
    result
}

#[inline]
fn init_rss_state_from_public_midstate(
    midstate: &[u64; 25],
    active_mask: u64,
    st_p: &mut [[u64; 1600]; 3],
    st_s: &mut [[u64; 1600]; 3],
) {
    for lane in 0..25 {
        let w = midstate[lane];
        for z in 0..64 {
            if ((w >> z) & 1) == 1 {
                st_p[0][64 * lane + z] = active_mask;
                st_s[2][64 * lane + z] = active_mask;
            }
        }
    }
}

/// Bitsliced theta, rho and pi on one share of 64 parallel states (`lane * 64 + bit`).
fn rss_keccak_linear_layer(st: &[u64; 1600], out: &mut [u64; 1600]) {
    let mut c = [[0u64; 64]; 5];
    for x in 0..5 {
        for z in 0..64 {
            c[x][z] = st[x * 64 + z]
                ^ st[(x + 5) * 64 + z]
                ^ st[(x + 10) * 64 + z]
                ^ st[(x + 15) * 64 + z]
                ^ st[(x + 20) * 64 + z];
        }
    }
    let mut d = [[0u64; 64]; 5];
    for x in 0..5 {
        let prev = &c[(x + 4) % 5];
        let next = &c[(x + 1) % 5];
        d[x][0] = prev[0] ^ next[63];
        for z in 1..64 {
            d[x][z] = prev[z] ^ next[z - 1];
        }
    }
    for source in 0..25 {
        let x = source % 5;
        let y = source / 5;
        let target = y + 5 * ((2 * x + 3 * y) % 5);
        let rot = KECCAK_ROTATION_OFFSETS[source] as usize;
        for z in 0..64 {
            let src_z = (z + 64 - rot) & 63;
            out[target * 64 + z] = st[source * 64 + src_z] ^ d[x][src_z];
        }
    }
    qsag_asm::volatile_fill(&mut c, [0; 64]);
    qsag_asm::volatile_fill(&mut d, [0; 64]);
}

/// Run the 24 replicated rounds on 64 bitsliced states and append every AND relation to
/// `pending_dzk` without verifying it.
fn eval_rss_keccak_f1600_batch64_record(
    session_id: &[u8; 32],
    batch_ctr: u64,
    batch_len: usize,
    states_prim: &mut [[u64; 1600]; 3],
    states_sec: &mut [[u64; 1600]; 3],
    mask: &RssMaskSession,
    pending_dzk: &mut RssPendingDzkTriples,
) -> Result<(), KeccakMpcError> {
    if pending_dzk.poison.is_set() {
        return Err(KeccakMpcError::Poisoned);
    }
    if batch_len == 0 || batch_len > 64 {
        return Err(KeccakMpcError::InvalidBatchSize(batch_len));
    }
    let active_mask = batch_active_mask(batch_len);
    pending_dzk.lane_perms += batch_len as u64;
    for (p, secondary) in states_sec.iter().enumerate() {
        let next = (p + 1) % 3;
        if secondary
            .iter()
            .zip(&states_prim[next])
            .any(|(a, b)| black_box((a ^ b) & active_mask) != 0)
        {
            return pending_dzk
                .poison
                .fail(KeccakMpcError::RssShareEqualityFailed(RssSlashingReceipt {
                    share_slot: next,
                    primary_party: next,
                    secondary_party: p,
                }));
        }
    }
    // Replica equality holds, so slot `s` is `states_prim[s]`; party `p` holds slots `p`, `p + 1`.
    let mut st = [[0u64; 1600]; 3];
    for s in 0..3 {
        for idx in 0..1600 {
            st[s][idx] = states_prim[s][idx] & active_mask;
        }
    }

    // One masked product share per AND and party. Pairwise streams provide cancelling masks;
    // the complete gate witnesses are checked before any cut.
    let (mut mask_prim, mut mask_sec) = mask.chi_streams(session_id, batch_ctr);
    let mut b = [[0u64; 1600]; 3];
    let mut mp = [[0u64; 1600]; 3];
    let mut ms = [[0u64; 1600]; 3];
    let mut prod = [[0u64; 1600]; 3];

    for &rc in &KECCAK_ROUND_CONSTANTS {
        for s in 0..3 {
            rss_keccak_linear_layer(&st[s], &mut b[s]);
            mask_prim[s].fill_words(&mut mp[s]);
        }
        match &mut mask_sec {
            Some(streams) => {
                for p in 0..3 {
                    streams[p].fill_words(&mut ms[p]);
                }
            }
            None => {
                for p in 0..3 {
                    ms[p] = mp[(p + 1) % 3];
                }
            }
        }
        // Chi: out[x] = b[x] ^ b[x+2] ^ (b[x+1] & b[x+2]); party p's product share is
        // a_p & (b_p ^ b_q) ^ a_q & b_p ^ mask, with a = b[x+1], b = b[x+2].
        for p in 0..3 {
            let q = (p + 1) % 3;
            for lane in 0..25 {
                let row = 5 * (lane / 5);
                let l1 = (row + (lane + 1) % 5) * 64;
                let l2 = (row + (lane + 2) % 5) * 64;
                let l0 = lane * 64;
                for z in 0..64 {
                    let ap = b[p][l1 + z];
                    let aq = b[q][l1 + z];
                    let bp = b[p][l2 + z];
                    let bq = b[q][l2 + z];
                    let t = ((ap & (bp ^ bq)) ^ (aq & bp) ^ mp[p][l0 + z] ^ ms[p][l0 + z])
                        & active_mask;
                    prod[p][l0 + z] = t;
                    st[p][l0 + z] = b[p][l0 + z] ^ bp ^ t;
                }
            }
        }
        for s in 0..3 {
            for lane in 0..25 {
                let row = 5 * (lane / 5);
                let l1 = (row + (lane + 1) % 5) * 64;
                let l2 = (row + (lane + 2) % 5) * 64;
                secret_vec_extend_from_slice(&mut pending_dzk.a[s], &b[s][l1..l1 + 64]);
                secret_vec_extend_from_slice(&mut pending_dzk.b[s], &b[s][l2..l2 + 64]);
            }
            secret_vec_extend_from_slice(&mut pending_dzk.c[s], &prod[s]);
        }
        // Iota: the public round constant enters slot 0.
        for (z, word) in st[0][..64].iter_mut().enumerate() {
            if ((rc >> z) & 1) == 1 {
                *word ^= active_mask;
            }
        }
    }

    for p in 0..3 {
        states_prim[p] = st[p];
        states_sec[p] = st[(p + 1) % 3];
    }
    for s in 0..3 {
        wipe_u64s(&mut st[s]);
        wipe_u64s(&mut b[s]);
        wipe_u64s(&mut mp[s]);
        wipe_u64s(&mut ms[s]);
        wipe_u64s(&mut prod[s]);
    }
    Ok(())
}

/// Evaluate 64 parallel `Keccak-f[1600]` permutations using direct replicated chi and the
/// batched AND-relation proof:
/// - `states_prim[p]` and `states_sec[p]` have length `1600` (`lane * 64 + bit_pos`), where bit `b` of each
///   `u64` belongs to sponge instance `b in 0..batch_len`.
/// - Records `24 * 1600 = 38,400` packed AND relation words (`1,600` per round), verifies
///   replicated input equality, and runs both passes of [`verify_rss_boolean_triples_bbcggi19`]
///   before returning.
/// - Mask and proof streams are hedged by a fresh joint coin from `party_rngs` on every call.
///
/// This is a one-shot evaluation: the mask session and the relation accumulator live only
/// for this call, and nothing is opened here. There is therefore no engine state in which
/// a failed proof could later be taken for a passed one. If the proof fails, both state
/// arrays are zeroed before the error is returned, so no unverified output share is left
/// for the caller to open. Argument and replica-equality errors are detected before the
/// states are touched and leave them unchanged.
pub fn eval_rss_keccak_f1600_batch64(
    session_id: &[u8; 32],
    batch_ctr: u64,
    batch_len: usize,
    states_prim: &mut [[u64; 1600]; 3],
    states_sec: &mut [[u64; 1600]; 3],
    keys: &[RssKeyShare256; 3],
    party_rngs: &mut [PartyPrivateRng; 3],
) -> Result<(), KeccakMpcError> {
    if batch_len == 0 || batch_len > 64 {
        return Err(KeccakMpcError::InvalidBatchSize(batch_len));
    }
    let mask = RssMaskSession::derive(session_id, keys, party_rngs)?;
    let mut pending = RssPendingDzkTriples::new();
    eval_rss_keccak_f1600_batch64_record(
        session_id,
        batch_ctr,
        batch_len,
        states_prim,
        states_sec,
        &mask,
        &mut pending,
    )?;
    let verified =
        verify_rss_boolean_triples_bbcggi19(session_id, batch_ctr, &mut pending, &mask, party_rngs);
    if verified.is_err() {
        wipe_rss_states(states_prim, states_sec);
    }
    verified
}

fn wipe_rss_states<const N: usize>(prim: &mut [[u64; N]; 3], sec: &mut [[u64; N]; 3]) {
    for p in 0..3 {
        wipe_u64s(&mut prim[p]);
        wipe_u64s(&mut sec[p]);
    }
}

/// Cut-boundary share words of the three parties, collected across batches until the cut
/// is verified and opened. Wiped on `Drop`, so an error return clears them as well.
struct RssCutBuffer {
    prim: [Vec<u64>; 3],
    sec: [Vec<u64>; 3],
}

impl RssCutBuffer {
    fn new() -> Self {
        Self {
            prim: [Vec::new(), Vec::new(), Vec::new()],
            sec: [Vec::new(), Vec::new(), Vec::new()],
        }
    }

    #[inline]
    fn push_party_slices(&mut self, party: usize, prim_slice: &[u64], sec_slice: &[u64]) {
        secret_vec_extend_from_slice(&mut self.prim[party], prim_slice);
        secret_vec_extend_from_slice(&mut self.sec[party], sec_slice);
    }
}

impl Drop for RssCutBuffer {
    fn drop(&mut self) {
        for p in 0..3 {
            wipe_u64s(&mut self.prim[p]);
            wipe_u64s(&mut self.sec[p]);
        }
    }
}

/// Active 2-of-3 RSS distributed `SLH-DSA` cluster implementing sealed [`SlhMpcOracles`].
pub struct RssSlhMpcCluster {
    pub session_id: [u8; 32],
    pub keys: [RssKeyShare256; 3],
    pub party_rngs: [PartyPrivateRng; 3],
    batch_ctr: u64,
    pending_dzk: RssPendingDzkTriples,
    pub(crate) mask_session: RssMaskSession,
    /// Set by the first failed verification, coin flip, opening commitment or replica check
    /// of this cluster. Nothing resets it; see [`RssSlhMpcCluster::is_poisoned`].
    poisoned: RssPoisonLatch,
}

impl fmt::Debug for RssSlhMpcCluster {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "RssSlhMpcCluster(n={}, ctr={}, [REDACTED])",
            self.keys[0].key_len, self.batch_ctr
        )
    }
}

impl RssSlhMpcCluster {
    /// Builds the cluster and derives its hedged mask session: every party contributes fresh
    /// private entropy to a joint coin, so mask and proof streams never repeat across clusters
    /// even when `session_id` and the batch counters do.
    pub fn new(
        session_id: [u8; 32],
        keys: [RssKeyShare256; 3],
        mut party_rngs: [PartyPrivateRng; 3],
    ) -> Result<Self, KeccakMpcError> {
        let n = keys[0].key_len;
        if (n != 16 && n != 24 && n != 32)
            || keys[0].party_id != 0
            || keys[1].party_id != 1
            || keys[2].party_id != 2
            || keys[1].key_len != n
            || keys[2].key_len != n
            || keys.iter().any(|k| k.pk_seed != keys[0].pk_seed
                || k.scheme_identity != keys[0].scheme_identity
                || k.tsw_binding != keys[0].tsw_binding
                || k.slh_params != keys[0].slh_params)
        {
            return Err(KeccakMpcError::InvalidParameters);
        }
        let mask_session = RssMaskSession::derive(&session_id, &keys, &mut party_rngs)?;
        Ok(Self {
            session_id,
            keys,
            party_rngs,
            batch_ctr: 0,
            pending_dzk: RssPendingDzkTriples::new(),
            mask_session,
            poisoned: RssPoisonLatch::new(),
        })
    }

    /// Bind the complete SLH profile once, and reject a different public seed or suite.
    fn bind_slh_params(&mut self, params: &Fips205Params, pk_seed: &[u8]) -> Result<(), Fips205Error> {
        if !params.is_valid() || self.keys.iter().any(|key|
            key.key_len != params.n || key.pk_seed[..key.key_len] != *pk_seed
            || key.tsw_binding.is_some() || key.scheme_identity.is_some()
            || key.slh_params.is_some_and(|bound| bound != *params)) {
            return Err(Fips205Error::InvalidParameterSet);
        }
        for key in &mut self.keys { key.slh_params = Some(*params); }
        Ok(())
    }

    /// True once any check of this cluster has failed. A poisoned cluster evaluates,
    /// verifies and opens nothing more: every such method returns
    /// [`KeccakMpcError::Poisoned`] (the sealed [`SlhMpcOracles`] methods, whose error type
    /// is fixed, return [`Fips205Error::MpcActiveTamperDetected`]). The session is over; the
    /// key shares can only be used again in a new cluster.
    pub(crate) fn is_poisoned(&self) -> bool {
        self.poisoned.is_set() || self.pending_dzk.is_poisoned()
    }

    /// Permanently poisons the cluster. For engines built on its public parts that detect
    /// a failure of their own.
    pub(crate) fn poison(&mut self) {
        self.poisoned.set();
    }

    fn ensure_live(&self) -> Result<(), KeccakMpcError> {
        if self.is_poisoned() {
            Err(KeccakMpcError::Poisoned)
        } else {
            Ok(())
        }
    }

    /// The stateless hash-signature binding shared by all three key shares, `None` when no
    /// share is bound. Shares that disagree are refused.
    fn tsw_binding(&self) -> Result<Option<TswKeyBinding>, KeccakMpcError> {
        if self.keys.iter().any(|k| k.slh_params.is_some()) { return Err(KeccakMpcError::KeyBindingMismatch); }
        let binding = self.keys[0].tsw_binding;
        if self.keys[1].tsw_binding != binding || self.keys[2].tsw_binding != binding {
            return Err(KeccakMpcError::KeyBindingMismatch);
        }
        Ok(binding)
    }

    /// One 64-way replicated permutation followed by the proof of its AND relations, under
    /// this cluster's next batch counter. Outputs remain shared. On any error the cluster
    /// is poisoned and both state arrays are zeroed.
    fn permute_batch64(
        &mut self,
        batch_len: usize,
        states_prim: &mut [[u64; 1600]; 3],
        states_sec: &mut [[u64; 1600]; 3],
    ) -> Result<(), KeccakMpcError> {
        let result = self.permute_batch64_inner(batch_len, states_prim, states_sec);
        if result.is_err() {
            self.poison();
            wipe_rss_states(states_prim, states_sec);
        }
        result
    }

    fn permute_batch64_inner(
        &mut self,
        batch_len: usize,
        states_prim: &mut [[u64; 1600]; 3],
        states_sec: &mut [[u64; 1600]; 3],
    ) -> Result<(), KeccakMpcError> {
        self.ensure_live()?;
        let ctr = self.next_ctr();
        eval_rss_keccak_f1600_batch64_record(
            &self.session_id,
            ctr,
            batch_len,
            states_prim,
            states_sec,
            &self.mask_session,
            &mut self.pending_dzk,
        )?;
        verify_rss_boolean_triples_bbcggi19(
            &self.session_id,
            ctr,
            &mut self.pending_dzk,
            &self.mask_session,
            &mut self.party_rngs,
        )
    }

    /// Record one 64-way replicated permutation into `self.pending_dzk`, flushing a batched
    /// 2-pass BBCGGI19 DZK verification barrier every `16` permutations (`614,400` relation
    /// words) and strictly before any cut opening in [`Self::flush_verify_and_open_cut`].
    fn permute_batch64_deferred(
        &mut self,
        batch_len: usize,
        states_prim: &mut [[u64; 1600]; 3],
        states_sec: &mut [[u64; 1600]; 3],
    ) -> Result<(), KeccakMpcError> {
        let result = self.permute_batch64_deferred_inner(batch_len, states_prim, states_sec);
        if result.is_err() {
            self.poison();
            wipe_rss_states(states_prim, states_sec);
        }
        result
    }

    fn permute_batch64_deferred_inner(
        &mut self,
        batch_len: usize,
        states_prim: &mut [[u64; 1600]; 3],
        states_sec: &mut [[u64; 1600]; 3],
    ) -> Result<(), KeccakMpcError> {
        const DEFERRED_DZK_FLUSH_WORDS: usize = 16 * 24 * 1600;
        self.ensure_live()?;
        let ctr = self.next_ctr();
        eval_rss_keccak_f1600_batch64_record(
            &self.session_id,
            ctr,
            batch_len,
            states_prim,
            states_sec,
            &self.mask_session,
            &mut self.pending_dzk,
        )?;
        if self.pending_dzk.len_words() >= DEFERRED_DZK_FLUSH_WORDS {
            let dzk_ctr = self.next_ctr();
            verify_rss_boolean_triples_bbcggi19(
                &self.session_id,
                dzk_ctr,
                &mut self.pending_dzk,
                &self.mask_session,
                &mut self.party_rngs,
            )?;
        }
        Ok(())
    }

    /// `Keccak-f[1600]` lane-permutations this cluster has evaluated under MPC.
    pub fn lane_permutations(&self) -> u64 {
        self.pending_dzk.lane_perms
    }

    pub(crate) fn next_ctr(&mut self) -> u64 {
        let c = self.batch_ctr;
        self.batch_ctr = self.batch_ctr.wrapping_add(1);
        c
    }

    /// Verify ALL accumulated Boolean-product relations via 2-pass BBCGGI19 DZK (`< 2^{-244}` soundness)
    /// **strictly BEFORE** committing-and-opening any cut-boundary shares, then mint
    /// [`CutBoundaryMacToken::mint_verified`].
    ///
    /// A poisoned cluster opens nothing. A failed verification or opening poisons it.
    fn flush_verify_and_open_cut(
        &mut self,
        phase: &'static str,
        cut: &RssCutBuffer,
    ) -> Result<(Vec<u64>, CutBoundaryMacToken), KeccakMpcError> {
        self.ensure_live()?;
        let dzk_ctr = self.next_ctr();
        if let Err(e) = verify_rss_boolean_triples_bbcggi19(
            &self.session_id,
            dzk_ctr,
            &mut self.pending_dzk,
            &self.mask_session,
            &mut self.party_rngs,
        ) {
            return self.poisoned.fail(e);
        }
        let opened = rss_commit_and_open_u64_batch(
            &self.session_id,
            phase,
            &cut.prim,
            &cut.sec,
            &mut self.party_rngs,
            &self.poisoned,
        )?;
        Ok((opened, CutBoundaryMacToken::mint_verified()))
    }

    /// Evaluate up to `64` single-block `PRF(PK.seed, SK.seed, adrs_batch[b])` instances in parallel!
    #[cfg(test)]
    fn eval_prf_batch64_secret(
        &mut self,
        pk_seed: &[u8],
        adrs_batch: &[Fips205Adrs],
    ) -> Result<RssCutShares, KeccakMpcError> {
        self.eval_prf_batch64_secret_impl(pk_seed, adrs_batch, false)
    }

    fn eval_prf_batch64_secret_deferred(
        &mut self,
        pk_seed: &[u8],
        adrs_batch: &[Fips205Adrs],
    ) -> Result<RssCutShares, KeccakMpcError> {
        self.eval_prf_batch64_secret_impl(pk_seed, adrs_batch, true)
    }

    fn eval_prf_batch64_secret_impl(
        &mut self,
        pk_seed: &[u8],
        adrs_batch: &[Fips205Adrs],
        defer_dzk: bool,
    ) -> Result<RssCutShares, KeccakMpcError> {
        self.ensure_live()?;
        let batch_len = adrs_batch.len();
        let n = self.keys[0].key_len;
        let active_mask = batch_active_mask(batch_len);
        let mut st_p = SecretBuffer([[0u64; 1600]; 3]);
        let mut st_s = SecretBuffer([[0u64; 1600]; 3]);

        // Frame: `PK.seed (n B) || ADRS (32 B) || SK.seed (n B) || 0x1f ... 0x80` (`2*n + 32 <= 96 < 136`!)
        let mut b = 0;
        while b < batch_len {
            let bit_b = 1u64 << b;
            let adrs_bytes = adrs_batch[b].to_bytes();
            // Public `PK.seed` at `0..n` -> slot 0 (`party 0` primary, `party 2` secondary)
            let mut byte_idx = 0;
            while byte_idx < n {
                let v = pk_seed[byte_idx];
                for bit in 0..8 {
                    if ((v >> bit) & 1) == 1 {
                        let pos = 8 * byte_idx + bit;
                        st_p[0][pos] |= bit_b;
                        st_s[2][pos] |= bit_b;
                    }
                }
                byte_idx += 1;
            }
            // Public `ADRS` at `n..n+32`
            let mut byte_idx = 0;
            while byte_idx < 32 {
                let v = adrs_bytes[byte_idx];
                for bit in 0..8 {
                    if ((v >> bit) & 1) == 1 {
                        let pos = 8 * (n + byte_idx) + bit;
                        st_p[0][pos] |= bit_b;
                        st_s[2][pos] |= bit_b;
                    }
                }
                byte_idx += 1;
            }
            // Padding `0x1f` at `2*n + 32` and `0x80` at `135`
            let pad_off = 8 * (2 * n + 32);
            for bit in 0..5 {
                st_p[0][pad_off + bit] |= bit_b;
                st_s[2][pad_off + bit] |= bit_b;
            }
            st_p[0][8 * 135 + 7] |= bit_b;
            st_s[2][8 * 135 + 7] |= bit_b;
            b += 1;
        }
        // Secret `SK.seed` at `n+32 .. 2*n+32` replicated across all active instances `active_mask`
        let sk_bit_off = 8 * (n + 32);
        for p in 0..3 {
            let (sk_p, sk_s) = self.keys[p].sk_seed_shares();
            for byte_idx in 0..n {
                for bit in 0..8 {
                    let mp = 0u64.wrapping_sub(((sk_p[byte_idx] >> bit) & 1) as u64);
                    let ms = 0u64.wrapping_sub(((sk_s[byte_idx] >> bit) & 1) as u64);
                    st_p[p][sk_bit_off + 8 * byte_idx + bit] = mp & active_mask;
                    st_s[p][sk_bit_off + 8 * byte_idx + bit] = ms & active_mask;
                }
            }
        }

        if defer_dzk {
            self.permute_batch64_deferred(batch_len, &mut st_p, &mut st_s)?;
        } else {
            self.permute_batch64(batch_len, &mut st_p, &mut st_s)?;
        }

        let n_bits = 8 * n;
        let mut out_p = [[0u64; 256]; 3];
        let mut out_s = [[0u64; 256]; 3];
        for p in 0..3 {
            out_p[p][..n_bits].copy_from_slice(&st_p[p][..n_bits]);
            out_s[p][..n_bits].copy_from_slice(&st_s[p][..n_bits]);
            wipe_u64s(&mut st_p[p]);
            wipe_u64s(&mut st_s[p]);
        }
        Ok((out_p, out_s))
    }

    /// Evaluate up to `64` single-block `F(PK.seed, adrs_batch[b], secret_in)` instances in parallel
    /// (masked by `exec_mask`, keeping lanes with bit `0` in `exec_mask` unchanged for unequal WOTS+ step depths!).
    /// On error the chain shares in `cur_p` / `cur_s` are zeroed.
    fn eval_f_step_masked_batch64(
        &mut self,
        pk_seed: &[u8],
        adrs_batch: &[Fips205Adrs],
        exec_mask: u64,
        cur_p: &mut [[u64; 256]; 3],
        cur_s: &mut [[u64; 256]; 3],
    ) -> Result<(), KeccakMpcError> {
        if let Err(e) = self.ensure_live() {
            wipe_rss_states(cur_p, cur_s);
            return Err(e);
        }
        let batch_len = adrs_batch.len();
        if exec_mask == 0 {
            return Ok(());
        }
        let n = self.keys[0].key_len;
        let n_bits = 8 * n;
        let mut st_p = SecretBuffer([[0u64; 1600]; 3]);
        let mut st_s = SecretBuffer([[0u64; 1600]; 3]);

        let mut b = 0;
        while b < batch_len {
            let bit_b = 1u64 << b;
            let adrs_bytes = adrs_batch[b].to_bytes();
            let mut byte_idx = 0;
            while byte_idx < n {
                let v = pk_seed[byte_idx];
                for bit in 0..8 {
                    if ((v >> bit) & 1) == 1 {
                        let pos = 8 * byte_idx + bit;
                        st_p[0][pos] |= bit_b;
                        st_s[2][pos] |= bit_b;
                    }
                }
                byte_idx += 1;
            }
            let mut byte_idx = 0;
            while byte_idx < 32 {
                let v = adrs_bytes[byte_idx];
                for bit in 0..8 {
                    if ((v >> bit) & 1) == 1 {
                        let pos = 8 * (n + byte_idx) + bit;
                        st_p[0][pos] |= bit_b;
                        st_s[2][pos] |= bit_b;
                    }
                }
                byte_idx += 1;
            }
            let pad_off = 8 * (2 * n + 32);
            for bit in 0..5 {
                st_p[0][pad_off + bit] |= bit_b;
                st_s[2][pad_off + bit] |= bit_b;
            }
            st_p[0][8 * 135 + 7] |= bit_b;
            st_s[2][8 * 135 + 7] |= bit_b;
            b += 1;
        }
        let m1_off = 8 * (n + 32);
        for p in 0..3 {
            for bit_idx in 0..n_bits {
                st_p[p][m1_off + bit_idx] = cur_p[p][bit_idx];
                st_s[p][m1_off + bit_idx] = cur_s[p][bit_idx];
            }
        }

        if let Err(e) = self.permute_batch64_deferred(batch_len, &mut st_p, &mut st_s) {
            wipe_rss_states(cur_p, cur_s);
            return Err(e);
        }

        let keep_mask = !exec_mask;
        for p in 0..3 {
            for bit_idx in 0..n_bits {
                cur_p[p][bit_idx] =
                    (cur_p[p][bit_idx] & keep_mask) | (st_p[p][bit_idx] & exec_mask);
                cur_s[p][bit_idx] =
                    (cur_s[p][bit_idx] & keep_mask) | (st_s[p][bit_idx] & exec_mask);
            }
            wipe_u64s(&mut st_p[p]);
            wipe_u64s(&mut st_s[p]);
        }
        Ok(())
    }

    /// Commit-before-open + replicated share-equality check strictly BEFORE declassifying `batch_len`
    /// `SlhBlock`s (`n` bytes each), minting [`CutBoundaryMacToken::mint_verified`].
    fn verify_and_open_cut_blocks(
        &mut self,
        phase: &'static str,
        batch_len: usize,
        blocks_p: &[[u64; 256]; 3],
        blocks_s: &[[u64; 256]; 3],
    ) -> Result<(Vec<SlhBlock>, CutBoundaryMacToken), KeccakMpcError> {
        self.ensure_live()?;
        let n = self.keys[0].key_len;
        let n_bits = 8 * n;
        let mut cut = RssCutBuffer::new();
        for p in 0..3 {
            cut.push_party_slices(p, &blocks_p[p][..n_bits], &blocks_s[p][..n_bits]);
        }
        let (opened_bits, tok) = self.flush_verify_and_open_cut(phase, &cut)?;
        let mut out = Vec::with_capacity(batch_len);
        for b in 0..batch_len {
            let mut blk = SlhBlock::zero(n);
            for byte_idx in 0..n {
                let mut v = 0u8;
                for bit in 0..8 {
                    let bit_val = ((opened_bits[8 * byte_idx + bit] >> b) & 1) as u8;
                    v |= bit_val << bit;
                }
                blk.bytes[byte_idx] = v;
            }
            out.push(blk);
        }
        Ok((out, tok))
    }

    /// `PRF_msg(SK.prf, opt_rand, m_prime) = SHAKE256(SK.prf || opt_rand || m_prime)[..n]`
    /// evaluated on the shared `SK.prf`, verified, then opened. The value depends only on
    /// the key and the two public inputs, never on the session or on party randomness.
    /// The caller checks `n == key_len` and `opt_rand.len() == n`.
    fn prf_msg_shared(
        &mut self,
        n: usize,
        opt_rand: &[u8],
        m_prime: &[u8],
    ) -> Result<(SlhBlock, CutBoundaryMacToken), KeccakMpcError> {
        self.ensure_live()?;
        // Stream `SHAKE256(SK.prf || opt_rand || M')` over 136-byte blocks in 2-of-3 RSS (`batch_len = 1`)
        let total_len = 2 * n + m_prime.len();
        let num_blocks = (total_len / SHAKE256_RATE_BYTES) + 1;
        let mut padded_pub = vec![0u8; num_blocks * SHAKE256_RATE_BYTES];
        padded_pub[n..2 * n].copy_from_slice(opt_rand);
        padded_pub[2 * n..2 * n + m_prime.len()].copy_from_slice(m_prime);
        padded_pub[total_len] ^= 0x1f;
        let last_idx = num_blocks * SHAKE256_RATE_BYTES - 1;
        padded_pub[last_idx] ^= 0x80;

        let mut st_p = SecretBuffer([[0u64; 1600]; 3]);
        let mut st_s = SecretBuffer([[0u64; 1600]; 3]);
        for blk_idx in 0..num_blocks {
            let blk =
                &padded_pub[blk_idx * SHAKE256_RATE_BYTES..(blk_idx + 1) * SHAKE256_RATE_BYTES];
            if blk_idx == 0 {
                for p in 0..3 {
                    let (prf_p, prf_s) = self.keys[p].sk_prf_shares();
                    for byte_idx in 0..n {
                        for bit in 0..8 {
                            st_p[p][8 * byte_idx + bit] ^= ((prf_p[byte_idx] >> bit) & 1) as u64;
                            st_s[p][8 * byte_idx + bit] ^= ((prf_s[byte_idx] >> bit) & 1) as u64;
                        }
                    }
                }
            }
            let start_b = if blk_idx == 0 { n } else { 0 };
            for byte_idx in start_b..SHAKE256_RATE_BYTES {
                let v = blk[byte_idx];
                for bit in 0..8 {
                    if ((v >> bit) & 1) == 1 {
                        st_p[0][8 * byte_idx + bit] ^= 1;
                        st_s[2][8 * byte_idx + bit] ^= 1;
                    }
                }
            }
            self.permute_batch64(1, &mut st_p, &mut st_s)?;
        }

        let mut out_p = [[0u64; 256]; 3];
        let mut out_s = [[0u64; 256]; 3];
        for p in 0..3 {
            out_p[p][..8 * n].copy_from_slice(&st_p[p][..8 * n]);
            out_s[p][..8 * n].copy_from_slice(&st_s[p][..8 * n]);
            wipe_u64s(&mut st_p[p]);
            wipe_u64s(&mut st_s[p]);
        }
        let opened = self.verify_and_open_cut_blocks("rss_cut_prf_msg", 1, &out_p, &out_s);
        wipe_rss_states(&mut out_p, &mut out_s);
        let (mut blks, tok) = opened?;
        Ok((blks.remove(0), tok))
    }
}

/// The sealed oracle interface has a fixed error type: every engine failure, including a
/// poisoned cluster, is reported as an active-tamper abort.
fn rss_oracle_abort(_: KeccakMpcError) -> Fips205Error {
    Fips205Error::MpcActiveTamperDetected
}

impl sealed_mpc_oracles::Sealed for RssSlhMpcCluster {}

impl SlhMpcOracles for RssSlhMpcCluster {
    fn bind_key_params(&mut self, params: &Fips205Params, pk_seed: &[u8]) -> Result<(), Fips205Error> {
        if self.is_poisoned() { return Err(Fips205Error::MpcActiveTamperDetected); }
        self.bind_slh_params(params, pk_seed)
    }

    fn eval_prf_msg_mpc(
        &mut self,
        n: usize,
        opt_rand: &[u8],
        m_prime: &[u8],
    ) -> Result<(SlhBlock, CutBoundaryMacToken), Fips205Error> {
        if self.is_poisoned() {
            return Err(Fips205Error::MpcActiveTamperDetected);
        }
        if n != self.keys[0].key_len || opt_rand.len() != n
            || self.keys.iter().any(|k| k.tsw_binding.is_some() || k.scheme_identity.is_some()) {
            return Err(Fips205Error::InvalidParameterSet);
        }
        self.prf_msg_shared(n, opt_rand, m_prime)
            .map_err(rss_oracle_abort)
    }

    fn eval_fors_trees_mpc(
        &mut self,
        params: &Fips205Params,
        pk_seed: &[u8],
        base_adrs: Fips205Adrs,
        fors_indices: &[u32],
    ) -> Result<(Vec<SlhBlock>, Vec<Vec<SlhBlock>>, CutBoundaryMacToken), Fips205Error> {
        if self.is_poisoned() {
            return Err(Fips205Error::MpcActiveTamperDetected);
        }
        self.bind_slh_params(params, pk_seed)?;
        let n = params.n;
        if n != self.keys[0].key_len || pk_seed.len() != n || fors_indices.len() != params.k {
            return Err(Fips205Error::InvalidParameterSet);
        }
        let t_leaves = 1usize << params.a;
        let total_leaves = params.k * t_leaves;

        // Collect all cut-boundary shares across chunks and verify/open in 1 atomic barrier!
        let mut cut = RssCutBuffer::new();
        let mut rev_chunks = Vec::new();
        let mut chunk_sizes = Vec::new();

        // Evaluate the `k` revealed FORS `sk` values in 64-wide batches (`<= 64` per batch).
        let mut rev_cursor = 0usize;
        while rev_cursor < params.k {
            let rev_len = (params.k - rev_cursor).min(64);
            let mut rev_prf_adrs = Vec::with_capacity(rev_len);
            for off in 0..rev_len {
                let i = rev_cursor + off;
                let idx_i = fors_indices[i] as usize;
                if idx_i >= t_leaves {
                    return Err(Fips205Error::MpcActiveTamperDetected);
                }
                let mut prf_adrs = base_adrs.with_type_and_clear(Fips205AdrsType::ForsPrf);
                prf_adrs.key_pair = base_adrs.key_pair;
                prf_adrs.f6 = (i * t_leaves + idx_i) as u32;
                rev_prf_adrs.push(prf_adrs);
            }
            let (mut rev_p, mut rev_s) = self
                .eval_prf_batch64_secret_deferred(pk_seed, &rev_prf_adrs)
                .map_err(rss_oracle_abort)?;
            for p in 0..3 {
                cut.push_party_slices(p, &rev_p[p][..8 * n], &rev_s[p][..8 * n]);
            }
            wipe_rss_states(&mut rev_p, &mut rev_s);
            rev_chunks.push(rev_len);
            rev_cursor += rev_len;
        }

        // Now evaluate all `total_leaves = k * 2^a` leaf hashes `F(PK.seed, leaf_adrs, PRF(PK.seed, SK.seed, prf_adrs))`
        // in 64-wide bitsliced batches (unrevealed `sk` values NEVER leave secret shares!)
        let mut leaf_cursor = 0usize;
        while leaf_cursor < total_leaves {
            let chunk_len = (total_leaves - leaf_cursor).min(64);
            let mut prf_batch = Vec::with_capacity(chunk_len);
            let mut leaf_batch = Vec::with_capacity(chunk_len);
            for c in 0..chunk_len {
                let flat = leaf_cursor + c;
                let mut prf_a = base_adrs.with_type_and_clear(Fips205AdrsType::ForsPrf);
                prf_a.key_pair = base_adrs.key_pair;
                prf_a.f6 = flat as u32;
                prf_batch.push(prf_a);

                let mut leaf_a = base_adrs;
                leaf_a.adrs_type = Fips205AdrsType::ForsTree;
                leaf_a.f5 = 0;
                leaf_a.f6 = flat as u32;
                leaf_batch.push(leaf_a);
            }
            let (cur_p, cur_s) = self
                .eval_prf_batch64_secret_deferred(pk_seed, &prf_batch)
                .map_err(rss_oracle_abort)?;
            let mut cur_p = SecretBuffer(cur_p);
            let mut cur_s = SecretBuffer(cur_s);
            let mask = batch_active_mask(chunk_len);
            self.eval_f_step_masked_batch64(pk_seed, &leaf_batch, mask, &mut cur_p, &mut cur_s)
                .map_err(rss_oracle_abort)?;
            for p in 0..3 {
                cut.push_party_slices(p, &cur_p[p][..8 * n], &cur_s[p][..8 * n]);
                wipe_u64s(&mut cur_p[p]);
                wipe_u64s(&mut cur_s[p]);
            }
            chunk_sizes.push(chunk_len);
            leaf_cursor += chunk_len;
        }

        let (opened_words, tok) = self
            .flush_verify_and_open_cut("rss_cut_fors_trees", &cut)
            .map_err(rss_oracle_abort)?;

        let n_bits = 8 * n;
        let mut revealed_sks = Vec::with_capacity(params.k);
        let mut word_off = 0usize;
        for &r_len in &rev_chunks {
            let slice = &opened_words[word_off..word_off + n_bits];
            for b in 0..r_len {
                let mut blk = SlhBlock::zero(n);
                for byte_idx in 0..n {
                    let mut v = 0u8;
                    for bit in 0..8 {
                        v |= (((slice[8 * byte_idx + bit] >> b) & 1) as u8) << bit;
                    }
                    blk.bytes[byte_idx] = v;
                }
                revealed_sks.push(blk);
            }
            word_off += n_bits;
        }

        let mut flat_leaves = Vec::with_capacity(total_leaves);
        for &c_len in &chunk_sizes {
            let slice = &opened_words[word_off..word_off + n_bits];
            for b in 0..c_len {
                let mut blk = SlhBlock::zero(n);
                for byte_idx in 0..n {
                    let mut v = 0u8;
                    for bit in 0..8 {
                        v |= (((slice[8 * byte_idx + bit] >> b) & 1) as u8) << bit;
                    }
                    blk.bytes[byte_idx] = v;
                }
                flat_leaves.push(blk);
            }
            word_off += n_bits;
        }

        let mut fors_all_leaves = Vec::with_capacity(params.k);
        for i in 0..params.k {
            fors_all_leaves.push(flat_leaves[i * t_leaves..(i + 1) * t_leaves].to_vec());
        }
        Ok((revealed_sks, fors_all_leaves, tok))
    }

    fn eval_wots_pkgen_subtree_mpc(
        &mut self,
        params: &Fips205Params,
        pk_seed: &[u8],
        layer: u32,
        tree: u128,
    ) -> Result<(Vec<SlhBlock>, CutBoundaryMacToken), Fips205Error> {
        if self.is_poisoned() {
            return Err(Fips205Error::MpcActiveTamperDetected);
        }
        self.bind_slh_params(params, pk_seed)?;
        let n = params.n;
        if n != self.keys[0].key_len || pk_seed.len() != n {
            return Err(Fips205Error::InvalidParameterSet);
        }
        let n_leaves = 1usize << params.hp;
        let ell = params.ell();
        let total_chains = n_leaves * ell;
        let n_bits = 8 * n;

        let mut cut = RssCutBuffer::new();
        let mut chunk_sizes = Vec::new();

        let mut cursor = 0usize;
        while cursor < total_chains {
            let chunk_len = (total_chains - cursor).min(64);
            let mask = batch_active_mask(chunk_len);
            let mut prf_batch = Vec::with_capacity(chunk_len);
            for c in 0..chunk_len {
                let flat = cursor + c;
                let kp = (flat / ell) as u32;
                let ch = (flat % ell) as u32;
                let mut a = Fips205Adrs::ZERO;
                a.layer = layer;
                a.set_tree_address(tree);
                a.adrs_type = Fips205AdrsType::WotsPrf;
                a.key_pair = kp;
                a.f5 = ch;
                prf_batch.push(a);
            }
            let (cur_p, cur_s) = self
                .eval_prf_batch64_secret_deferred(pk_seed, &prf_batch)
                .map_err(rss_oracle_abort)?;
            let mut cur_p = SecretBuffer(cur_p);
            let mut cur_s = SecretBuffer(cur_s);
            for step in 0..15u32 {
                let mut step_batch = Vec::with_capacity(chunk_len);
                for c in 0..chunk_len {
                    let flat = cursor + c;
                    let kp = (flat / ell) as u32;
                    let ch = (flat % ell) as u32;
                    let mut a = Fips205Adrs::ZERO;
                    a.layer = layer;
                    a.set_tree_address(tree);
                    a.adrs_type = Fips205AdrsType::WotsHash;
                    a.key_pair = kp;
                    a.f5 = ch;
                    a.f6 = step;
                    step_batch.push(a);
                }
                self.eval_f_step_masked_batch64(
                    pk_seed,
                    &step_batch,
                    mask,
                    &mut cur_p,
                    &mut cur_s,
                )
                .map_err(rss_oracle_abort)?;
            }
            for p in 0..3 {
                cut.push_party_slices(p, &cur_p[p][..n_bits], &cur_s[p][..n_bits]);
                wipe_u64s(&mut cur_p[p]);
                wipe_u64s(&mut cur_s[p]);
            }
            chunk_sizes.push(chunk_len);
            cursor += chunk_len;
        }

        let (opened_words, tok) = self
            .flush_verify_and_open_cut("rss_cut_wots_pkgen", &cut)
            .map_err(rss_oracle_abort)?;

        let mut endpoints = Vec::with_capacity(total_chains);
        let mut word_off = 0usize;
        for &c_len in &chunk_sizes {
            let slice = &opened_words[word_off..word_off + n_bits];
            for b in 0..c_len {
                let mut blk = SlhBlock::zero(n);
                for byte_idx in 0..n {
                    let mut v = 0u8;
                    for bit in 0..8 {
                        v |= (((slice[8 * byte_idx + bit] >> b) & 1) as u8) << bit;
                    }
                    blk.bytes[byte_idx] = v;
                }
                endpoints.push(blk);
            }
            word_off += n_bits;
        }
        Ok((endpoints, tok))
    }

    fn eval_wots_layer_sign_and_siblings_mpc(
        &mut self,
        _authorization: crate::fips205::OracleCallToken,
        params: &Fips205Params,
        pk_seed: &[u8],
        layer: u32,
        tree: u128,
        active_kp: u32,
        msg_to_sign: &SlhBlock,
    ) -> Result<(Vec<SlhBlock>, CutBoundaryMacToken), Fips205Error> {
        if self.is_poisoned() {
            return Err(Fips205Error::MpcActiveTamperDetected);
        }
        self.bind_slh_params(params, pk_seed)?;
        let n = params.n;
        let n_leaves = 1usize << params.hp;
        if n != self.keys[0].key_len
            || pk_seed.len() != n
            || msg_to_sign.len() != n
            || (active_kp as usize) >= n_leaves
        {
            return Err(Fips205Error::InvalidParameterSet);
        }
        let (digits, ell_check) = try_wots_base16_digits_and_csum(msg_to_sign.as_slice())?;
        let ell = params.ell();
        if ell_check != ell {
            return Err(Fips205Error::InvalidParameterSet);
        }
        let total_chains = n_leaves * ell;
        let n_bits = 8 * n;

        let mut cut = RssCutBuffer::new();
        let mut chunk_sizes = Vec::new();

        let mut cursor = 0usize;
        while cursor < total_chains {
            let chunk_len = (total_chains - cursor).min(64);
            let mut prf_batch = Vec::with_capacity(chunk_len);
            let mut target_steps = [0u32; 64];
            let mut c = 0;
            while c < chunk_len {
                let flat = cursor + c;
                let kp = (flat / ell) as u32;
                let ch = flat % ell;
                target_steps[c] = if kp == active_kp {
                    digits[ch] as u32
                } else {
                    15
                };
                let mut a = Fips205Adrs::ZERO;
                a.layer = layer;
                a.set_tree_address(tree);
                a.adrs_type = Fips205AdrsType::WotsPrf;
                a.key_pair = kp;
                a.f5 = ch as u32;
                prf_batch.push(a);
                c += 1;
            }
            let (cur_p, cur_s) = self
                .eval_prf_batch64_secret_deferred(pk_seed, &prf_batch)
                .map_err(rss_oracle_abort)?;
            let mut cur_p = SecretBuffer(cur_p);
            let mut cur_s = SecretBuffer(cur_s);

            for step in 0..15u32 {
                let mut exec_mask = 0u64;
                let mut step_batch = Vec::with_capacity(chunk_len);
                let mut c = 0;
                while c < chunk_len {
                    if step < target_steps[c] {
                        exec_mask |= 1u64 << c;
                    }
                    let flat = cursor + c;
                    let kp = (flat / ell) as u32;
                    let ch = (flat % ell) as u32;
                    let mut a = Fips205Adrs::ZERO;
                    a.layer = layer;
                    a.set_tree_address(tree);
                    a.adrs_type = Fips205AdrsType::WotsHash;
                    a.key_pair = kp;
                    a.f5 = ch;
                    a.f6 = step;
                    step_batch.push(a);
                    c += 1;
                }
                self.eval_f_step_masked_batch64(
                    pk_seed,
                    &step_batch,
                    exec_mask,
                    &mut cur_p,
                    &mut cur_s,
                )
                .map_err(rss_oracle_abort)?;
            }

            for p in 0..3 {
                cut.push_party_slices(p, &cur_p[p][..n_bits], &cur_s[p][..n_bits]);
                wipe_u64s(&mut cur_p[p]);
                wipe_u64s(&mut cur_s[p]);
            }
            chunk_sizes.push(chunk_len);
            cursor += chunk_len;
        }

        let (opened_words, tok) = self
            .flush_verify_and_open_cut("rss_cut_wots_layer", &cut)
            .map_err(rss_oracle_abort)?;

        let mut opened_nodes = Vec::with_capacity(total_chains);
        let mut word_off = 0usize;
        for &c_len in &chunk_sizes {
            let slice = &opened_words[word_off..word_off + n_bits];
            for b in 0..c_len {
                let mut blk = SlhBlock::zero(n);
                for byte_idx in 0..n {
                    let mut v = 0u8;
                    for bit in 0..8 {
                        v |= (((slice[8 * byte_idx + bit] >> b) & 1) as u8) << bit;
                    }
                    blk.bytes[byte_idx] = v;
                }
                opened_nodes.push(blk);
            }
            word_off += n_bits;
        }
        Ok((opened_nodes, tok))
    }
}

// ============================================================================
// 2. Dishonest-Majority $t$-of-$n$ SPDZ Shamir `Keccak-f[1600]` & `SlhMpcOracles`
// ============================================================================

#[inline]
fn rotate_bs_gf256_lanes_left(w: &BitslicedGf256x64, r: u32) -> BitslicedGf256x64 {
    core::array::from_fn(|pl| w[pl].rotate_left(r))
}

#[inline]
fn rotate_spdz_macs_left(m: &[[Tower128; 64]; 2], r: u32) -> [[Tower128; 64]; 2] {
    let shift = (r as usize) & 63;
    if shift == 0 {
        return *m;
    }
    let mut out = [[Tower128::ZERO; 64]; 2];
    for lane in 0..2 {
        for src in 0..64 {
            out[lane][(src + shift) & 63] = m[lane][src];
        }
    }
    out
}

#[inline]
fn xor_spdz_macs_assign(dst: &mut [[Tower128; 64]; 2], rhs: &[[Tower128; 64]; 2]) {
    for lane in 0..2 {
        for bit in 0..64 {
            dst[lane][bit].0 ^= rhs[lane][bit].0;
        }
    }
}

#[inline]
fn add_public_u64_to_spdz_word(
    pub_word: u64,
    sh: &mut BitslicedGf256x64,
    mac: &mut [[Tower128; 64]; 2],
    alpha_share: &[Tower128; 2],
) {
    // In Shamir over `TowerGf256`, constant polynomial `f(X) = c` evaluates to `c` at every point!
    sh[0] ^= pub_word;
    let mut bit = 0;
    while bit < 64 {
        let mask = 0u128.wrapping_sub(((pub_word >> bit) & 1) as u128);
        mac[0][bit].0 ^= mask & alpha_share[0].0;
        mac[1][bit].0 ^= mask & alpha_share[1].0;
        bit += 1;
    }
}

/// Commit-before-open + full `0..m` Shamir degree-`< t` opening for Beaver masked `(d, e)` words,
/// appending `(opened_word, mac_shares)` to `pending_mac_words` and `pending_mac_tags` for the
/// pre-cut 2-lane `Tower128` SPDZ `MacCheck` barrier (`[P0-08]`).
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the existing explicit protocol interface for callers"
)]
fn commit_and_open_beaver_de_batch(
    session_id: &[u8; 32],
    round_idx: usize,
    t: usize,
    quorum_pts: &[TowerGf256],
    de_shares: &[Vec<BitslicedGf256x64>],
    de_macs: &[Vec<[[Tower128; 64]; 2]>],
    pending_opened: &mut Vec<BitslicedGf256x64>,
    pending_macs: &mut [Vec<[[Tower128; 64]; 2]>],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<BitslicedGf256x64>, PreprocessError> {
    let m = quorum_pts.len();
    let batch_len = de_shares[0].len();

    let mut salts = Vec::with_capacity(m);
    let mut coms = Vec::with_capacity(m);
    for p in 0..m {
        let salt = party_rngs[p].next_bytes32();
        let mut xof = Cshake256Xof::new(b"QSAG.SPDZ.KECCAK.DE.COM/v1");
        xof.absorb(session_id);
        xof.absorb(&(round_idx as u64).to_be_bytes());
        xof.absorb(&(p as u64).to_be_bytes());
        xof.absorb(&salt);
        let mut w = 0;
        while w < batch_len {
            let mut pl = 0;
            while pl < 8 {
                xof.absorb(&de_shares[p][w][pl].to_le_bytes());
                pl += 1;
            }
            w += 1;
        }
        let mut com = [0u8; 32];
        xof.squeeze(&mut com);
        salts.push(salt);
        coms.push(com);
    }

    for p in 0..m {
        let mut xof = Cshake256Xof::new(b"QSAG.SPDZ.KECCAK.DE.COM/v1");
        xof.absorb(session_id);
        xof.absorb(&(round_idx as u64).to_be_bytes());
        xof.absorb(&(p as u64).to_be_bytes());
        xof.absorb(&salts[p]);
        let mut w = 0;
        while w < batch_len {
            let mut pl = 0;
            while pl < 8 {
                xof.absorb(&de_shares[p][w][pl].to_le_bytes());
                pl += 1;
            }
            w += 1;
        }
        wipe_bytes32(&mut salts[p]);
        let mut exp = [0u8; 32];
        xof.squeeze(&mut exp);
        if !ct_eq_bytes32(&exp, &coms[p]) {
            return Err(PreprocessError::ShareCommitMismatch {
                phase: "spdz_keccak_chi_de",
                party_id: p,
            });
        }
    }

    let mut opened = Vec::with_capacity(batch_len);
    let mut single_sh = SecretBuffer(vec![[0u64; 8]; m]);
    let opening_tables = crate::preprocessing::Gf256OpeningTables::new(t, quorum_pts)?;
    for w in 0..batch_len {
        for p in 0..m {
            single_sh[p] = de_shares[p][w];
            secret_vec_push(&mut pending_macs[p], de_macs[p][w]);
        }
        let val = opening_tables.open_bitsliced(&single_sh, "spdz_keccak_chi_de")?;
        pending_opened.push(val);
        opened.push(val);
    }
    for s in single_sh.iter_mut() {
        wipe_u64s(s);
    }
    Ok(opened)
}

/// Folded 2-lane `Tower128` SPDZ `MacCheck` (`2^{-256}` soundness) verifying all accumulated Beaver
/// openings `pending_opened` **strictly before** any party reveals its cut-boundary output share!
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the existing explicit protocol interface for callers"
)]
fn verify_pending_spdz_mac_batch(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    quorum_pts: &[TowerGf256],
    pending_opened: &[BitslicedGf256x64],
    pending_macs: &[Vec<[[Tower128; 64]; 2]>],
    alpha_shares: &[[Tower128; 2]],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(), PreprocessError> {
    if pending_opened.is_empty() {
        return Ok(());
    }
    let lambdas_0 = lagrange_weights_zero_gf256(&quorum_pts[..t])
        .ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;

    let mut dig_xof = Cshake256Xof::new(b"QSAG.SPDZ.KECCAK.PEND.DIG/v1");
    for w in pending_opened {
        let mut pl = 0;
        while pl < 8 {
            dig_xof.absorb(&w[pl].to_le_bytes());
            pl += 1;
        }
    }
    let mut open_digest = [0u8; 32];
    dig_xof.squeeze(&mut open_digest);

    let fold_coin =
        run_commit_and_open_coin(session_id, phase.as_bytes(), &open_digest, party_rngs)?;
    let mut chi_xof = Cshake256Xof::new(b"QSAG.SPDZ.KECCAK.PEND.CHIS/v1");
    chi_xof.absorb(&fold_coin);

    let total_words = pending_opened.len();
    let mut x_folded = [Tower128::ZERO; 2];
    let mut m_folded = SecretBuffer(vec![[Tower128::ZERO; 2]; t]);
    let mut chi_buf = [0u8; 64 * 32];

    for w in 0..total_words {
        chi_xof.squeeze(&mut chi_buf);
        let chis: [[u128; 2]; 64] = core::array::from_fn(|bit| {
            core::array::from_fn(|lane| {
                let off = (2 * bit + lane) * 16;
                u128::from_le_bytes(core::array::from_fn(|i| chi_buf[off + i]))
            })
        });
        for (bit, pair) in chis.iter().enumerate() {
            let value = bs_gf256_extract_lane(&pending_opened[w], bit);
            for lane in 0..2 {
                x_folded[lane] = x_folded[lane].add(Tower128(pair[lane]).mul_gf256(value));
            }
        }
        for q in 0..t {
            let mut macs: [[u128; 2]; 64] = core::array::from_fn(|bit| [pending_macs[q][w][0][bit].0, pending_macs[q][w][1][bit].0]);
            let mut folded = qsag_asm::tower128_bdoz_2lane_mac(&chis, &macs);
            for lane in 0..2 { m_folded[q][lane] = m_folded[q][lane].add(Tower128(folded[lane])); }
            crate::wipe::wipe_u128s(macs.as_flattened_mut());
            crate::wipe::wipe_u128s(&mut folded);
        }
    }
    wipe_bytes(&mut chi_buf);

    let mut z_masks = SecretBuffer(vec![[Tower128::ZERO; 2]; t]);
    if t > 1 {
        let mut r = 0;
        while r < t {
            let mut s0 = Tower128::ZERO;
            let mut s1 = Tower128::ZERO;
            let mut q = 0;
            while q < (t - 1) {
                let u0 = party_rngs[r].next_tower128();
                let u1 = party_rngs[r].next_tower128();
                z_masks[q][0] = z_masks[q][0].add(u0);
                z_masks[q][1] = z_masks[q][1].add(u1);
                s0 = s0.add(u0);
                s1 = s1.add(u1);
                q += 1;
            }
            z_masks[t - 1][0] = z_masks[t - 1][0].add(s0);
            z_masks[t - 1][1] = z_masks[t - 1][1].add(s1);
            r += 1;
        }
    }

    let mut sigmas = SecretBuffer(Vec::with_capacity(t));
    let mut sig_salts = SecretBuffer(Vec::with_capacity(t));
    let mut sig_coms = Vec::with_capacity(t);
    for q in 0..t {
        let d0 = m_folded[q][0].add(alpha_shares[q][0].mul(x_folded[0]));
        let d1 = m_folded[q][1].add(alpha_shares[q][1].mul(x_folded[1]));
        let sig_q = [
            d0.mul_gf256(lambdas_0[q]).add(z_masks[q][0]),
            d1.mul_gf256(lambdas_0[q]).add(z_masks[q][1]),
        ];
        let salt = party_rngs[q].next_bytes32();
        let q_be = (q as u64).to_be_bytes();
        let s0_b = sig_q[0].0.to_le_bytes();
        let s1_b = sig_q[1].0.to_le_bytes();
        let com = cshake256_32_multi_frame(
            b"QSAG.SPDZ.KECCAK.PEND.MAC.COM/v1",
            &[session_id, phase.as_bytes(), &q_be, &s0_b, &s1_b, &salt],
        );
        sigmas.push(sig_q);
        sig_salts.push(salt);
        sig_coms.push(com);
    }
    for z in z_masks.iter_mut() {
        wipe_tower128(z);
    }
    for m in m_folded.iter_mut() {
        wipe_tower128(m);
    }

    let mut sum0 = Tower128::ZERO;
    let mut sum1 = Tower128::ZERO;
    for q in 0..t {
        let q_be = (q as u64).to_be_bytes();
        let s0_b = sigmas[q][0].0.to_le_bytes();
        let s1_b = sigmas[q][1].0.to_le_bytes();
        let exp = cshake256_32_multi_frame(
            b"QSAG.SPDZ.KECCAK.PEND.MAC.COM/v1",
            &[
                session_id,
                phase.as_bytes(),
                &q_be,
                &s0_b,
                &s1_b,
                &sig_salts[q],
            ],
        );
        wipe_bytes32(&mut sig_salts[q]);
        if !ct_eq_bytes32(&exp, &sig_coms[q]) {
            return Err(PreprocessError::ShareCommitMismatch { phase, party_id: q });
        }
        sum0 = sum0.add(sigmas[q][0]);
        sum1 = sum1.add(sigmas[q][1]);
        wipe_tower128(&mut sigmas[q]);
    }
    if !(sum0.ct_eq(Tower128::ZERO) && sum1.ct_eq(Tower128::ZERO)) {
        return Err(PreprocessError::MacCheckFailed {
            phase,
            accused_party: None,
        });
    }
    Ok(())
}

/// A vault poisoned by an earlier abort has a zeroed MAC key share, so no MAC relation
/// checked against it means anything. If any vault of the quorum is poisoned, the rest are
/// poisoned too and the call is refused before anything is evaluated or opened.
fn spdz_refuse_poisoned_vaults(
    vaults: &mut [PreprocessedKeccakPartyVault],
) -> Result<(), KeccakMpcError> {
    if vaults.iter().any(|v| v.poisoned) {
        for v in vaults.iter_mut() {
            v.poison_and_wipe();
        }
        return Err(KeccakMpcError::Poisoned);
    }
    Ok(())
}

/// Evaluate one 24-round `Keccak-f[1600]` permutation in dishonest-majority $t$-of-$n$ SPDZ Shamir
/// over `25` intra-sponge 64-bit `BitslicedGf256x64` lanes (`600` `KeccakBitTripleShare64` words!),
/// propagating exact 2-lane `Tower128` SPDZ MAC shares across $\theta, \rho, \pi, \chi, \iota$.
///
/// On ANY commitment/degree failure, poisons and wipes ALL vaults immediately (`[P0-07]`).
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the existing explicit protocol interface for callers"
)]
pub fn eval_spdz_keccak_f1600_single(
    session_id: &[u8; 32],
    perm_ctr: usize,
    t: usize,
    quorum_pts: &[TowerGf256],
    states_sh: &mut [[BitslicedGf256x64; 25]],
    states_mac: &mut [[[[Tower128; 64]; 2]; 25]],
    vaults: &mut [PreprocessedKeccakPartyVault],
    pending_opened: &mut Vec<BitslicedGf256x64>,
    pending_macs: &mut [Vec<[[Tower128; 64]; 2]>],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(), KeccakMpcError> {
    let m = quorum_pts.len();
    if t == 0
        || m < t
        || states_sh.len() != m
        || states_mac.len() != m
        || vaults.len() != m
        || pending_macs.len() != m
        || party_rngs.len() != m
    {
        return Err(KeccakMpcError::InvalidParameters);
    }
    validate_all_eval_points_gf256(quorum_pts)?;
    spdz_refuse_poisoned_vaults(vaults)?;

    for (rnd, &rc) in KECCAK_ROUND_CONSTANTS.iter().enumerate() {
        // 1. Theta + Rho + Pi on shares AND 2-lane `Tower128` SPDZ MACs
        let mut b_sh = SecretBuffer(vec![[[0u64; 8]; 25]; m]);
        let mut b_mac = SecretBuffer(vec![[[[Tower128::ZERO; 64]; 2]; 25]; m]);

        for p in 0..m {
            let mut c_sh = [[0u64; 8]; 5];
            let mut c_mac = [[[Tower128::ZERO; 64]; 2]; 5];
            for x in 0..5 {
                for y in 0..5 {
                    bs_gf256_xor_assign(&mut c_sh[x], &states_sh[p][x + 5 * y]);
                    xor_spdz_macs_assign(&mut c_mac[x], &states_mac[p][x + 5 * y]);
                }
            }
            for x in 0..5 {
                let d_sh = bs_gf256_xor(
                    &c_sh[(x + 4) % 5],
                    &rotate_bs_gf256_lanes_left(&c_sh[(x + 1) % 5], 1),
                );
                let mut d_mac = c_mac[(x + 4) % 5];
                let rot_m = rotate_spdz_macs_left(&c_mac[(x + 1) % 5], 1);
                xor_spdz_macs_assign(&mut d_mac, &rot_m);

                for y in 0..5 {
                    bs_gf256_xor_assign(&mut states_sh[p][x + 5 * y], &d_sh);
                    xor_spdz_macs_assign(&mut states_mac[p][x + 5 * y], &d_mac);
                }
            }
            for source in 0..25 {
                let x = source % 5;
                let y = source / 5;
                let target = y + 5 * ((2 * x + 3 * y) % 5);
                let rot = KECCAK_ROTATION_OFFSETS[source];
                b_sh[p][target] = rotate_bs_gf256_lanes_left(&states_sh[p][source], rot);
                b_mac[p][target] = rotate_spdz_macs_left(&states_mac[p][source], rot);
            }
        }

        // 2. Chi: 25 parallel Beaver AND words (`50` masked words opened in 1 round!)
        let mut de_sh = SecretBuffer(vec![Vec::with_capacity(50); m]);
        let mut de_mac = SecretBuffer(vec![Vec::with_capacity(50); m]);
        let mut round_triples_a = SecretBuffer(vec![[[0u64; 8]; 25]; m]);
        let mut round_triples_b = SecretBuffer(vec![[[0u64; 8]; 25]; m]);
        let mut round_triples_c = SecretBuffer(vec![[[0u64; 8]; 25]; m]);
        let mut round_mac_a = SecretBuffer(vec![[[[Tower128::ZERO; 64]; 2]; 25]; m]);
        let mut round_mac_b = SecretBuffer(vec![[[[Tower128::ZERO; 64]; 2]; 25]; m]);
        let mut round_mac_c = SecretBuffer(vec![[[[Tower128::ZERO; 64]; 2]; 25]; m]);

        for lane in 0..25 {
            let x = lane % 5;
            let y = lane / 5;
            let u_lane = 5 * y + ((x + 1) % 5);
            let v_lane = 5 * y + ((x + 2) % 5);

            for p in 0..m {
                let alpha_p = vaults[p].mac_alpha_lanes;
                let tr = match vaults[p].pop_triple() {
                    Ok(t_ref) => t_ref,
                    Err(e) => {
                        for v in vaults.iter_mut() {
                            v.poison_and_wipe();
                        }
                        return Err(KeccakMpcError::Preprocess(e));
                    }
                };
                round_triples_a[p][lane] = tr.a;
                round_triples_b[p][lane] = tr.b;
                round_triples_c[p][lane] = tr.c;
                round_mac_a[p][lane] = tr.a_mac;
                round_mac_b[p][lane] = tr.b_mac;
                round_mac_c[p][lane] = tr.c_mac;

                let mut not_u_sh = b_sh[p][u_lane];
                let mut not_u_mac = b_mac[p][u_lane];
                add_public_u64_to_spdz_word(u64::MAX, &mut not_u_sh, &mut not_u_mac, &alpha_p);

                let d_w = bs_gf256_xor(&not_u_sh, &round_triples_a[p][lane]);
                let mut d_m = not_u_mac;
                xor_spdz_macs_assign(&mut d_m, &round_mac_a[p][lane]);

                let e_w = bs_gf256_xor(&b_sh[p][v_lane], &round_triples_b[p][lane]);
                let mut e_m = b_mac[p][v_lane];
                xor_spdz_macs_assign(&mut e_m, &round_mac_b[p][lane]);

                de_sh[p].push(d_w);
                de_sh[p].push(e_w);
                de_mac[p].push(d_m);
                de_mac[p].push(e_m);
            }
        }

        let de_opened = match commit_and_open_beaver_de_batch(
            session_id,
            perm_ctr * 24 + rnd,
            t,
            quorum_pts,
            &de_sh,
            &de_mac,
            pending_opened,
            pending_macs,
            party_rngs,
        ) {
            Ok(v) => v,
            Err(e) => {
                for v in vaults.iter_mut() {
                    v.poison_and_wipe();
                }
                return Err(KeccakMpcError::Preprocess(e));
            }
        };

        for lane in 0..25 {
            let d_pub = &de_opened[2 * lane];
            let e_pub = &de_opened[2 * lane + 1];
            let de_pub = bs_gf256_mul_planes_ct(d_pub, e_pub);

            for p in 0..m {
                let db = bs_gf256_mul_planes_ct(d_pub, &round_triples_b[p][lane]);
                let ea = bs_gf256_mul_planes_ct(e_pub, &round_triples_a[p][lane]);
                // Note: `de_pub` is a public `BitslicedGf256x64` constant (plane 0..7), added identically
                // to every party's Shamir share (`f(X) = de_pub` has degree 0)!
                let mut prod_sh = bs_gf256_xor(&round_triples_c[p][lane], &db);
                bs_gf256_xor_assign(&mut prod_sh, &ea);
                bs_gf256_xor_assign(&mut prod_sh, &de_pub);

                let alpha_p = vaults[p].mac_alpha_lanes;
                let mut prod_mac = round_mac_c[p][lane];
                for ml in 0..2 {
                    for bit in 0..64 {
                        let term = round_mac_b[p][lane][ml][bit]
                            .mul_gf256(bs_gf256_extract_lane(d_pub, bit))
                            .add(
                                round_mac_a[p][lane][ml][bit]
                                    .mul_gf256(bs_gf256_extract_lane(e_pub, bit)),
                            )
                            .add(alpha_p[ml].mul_gf256(bs_gf256_extract_lane(&de_pub, bit)));
                        prod_mac[ml][bit] = prod_mac[ml][bit].add(term);
                    }
                }

                states_sh[p][lane] = bs_gf256_xor(&b_sh[p][lane], &prod_sh);
                states_mac[p][lane] = b_mac[p][lane];
                xor_spdz_macs_assign(&mut states_mac[p][lane], &prod_mac);

                wipe_u64s(&mut round_triples_a[p][lane]);
                wipe_u64s(&mut round_triples_b[p][lane]);
                wipe_u64s(&mut round_triples_c[p][lane]);
            }
        }

        // 3. Iota: XOR public round constant `rc` into lane `0`
        for p in 0..m {
            let alpha_p = vaults[p].mac_alpha_lanes;
            add_public_u64_to_spdz_word(rc, &mut states_sh[p][0], &mut states_mac[p][0], &alpha_p);
        }
    }
    Ok(())
}

/// Bit positions of one `Keccak-f[1600]` state in the instance-bitsliced layout.
const SPDZ_BATCH_POSITIONS: usize = 1600;

/// Evaluate 64 independent 24-round `Keccak-f[1600]` permutations in dishonest-majority
/// $t$-of-$n$ SPDZ Shamir, bitsliced across sponge instances.
///
/// `states_sh[p][lane * 64 + z]` holds party `p`'s `TowerGf256` Shamir shares of state bit
/// `(lane, z)` for all 64 instances (bit `i` of plane `k` is bit `k` of instance `i`'s share), and
/// `states_mac[p][lane * 64 + z][l][i]` the matching lane-`l` MAC share of instance `i`.
/// - Theta, rho and pi are word XORs and index moves on shares and MAC shares alike.
/// - Chi consumes `1600` 64-way Beaver triple words per round, so one bit of every triple word
///   serves one instance, and opens all `3200` masked words of the round in one
///   commit-then-open step shared by the 64 instances.
/// - Every opened word and its MAC shares are appended to `pending_opened` / `pending_macs`;
///   the caller must pass the batched `MacCheck` before any output share is revealed.
///
/// On ANY commitment/degree failure, poisons and wipes ALL vaults immediately (`[P0-07]`).
#[expect(
    clippy::too_many_arguments,
    reason = "Same explicit protocol interface as the single-instance evaluator"
)]
pub fn eval_spdz_keccak_f1600_batch64(
    session_id: &[u8; 32],
    perm_ctr: usize,
    t: usize,
    quorum_pts: &[TowerGf256],
    states_sh: &mut [Vec<BitslicedGf256x64>],
    states_mac: &mut [Vec<SpdzMacWord>],
    vaults: &mut [PreprocessedKeccakPartyVault],
    pending_opened: &mut Vec<BitslicedGf256x64>,
    pending_macs: &mut [Vec<SpdzMacWord>],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(), KeccakMpcError> {
    const N: usize = SPDZ_BATCH_POSITIONS;
    const ZERO_MAC: SpdzMacWord = [[Tower128::ZERO; 64]; 2];
    let m = quorum_pts.len();
    if t == 0
        || m < t
        || states_sh.len() != m
        || states_mac.len() != m
        || vaults.len() != m
        || pending_macs.len() != m
        || party_rngs.len() != m
        || states_sh.iter().any(|s| s.len() != N)
        || states_mac.iter().any(|s| s.len() != N)
    {
        return Err(KeccakMpcError::InvalidParameters);
    }
    validate_all_eval_points_gf256(quorum_pts)?;
    spdz_refuse_poisoned_vaults(vaults)?;

    let mut b_sh = SecretBuffer(vec![vec![[0u64; 8]; N]; m]);
    let mut b_mac = SecretBuffer(vec![vec![ZERO_MAC; N]; m]);
    let mut col_sh = SecretBuffer(vec![[0u64; 8]; 320]);
    let mut col_mac = SecretBuffer(vec![ZERO_MAC; 320]);
    let mut d_sh = SecretBuffer(vec![[0u64; 8]; 320]);
    let mut d_mac = SecretBuffer(vec![ZERO_MAC; 320]);
    let mut tr_a = SecretBuffer(vec![vec![[0u64; 8]; N]; m]);
    let mut tr_b = SecretBuffer(vec![vec![[0u64; 8]; N]; m]);
    let mut tr_c = SecretBuffer(vec![vec![[0u64; 8]; N]; m]);
    let mut mac_a = SecretBuffer(vec![vec![ZERO_MAC; N]; m]);
    let mut mac_b = SecretBuffer(vec![vec![ZERO_MAC; N]; m]);
    let mut mac_c = SecretBuffer(vec![vec![ZERO_MAC; N]; m]);
    let mut de_sh = SecretBuffer(vec![Vec::with_capacity(2 * N); m]);
    let mut de_mac = SecretBuffer(vec![Vec::with_capacity(2 * N); m]);

    for (rnd, &rc) in KECCAK_ROUND_CONSTANTS.iter().enumerate() {
        // 1. Theta + Rho + Pi on shares and MAC shares: no rotation inside a word, only moves.
        for p in 0..m {
            for x in 0..5 {
                for z in 0..64 {
                    let mut cs = [0u64; 8];
                    let mut cm = ZERO_MAC;
                    for y in 0..5 {
                        let idx = (x + 5 * y) * 64 + z;
                        bs_gf256_xor_assign(&mut cs, &states_sh[p][idx]);
                        xor_spdz_macs_assign(&mut cm, &states_mac[p][idx]);
                    }
                    col_sh[x * 64 + z] = cs;
                    col_mac[x * 64 + z] = cm;
                }
            }
            for x in 0..5 {
                for z in 0..64 {
                    let prev = ((x + 4) % 5) * 64 + z;
                    let next = ((x + 1) % 5) * 64 + ((z + 63) & 63);
                    d_sh[x * 64 + z] = bs_gf256_xor(&col_sh[prev], &col_sh[next]);
                    d_mac[x * 64 + z] = col_mac[prev];
                    xor_spdz_macs_assign(&mut d_mac[x * 64 + z], &col_mac[next]);
                }
            }
            for (source, rot) in KECCAK_ROTATION_OFFSETS.iter().enumerate() {
                let x = source % 5;
                let y = source / 5;
                let target = y + 5 * ((2 * x + 3 * y) % 5);
                let rot = *rot as usize;
                for z in 0..64 {
                    let src_z = (z + 64 - rot) & 63;
                    let src = source * 64 + src_z;
                    let dst = target * 64 + z;
                    b_sh[p][dst] = bs_gf256_xor(&states_sh[p][src], &d_sh[x * 64 + src_z]);
                    b_mac[p][dst] = states_mac[p][src];
                    xor_spdz_macs_assign(&mut b_mac[p][dst], &d_mac[x * 64 + src_z]);
                }
            }
        }

        // 2. Chi: one Beaver triple word per state bit; all masked words open together.
        for p in 0..m {
            de_sh[p].clear();
            de_mac[p].clear();
        }
        for idx in 0..N {
            let lane = idx / 64;
            let z = idx % 64;
            let row = 5 * (lane / 5);
            let u = (row + (lane + 1) % 5) * 64 + z;
            let v = (row + (lane + 2) % 5) * 64 + z;
            for p in 0..m {
                let alpha_p = vaults[p].mac_alpha_lanes;
                let tr = match vaults[p].pop_triple() {
                    Ok(t_ref) => t_ref,
                    Err(e) => {
                        for vault in vaults.iter_mut() {
                            vault.poison_and_wipe();
                        }
                        return Err(KeccakMpcError::Preprocess(e));
                    }
                };
                tr_a[p][idx] = tr.a;
                tr_b[p][idx] = tr.b;
                tr_c[p][idx] = tr.c;
                mac_a[p][idx] = tr.a_mac;
                mac_b[p][idx] = tr.b_mac;
                mac_c[p][idx] = tr.c_mac;

                let mut not_u_sh = b_sh[p][u];
                let mut not_u_mac = b_mac[p][u];
                add_public_u64_to_spdz_word(u64::MAX, &mut not_u_sh, &mut not_u_mac, &alpha_p);

                let mut d_m = not_u_mac;
                xor_spdz_macs_assign(&mut d_m, &mac_a[p][idx]);
                let mut e_m = b_mac[p][v];
                xor_spdz_macs_assign(&mut e_m, &mac_b[p][idx]);
                de_sh[p].push(bs_gf256_xor(&not_u_sh, &tr_a[p][idx]));
                de_sh[p].push(bs_gf256_xor(&b_sh[p][v], &tr_b[p][idx]));
                de_mac[p].push(d_m);
                de_mac[p].push(e_m);
            }
        }

        let de_opened = match commit_and_open_beaver_de_batch(
            session_id,
            perm_ctr * 24 + rnd,
            t,
            quorum_pts,
            &de_sh,
            &de_mac,
            pending_opened,
            pending_macs,
            party_rngs,
        ) {
            Ok(opened) => opened,
            Err(e) => {
                for vault in vaults.iter_mut() {
                    vault.poison_and_wipe();
                }
                return Err(KeccakMpcError::Preprocess(e));
            }
        };

        for idx in 0..N {
            let d_pub = &de_opened[2 * idx];
            let e_pub = &de_opened[2 * idx + 1];
            let de_pub = bs_gf256_mul_planes_ct(d_pub, e_pub);
            let d_lanes: [TowerGf256; 64] = core::array::from_fn(|i| bs_gf256_extract_lane(d_pub, i));
            let e_lanes: [TowerGf256; 64] = core::array::from_fn(|i| bs_gf256_extract_lane(e_pub, i));
            let de_lanes: [TowerGf256; 64] =
                core::array::from_fn(|i| bs_gf256_extract_lane(&de_pub, i));
            for p in 0..m {
                let db = bs_gf256_mul_planes_ct(d_pub, &tr_b[p][idx]);
                let ea = bs_gf256_mul_planes_ct(e_pub, &tr_a[p][idx]);
                // `de_pub` is public, so it enters every party's share (constant polynomial).
                let mut prod_sh = bs_gf256_xor(&tr_c[p][idx], &db);
                bs_gf256_xor_assign(&mut prod_sh, &ea);
                bs_gf256_xor_assign(&mut prod_sh, &de_pub);

                let alpha_p = vaults[p].mac_alpha_lanes;
                let mut out_mac = b_mac[p][idx];
                for ml in 0..2 {
                    for i in 0..64 {
                        let term = mac_c[p][idx][ml][i]
                            .add(mac_b[p][idx][ml][i].mul_gf256(d_lanes[i]))
                            .add(mac_a[p][idx][ml][i].mul_gf256(e_lanes[i]))
                            .add(alpha_p[ml].mul_gf256(de_lanes[i]));
                        out_mac[ml][i] = out_mac[ml][i].add(term);
                    }
                }
                states_sh[p][idx] = bs_gf256_xor(&b_sh[p][idx], &prod_sh);
                states_mac[p][idx] = out_mac;
            }
        }

        // 3. Iota: the public round constant enters lane 0 of every instance.
        for p in 0..m {
            let alpha_p = vaults[p].mac_alpha_lanes;
            for z in 0..64 {
                if ((rc >> z) & 1) == 1 {
                    add_public_u64_to_spdz_word(
                        u64::MAX,
                        &mut states_sh[p][z],
                        &mut states_mac[p][z],
                        &alpha_p,
                    );
                }
            }
        }
    }
    for p in 0..m {
        for words in [&mut b_sh[p], &mut tr_a[p], &mut tr_b[p], &mut tr_c[p]] {
            for word in words.iter_mut() {
                wipe_u64s(word);
            }
        }
    }
    Ok(())
}

fn slh_profile_digest_u64x4(params: &Fips205Params) -> [u64; 4] {
    let n_b = (params.n as u64).to_le_bytes();
    let h_b = (params.h as u64).to_le_bytes();
    let d_b = (params.d as u64).to_le_bytes();
    let hp_b = (params.hp as u64).to_le_bytes();
    let a_b = (params.a as u64).to_le_bytes();
    let k_b = (params.k as u64).to_le_bytes();
    let lg_w_b = (params.lg_w as u64).to_le_bytes();
    let m_b = (params.m as u64).to_le_bytes();
    let digest = cshake256_32_multi_frame(
        b"QSAG.FIPS205.PROFILE.V1",
        &[
            params.name.as_bytes(),
            &n_b,
            &h_b,
            &d_b,
            &hp_b,
            &a_b,
            &k_b,
            &lg_w_b,
            &m_b,
        ],
    );
    core::array::from_fn(|i| {
        u64::from_le_bytes(core::array::from_fn(|b| digest[8 * i + b]))
    })
}

#[inline]
fn ct_eq_u64_x4(a: &[u64; 4], b: &[u64; 4]) -> bool {
    let mut ok = 1u8;
    for i in 0..4 {
        ok &= ct_eq_u64(a[i], b[i]) as u8;
    }
    ok == 1
}

/// Lock-free write-once commitment to an enrolled [`Fips205Params`] profile on a share.
struct SlhProfileLatch {
    state: AtomicU8,
    digest: [AtomicU64; 4],
}

impl SlhProfileLatch {
    const UNBOUND: u8 = 0;
    const BINDING: u8 = 1;
    const BOUND: u8 = 2;

    const fn new() -> Self {
        Self {
            state: AtomicU8::new(Self::UNBOUND),
            digest: [
                AtomicU64::new(0),
                AtomicU64::new(0),
                AtomicU64::new(0),
                AtomicU64::new(0),
            ],
        }
    }

    fn enrolled(&self) -> Result<Option<[u64; 4]>, ()> {
        match self.state.load(Ordering::Acquire) {
            Self::UNBOUND => Ok(None),
            Self::BOUND => Ok(Some([
                self.digest[0].load(Ordering::Acquire),
                self.digest[1].load(Ordering::Acquire),
                self.digest[2].load(Ordering::Acquire),
                self.digest[3].load(Ordering::Acquire),
            ])),
            _ => Err(()),
        }
    }

    fn bind(&self, want: [u64; 4]) -> Result<(), ()> {
        if self
            .state
            .compare_exchange(Self::UNBOUND, Self::BINDING, Ordering::AcqRel, Ordering::Acquire)
            .is_ok()
        {
            for (slot, &val) in self.digest.iter().zip(&want) {
                slot.store(val, Ordering::Release);
            }
            self.state.store(Self::BOUND, Ordering::Release);
            return Ok(());
        }
        if let Ok(Some(cur)) = self.enrolled()
            && ct_eq_u64_x4(&cur, &want)
        {
            return Ok(());
        }
        Err(())
    }
}

/// Authenticated SPDZ Shamir representation of `(SK.seed, SK.prf)` packed into four 64-bit words
/// (`[BitslicedGf256x64; 4]` = 32 bytes each) paired with 2-lane `Tower128` SPDZ MAC shares!
pub struct SpdzAuthenticatedKeyShare {
    pub party_id: usize,
    pub eval_point: TowerGf256,
    pub key_len: usize,
    pub pk_seed: [u8; 32],
    pub sk_seed_words: [BitslicedGf256x64; 4],
    pub sk_seed_macs: [[[Tower128; 64]; 2]; 4],
    pub sk_prf_words: [BitslicedGf256x64; 4],
    pub sk_prf_macs: [[[Tower128; 64]; 2]; 4],
    slh_profile: SlhProfileLatch,
}

impl fmt::Debug for SpdzAuthenticatedKeyShare {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "SpdzAuthenticatedKeyShare(party={}, n={}, [REDACTED])",
            self.party_id, self.key_len
        )
    }
}

impl Drop for SpdzAuthenticatedKeyShare {
    fn drop(&mut self) {
        for w in 0..4 {
            wipe_u64s(&mut self.sk_seed_words[w]);
            wipe_u64s(&mut self.sk_prf_words[w]);
            for l in 0..2 {
                wipe_tower128(&mut self.sk_seed_macs[w][l]);
                wipe_tower128(&mut self.sk_prf_macs[w][l]);
            }
        }
    }
}

/// Authenticate DKG/reshared `ShamirSeedShare256` `(sk_seed, sk_prf)` shares under the SPDZ global
/// 2-lane `Tower128` MAC key of `vaults` (`alpha_contribs` from `spdz_setup_alpha_gf256`), with zero
/// secret reconstruction!
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the existing explicit protocol interface for callers"
)]
pub fn authenticate_dkg_seed_shares_for_spdz(
    session_id: &[u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    key_len: usize,
    pk_seed: [u8; 32],
    sk_seed_dkg: &[ShamirSeedShare256],
    sk_prf_dkg: &[ShamirSeedShare256],
    alpha_contribs: &[[Tower128; 2]],
    alpha_shamir: &[[Tower128; 2]],
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<SpdzAuthenticatedKeyShare>, KeccakMpcError> {
    let n = eval_points.len();
    if (key_len != 16 && key_len != 24 && key_len != 32)
        || sk_seed_dkg.len() != n
        || sk_prf_dkg.len() != n
        || alpha_contribs.len() != n
        || alpha_shamir.len() != n
        || party_rngs.len() != n
    {
        return Err(KeccakMpcError::InvalidParameters);
    }
    validate_all_eval_points_gf256(eval_points)?;

    let mut packed_words = SecretBuffer(vec![vec![[0u64; 8]; 8]; n]);
    for p in 0..n {
        if !sk_seed_dkg[p].is_valid()
            || !sk_prf_dkg[p].is_valid()
            || sk_seed_dkg[p].eval_point != eval_points[p]
            || sk_prf_dkg[p].eval_point != eval_points[p]
        {
            return Err(KeccakMpcError::InvalidParameters);
        }
        for w in 0..4 {
            for bit in 0..64 {
                let idx = 64 * w + bit;
                if idx < 8 * key_len {
                    bs_gf256_insert_lane(
                        &mut packed_words[p][w],
                        bit,
                        sk_seed_dkg[p].bit_shares[idx],
                    );
                    bs_gf256_insert_lane(
                        &mut packed_words[p][4 + w],
                        bit,
                        sk_prf_dkg[p].bit_shares[idx],
                    );
                }
            }
        }
    }

    let all_macs = SecretBuffer(spdz_authenticate_bs_gf256_words(
        session_id,
        t,
        eval_points,
        ot_mesh,
        alpha_contribs,
        alpha_shamir,
        &packed_words,
        party_rngs,
    )?);

    let mut out = Vec::with_capacity(n);
    for p in 0..n {
        let sk_seed_words: [BitslicedGf256x64; 4] = core::array::from_fn(|array_index| (packed_words[p][0..4])[array_index]);
        let sk_prf_words: [BitslicedGf256x64; 4] = core::array::from_fn(|array_index| (packed_words[p][4..8])[array_index]);
        let sk_seed_macs: [[[Tower128; 64]; 2]; 4] = core::array::from_fn(|array_index| (all_macs[p][0..4])[array_index]);
        let sk_prf_macs: [[[Tower128; 64]; 2]; 4] = core::array::from_fn(|array_index| (all_macs[p][4..8])[array_index]);
        let mut w = 0;
        while w < 8 {
            wipe_u64s(&mut packed_words[p][w]);
            w += 1;
        }
        out.push(SpdzAuthenticatedKeyShare {
            party_id: p,
            eval_point: eval_points[p],
            key_len,
            pk_seed,
            sk_seed_words,
            sk_seed_macs,
            sk_prf_words,
            sk_prf_macs,
            slh_profile: SlhProfileLatch::new(),
        });
    }
    Ok(out)
}

/// Dishonest-majority $t$-of-$n$ SPDZ Shamir cluster implementing sealed [`SlhMpcOracles`].
///
/// Enforces:
/// 1. Pre-cut SPDZ `MacCheck` over all intermediate Beaver `(d, e)` wires **strictly before** any
///    party commits/opens a cut-boundary output share (`[P0-08]`).
/// 2. Committed SPDZ `MacCheck` on the cut-boundary output shares themselves before minting
///    [`CutBoundaryMacToken::mint_verified`].
/// 3. Immediate `vault.poison_and_wipe()` across all quorum vaults on any `MacCheck` failure (`[P0-07]`).
/// 4. A quorum with a poisoned vault is refused by [`SpdzSlhMpcCluster::new`] and by every
///    evaluation and opening method. Poisoning zeroes the MAC key shares, so a `MacCheck`
///    run afterwards would accept any share whose MAC shares are zero.
pub struct SpdzSlhMpcCluster<'a> {
    pub session_id: [u8; 32],
    pub t: usize,
    pub quorum_pts: Vec<TowerGf256>,
    pub keys: &'a [SpdzAuthenticatedKeyShare],
    pub vaults: &'a mut [PreprocessedKeccakPartyVault],
    pub party_rngs: &'a mut [PartyPrivateRng],
    perm_ctr: usize,
}

impl<'a> SpdzSlhMpcCluster<'a> {
    pub fn new(
        session_id: [u8; 32],
        t: usize,
        keys: &'a [SpdzAuthenticatedKeyShare],
        vaults: &'a mut [PreprocessedKeccakPartyVault],
        party_rngs: &'a mut [PartyPrivateRng],
    ) -> Result<Self, KeccakMpcError> {
        let m = keys.len();
        if t == 0 || m < t || vaults.len() != m || party_rngs.len() != m {
            return Err(KeccakMpcError::InvalidParameters);
        }
        let quorum_pts: Vec<TowerGf256> = keys.iter().map(|k| k.eval_point).collect();
        validate_all_eval_points_gf256(&quorum_pts)?;
        let enrolled0 = keys[0]
            .slh_profile
            .enrolled()
            .map_err(|()| KeccakMpcError::InvalidParameters)?;
        for p in 0..m {
            let enrolled_p = keys[p]
                .slh_profile
                .enrolled()
                .map_err(|()| KeccakMpcError::InvalidParameters)?;
            let same_profile = match (&enrolled0, &enrolled_p) {
                (None, None) => true,
                (Some(a), Some(b)) => ct_eq_u64_x4(a, b),
                _ => false,
            };
            if vaults[p].eval_point != quorum_pts[p]
                || keys[p].key_len != keys[0].key_len
                || keys[p].pk_seed != keys[0].pk_seed
                || !same_profile
            {
                return Err(KeccakMpcError::InvalidParameters);
            }
        }
        spdz_refuse_poisoned_vaults(vaults)?;
        Ok(Self {
            session_id,
            t,
            quorum_pts,
            keys,
            vaults,
            party_rngs,
            perm_ctr: 0,
        })
    }

    fn poison_all(&mut self) {
        for v in self.vaults.iter_mut() {
            v.poison_and_wipe();
        }
    }

    /// Entry check of every evaluation and opening method.
    fn ensure_live(&mut self) -> Result<(), Fips205Error> {
        spdz_refuse_poisoned_vaults(self.vaults).map_err(|_| Fips205Error::MpcActiveTamperDetected)
    }

    /// Instance-bitsliced absorb of one public rate block per sponge instance into a zero
    /// state: bit `i` of every word belongs to `pub_blocks[i]`.
    fn init_batch_state_spdz(&self, pub_blocks: &[[u8; SHAKE256_RATE_BYTES]]) -> SpdzBitShares {
        let m = self.quorum_pts.len();
        let mut sh = vec![vec![[0u64; 8]; SPDZ_BATCH_POSITIONS]; m];
        let mut mac = vec![vec![[[Tower128::ZERO; 64]; 2]; SPDZ_BATCH_POSITIONS]; m];
        for pos in 0..8 * SHAKE256_RATE_BYTES {
            let mut word = 0u64;
            for (i, blk) in pub_blocks.iter().enumerate() {
                word |= u64::from((blk[pos / 8] >> (pos % 8)) & 1) << i;
            }
            if word != 0 {
                for p in 0..m {
                    let alpha_p = self.vaults[p].mac_alpha_lanes;
                    add_public_u64_to_spdz_word(word, &mut sh[p][pos], &mut mac[p][pos], &alpha_p);
                }
            }
        }
        (sh, mac)
    }

    /// Public single-block frame `PK.seed || ADRS || <n secret bytes> || 0x1f .. 0x80`.
    fn single_block_frames(
        n: usize,
        pk_seed: &[u8],
        adrs_batch: &[Fips205Adrs],
    ) -> Vec<[u8; SHAKE256_RATE_BYTES]> {
        adrs_batch
            .iter()
            .map(|adrs| {
                let mut blk = [0u8; SHAKE256_RATE_BYTES];
                blk[..n].copy_from_slice(pk_seed);
                blk[n..n + 32].copy_from_slice(&adrs.to_bytes());
                blk[2 * n + 32] = 0x1f;
                blk[SHAKE256_RATE_BYTES - 1] = 0x80;
                blk
            })
            .collect()
    }

    /// Run one 64-instance permutation and pass the batched `MacCheck` over every Beaver
    /// opening of all its instances before returning. Outputs stay shared.
    fn run_batch64_and_mac_check_spdz(
        &mut self,
        st_sh: &mut [Vec<BitslicedGf256x64>],
        st_mac: &mut [Vec<SpdzMacWord>],
    ) -> Result<(), Fips205Error> {
        self.ensure_live()?;
        let m = self.quorum_pts.len();
        let mut pending_opened = Vec::new();
        let mut pending_macs = SecretBuffer(vec![Vec::new(); m]);
        let ctr = self.perm_ctr;
        self.perm_ctr += 1;
        if eval_spdz_keccak_f1600_batch64(
            &self.session_id,
            ctr,
            self.t,
            &self.quorum_pts,
            st_sh,
            st_mac,
            self.vaults,
            &mut pending_opened,
            &mut pending_macs,
            self.party_rngs,
        )
        .is_err()
        {
            self.poison_all();
            return Err(Fips205Error::MpcActiveTamperDetected);
        }
        let alpha_sh = SecretBuffer(
            (0..m)
                .map(|p| self.vaults[p].mac_alpha_lanes)
                .collect::<Vec<[Tower128; 2]>>(),
        );
        if verify_pending_spdz_mac_batch(
            &self.session_id,
            "spdz_batch64_chi",
            self.t,
            &self.quorum_pts,
            &pending_opened,
            &pending_macs,
            &alpha_sh,
            self.party_rngs,
        )
        .is_err()
        {
            self.poison_all();
            return Err(Fips205Error::MpcActiveTamperDetected);
        }
        Ok(())
    }

    /// Evaluate up to 64 single-block `PRF(PK.seed, SK.seed, adrs_batch[i])` instances in one
    /// bitsliced permutation. Returns the `8 n` output bit positions as shares and MAC shares.
    fn eval_prf_batch64_spdz(
        &mut self,
        pk_seed: &[u8],
        adrs_batch: &[Fips205Adrs],
    ) -> Result<SpdzBitShares, Fips205Error> {
        self.ensure_live()?;
        let m = self.quorum_pts.len();
        let n = self.keys[0].key_len;
        let batch_len = adrs_batch.len();
        if batch_len == 0 || batch_len > 64 {
            return Err(Fips205Error::InvalidParameterSet);
        }
        let active_mask = batch_active_mask(batch_len);
        let frames = Self::single_block_frames(n, pk_seed, adrs_batch);
        let (st_sh, st_mac) = self.init_batch_state_spdz(&frames);
            let mut st_sh = SecretBuffer(st_sh);
            let mut st_mac = SecretBuffer(st_mac);

        // The same authenticated key bit feeds every active instance.
        let sk_off = 8 * (n + 32);
        for key_bit in 0..8 * n {
            let w = key_bit / 64;
            let bit = key_bit % 64;
            for p in 0..m {
                let elem = bs_gf256_extract_lane(&self.keys[p].sk_seed_words[w], bit);
                for (pl, plane) in st_sh[p][sk_off + key_bit].iter_mut().enumerate() {
                    let select = 0u64.wrapping_sub(u64::from((elem.0 >> pl) & 1));
                    *plane = select & active_mask;
                }
                for (l, lane_macs) in st_mac[p][sk_off + key_bit].iter_mut().enumerate() {
                    let key_mac = self.keys[p].sk_seed_macs[w][l][bit];
                    for slot in lane_macs[..batch_len].iter_mut() {
                        *slot = key_mac;
                    }
                }
            }
        }

        self.run_batch64_and_mac_check_spdz(&mut st_sh, &mut st_mac)?;

        let n_bits = 8 * n;
        let mut out_sh = Vec::with_capacity(m);
        let mut out_mac = Vec::with_capacity(m);
        for p in 0..m {
            out_sh.push(st_sh[p][..n_bits].to_vec());
            out_mac.push(st_mac[p][..n_bits].to_vec());
            for word in st_sh[p].iter_mut() {
                wipe_u64s(word);
            }
        }
        Ok((out_sh, out_mac))
    }

    /// Evaluate up to 64 single-block `F(PK.seed, adrs_batch[i], cur_i)` instances in one
    /// bitsliced permutation; instances with a zero bit in the public `exec_mask` keep `cur_i`
    /// (unequal WOTS+ chain depths).
    fn eval_f_step_masked_batch64_spdz(
        &mut self,
        pk_seed: &[u8],
        adrs_batch: &[Fips205Adrs],
        exec_mask: u64,
        cur_sh: &mut [Vec<BitslicedGf256x64>],
        cur_mac: &mut [Vec<SpdzMacWord>],
    ) -> Result<(), Fips205Error> {
        self.ensure_live()?;
        if exec_mask == 0 {
            return Ok(());
        }
        let m = self.quorum_pts.len();
        let n = self.keys[0].key_len;
        let n_bits = 8 * n;
        let frames = Self::single_block_frames(n, pk_seed, adrs_batch);
        let (st_sh, st_mac) = self.init_batch_state_spdz(&frames);
            let mut st_sh = SecretBuffer(st_sh);
            let mut st_mac = SecretBuffer(st_mac);
        let m1_off = 8 * (n + 32);
        for p in 0..m {
            for k in 0..n_bits {
                st_sh[p][m1_off + k] = cur_sh[p][k];
                st_mac[p][m1_off + k] = cur_mac[p][k];
            }
        }

        self.run_batch64_and_mac_check_spdz(&mut st_sh, &mut st_mac)?;

        for p in 0..m {
            for k in 0..n_bits {
                for pl in 0..8 {
                    cur_sh[p][k][pl] = (cur_sh[p][k][pl] & !exec_mask) | (st_sh[p][k][pl] & exec_mask);
                }
                for l in 0..2 {
                    for i in 0..64 {
                        if (exec_mask >> i) & 1 == 1 {
                            cur_mac[p][k][l][i] = st_mac[p][k][l][i];
                        }
                    }
                }
            }
            for word in st_sh[p].iter_mut() {
                wipe_u64s(word);
            }
        }
        Ok(())
    }

    /// Commit-and-open plus SPDZ `MacCheck` of instance-bitsliced cut-boundary words (every
    /// intermediate Beaver opening has already passed its batched `MacCheck`), then unpack
    /// `chunk_sizes[c]` blocks from the `8 n` words of chunk `c`. Poisons all vaults on failure.
    fn finalize_cut_batches_spdz(
        &mut self,
        phase: &'static str,
        cut_sh: &[Vec<BitslicedGf256x64>],
        cut_mac: &[Vec<SpdzMacWord>],
        chunk_sizes: &[usize],
    ) -> Result<(Vec<SlhBlock>, CutBoundaryMacToken), Fips205Error> {
        self.ensure_live()?;
        let m = self.quorum_pts.len();
        let n = self.keys[0].key_len;
        let n_bits = 8 * n;
        let alpha_sh = SecretBuffer(
            (0..m)
                .map(|p| self.vaults[p].mac_alpha_lanes)
                .collect::<Vec<[Tower128; 2]>>(),
        );
        let opened_words = match commit_and_open_spdz_bs_gf256_batch_quorum(
            &self.session_id,
            phase,
            self.t,
            &self.quorum_pts,
            cut_sh,
            cut_mac,
            &alpha_sh,
            self.party_rngs,
        ) {
            Ok(w) => w,
            Err(_) => {
                self.poison_all();
                return Err(Fips205Error::MpcActiveTamperDetected);
            }
        };
        // Every opened share must be a bit: planes 1..8 of each word are zero.
        if opened_words.len() != chunk_sizes.len() * n_bits
            || opened_words.iter().any(|w| w[1..] != [0u64; 7])
        {
            self.poison_all();
            return Err(Fips205Error::MpcActiveTamperDetected);
        }
        let tok = CutBoundaryMacToken::mint_verified();
        let mut blocks = Vec::with_capacity(chunk_sizes.iter().sum());
        for (c, &c_len) in chunk_sizes.iter().enumerate() {
            let words = &opened_words[c * n_bits..(c + 1) * n_bits];
            for b in 0..c_len {
                let mut blk = SlhBlock::zero(n);
                for byte_idx in 0..n {
                    let mut v = 0u8;
                    for bit in 0..8 {
                        v |= (((words[8 * byte_idx + bit][0] >> b) & 1) as u8) << bit;
                    }
                    blk.bytes[byte_idx] = v;
                }
                blocks.push(blk);
            }
        }
        Ok((blocks, tok))
    }

    /// Execute the two-stage pre-cut SPDZ `MacCheck` barrier (`[P0-08]`):
    /// 1. Verify ALL intermediate Beaver `(d, e)` MACs **before** touching cut-boundary shares!
    /// 2. Commit-and-open + SPDZ `MacCheck` the cut-boundary `SlhBlock` words!
    /// 3. Poison all vaults on any failure; mint [`CutBoundaryMacToken::mint_verified`] only on success!
    fn finalize_cut_blocks_spdz(
        &mut self,
        phase: &'static str,
        pending_opened: &[BitslicedGf256x64],
        pending_macs: &[Vec<[[Tower128; 64]; 2]>],
        cut_words_sh: &[Vec<BitslicedGf256x64>],
        cut_words_mac: &[Vec<[[Tower128; 64]; 2]>],
    ) -> Result<(Vec<SlhBlock>, CutBoundaryMacToken), Fips205Error> {
        self.ensure_live()?;
        let m = self.quorum_pts.len();
        let n = self.keys[0].key_len;
        let words_per_block = n / 8;
        let alpha_sh = SecretBuffer(
            (0..m)
                .map(|p| self.vaults[p].mac_alpha_lanes)
                .collect::<Vec<[Tower128; 2]>>(),
        );

        if verify_pending_spdz_mac_batch(
            &self.session_id,
            phase,
            self.t,
            &self.quorum_pts,
            pending_opened,
            pending_macs,
            &alpha_sh,
            self.party_rngs,
        )
        .is_err()
        {
            self.poison_all();
            return Err(Fips205Error::MpcActiveTamperDetected);
        }

        let opened_words = match commit_and_open_spdz_bs_gf256_batch_quorum(
            &self.session_id,
            phase,
            self.t,
            &self.quorum_pts,
            cut_words_sh,
            cut_words_mac,
            &alpha_sh,
            self.party_rngs,
        ) {
            Ok(w) => w,
            Err(_) => {
                self.poison_all();
                return Err(Fips205Error::MpcActiveTamperDetected);
            }
        };

        for w in &opened_words {
            if w[1..] != [0u64; 7] {
                self.poison_all();
                return Err(Fips205Error::MpcActiveTamperDetected);
            }
        }
        let tok = CutBoundaryMacToken::mint_verified();
        let num_blocks = opened_words.len() / words_per_block;
        let mut blocks = Vec::with_capacity(num_blocks);
        for b in 0..num_blocks {
            let mut blk = SlhBlock::zero(n);
            for w in 0..words_per_block {
                let bytes = opened_words[b * words_per_block + w][0].to_le_bytes();
                blk.bytes[8 * w..8 * (w + 1)].copy_from_slice(&bytes);
            }
            blocks.push(blk);
        }
        Ok((blocks, tok))
    }
}

impl<'a> sealed_mpc_oracles::Sealed for SpdzSlhMpcCluster<'a> {}

impl<'a> SlhMpcOracles for SpdzSlhMpcCluster<'a> {
    fn bind_key_params(&mut self, params: &Fips205Params, pk_seed: &[u8]) -> Result<(), Fips205Error> {
        self.ensure_live()?;
        if !params.is_valid()
            || pk_seed.len() != params.n
            || self
                .keys
                .iter()
                .any(|key| key.key_len != params.n || key.pk_seed[..key.key_len] != *pk_seed)
        {
            return Err(Fips205Error::InvalidParameterSet);
        }
        let want = slh_profile_digest_u64x4(params);
        for key in self.keys {
            match key.slh_profile.enrolled() {
                Ok(None) => {}
                Ok(Some(cur)) if ct_eq_u64_x4(&cur, &want) => {}
                _ => return Err(Fips205Error::InvalidParameterSet),
            }
        }
        for key in self.keys {
            key.slh_profile
                .bind(want)
                .map_err(|()| Fips205Error::InvalidParameterSet)?;
        }
        Ok(())
    }

    fn eval_prf_msg_mpc(
        &mut self,
        n: usize,
        opt_rand: &[u8],
        m_prime: &[u8],
    ) -> Result<(SlhBlock, CutBoundaryMacToken), Fips205Error> {
        self.ensure_live()?;
        let m = self.quorum_pts.len();
        if n != self.keys[0].key_len || opt_rand.len() != n {
            return Err(Fips205Error::InvalidParameterSet);
        }
        let out_words = n / 8;
        let total_len = 2 * n + m_prime.len();
        let num_blocks = (total_len / SHAKE256_RATE_BYTES) + 1;
        let mut padded_pub = vec![0u8; num_blocks * SHAKE256_RATE_BYTES];
        padded_pub[n..2 * n].copy_from_slice(opt_rand);
        padded_pub[2 * n..2 * n + m_prime.len()].copy_from_slice(m_prime);
        padded_pub[total_len] ^= 0x1f;
        let last_idx = num_blocks * SHAKE256_RATE_BYTES - 1;
        padded_pub[last_idx] ^= 0x80;

        let mut st_sh = SecretBuffer(vec![[[0u64; 8]; 25]; m]);
        let mut st_mac = SecretBuffer(vec![[[[Tower128::ZERO; 64]; 2]; 25]; m]);
        let mut pending_opened = Vec::new();
        let mut pending_macs = SecretBuffer(vec![Vec::new(); m]);

        for blk_idx in 0..num_blocks {
            let blk =
                &padded_pub[blk_idx * SHAKE256_RATE_BYTES..(blk_idx + 1) * SHAKE256_RATE_BYTES];
            if blk_idx == 0 {
                for w in 0..out_words {
                    for p in 0..m {
                        bs_gf256_xor_assign(&mut st_sh[p][w], &self.keys[p].sk_prf_words[w]);
                        xor_spdz_macs_assign(&mut st_mac[p][w], &self.keys[p].sk_prf_macs[w]);
                    }
                }
            }
            let start_lane = if blk_idx == 0 { out_words } else { 0 };
            for lane in start_lane..17 {
                let pub_w = u64::from_le_bytes(core::array::from_fn(|array_index| (blk[8 * lane..8 * (lane + 1)])[array_index]));
                if pub_w != 0 {
                    for p in 0..m {
                        let alpha_p = self.vaults[p].mac_alpha_lanes;
                        add_public_u64_to_spdz_word(
                            pub_w,
                            &mut st_sh[p][lane],
                            &mut st_mac[p][lane],
                            &alpha_p,
                        );
                    }
                }
            }
            let ctr = self.perm_ctr;
            self.perm_ctr += 1;
            if eval_spdz_keccak_f1600_single(
                &self.session_id,
                ctr,
                self.t,
                &self.quorum_pts,
                &mut st_sh,
                &mut st_mac,
                self.vaults,
                &mut pending_opened,
                &mut pending_macs,
                self.party_rngs,
            )
            .is_err()
            {
                self.poison_all();
                for party in st_sh.iter_mut() {
                    for lane in party.iter_mut() {
                        wipe_u64s(lane);
                    }
                }
                return Err(Fips205Error::MpcActiveTamperDetected);
            }
        }

        let mut cut_sh = SecretBuffer(vec![Vec::with_capacity(out_words); m]);
        let mut cut_mac = SecretBuffer(vec![Vec::with_capacity(out_words); m]);
        for p in 0..m {
            for w in 0..out_words {
                secret_vec_push(&mut cut_sh[p], st_sh[p][w]);
                secret_vec_push(&mut cut_mac[p], st_mac[p][w]);
            }
            let mut lane = 0;
            while lane < 25 {
                wipe_u64s(&mut st_sh[p][lane]);
                lane += 1;
            }
        }

        let (mut blks, tok) = self.finalize_cut_blocks_spdz(
            "spdz_cut_prf_msg",
            &pending_opened,
            &pending_macs,
            &cut_sh,
            &cut_mac,
        )?;
        Ok((blks.remove(0), tok))
    }

    fn eval_fors_trees_mpc(
        &mut self,
        params: &Fips205Params,
        pk_seed: &[u8],
        base_adrs: Fips205Adrs,
        fors_indices: &[u32],
    ) -> Result<(Vec<SlhBlock>, Vec<Vec<SlhBlock>>, CutBoundaryMacToken), Fips205Error> {
        self.bind_key_params(params, pk_seed)?;
        let m = self.quorum_pts.len();
        if fors_indices.len() != params.k {
            return Err(Fips205Error::InvalidParameterSet);
        }
        let t_leaves = 1usize << params.a;
        let total_leaves = params.k * t_leaves;

        let mut cut_sh = SecretBuffer(vec![Vec::new(); m]);
        let mut cut_mac = SecretBuffer(vec![Vec::new(); m]);
        let mut chunk_sizes = Vec::new();

        // The `k` revealed FORS secret values chunked in 64-instance batches (`<= 64` per batch).
        let mut rev_cursor = 0usize;
        while rev_cursor < params.k {
            let rev_len = (params.k - rev_cursor).min(64);
            let mut rev_prf_adrs = Vec::with_capacity(rev_len);
            for off in 0..rev_len {
                let i = rev_cursor + off;
                let idx_i = fors_indices[i] as usize;
                if idx_i >= t_leaves {
                    return Err(Fips205Error::MpcActiveTamperDetected);
                }
                let mut prf_adrs = base_adrs.with_type_and_clear(Fips205AdrsType::ForsPrf);
                prf_adrs.key_pair = base_adrs.key_pair;
                prf_adrs.f6 = (i * t_leaves + idx_i) as u32;
                rev_prf_adrs.push(prf_adrs);
            }
            let (rev_sh, rev_mac) = self.eval_prf_batch64_spdz(pk_seed, &rev_prf_adrs)?;
            let rev_sh = SecretBuffer(rev_sh);
            let rev_mac = SecretBuffer(rev_mac);
            for p in 0..m {
                secret_vec_extend_from_slice(&mut cut_sh[p], &rev_sh[p]);
                secret_vec_extend_from_slice(&mut cut_mac[p], &rev_mac[p]);
            }
            chunk_sizes.push(rev_len);
            rev_cursor += rev_len;
        }

        // All `k * 2^a` leaves `F(PRF(..))`, 64 instances per permutation; unrevealed secret
        // values never leave their shares.
        let mut leaf_cursor = 0usize;
        while leaf_cursor < total_leaves {
            let chunk_len = (total_leaves - leaf_cursor).min(64);
            let mut prf_batch = Vec::with_capacity(chunk_len);
            let mut leaf_batch = Vec::with_capacity(chunk_len);
            for c in 0..chunk_len {
                let flat = (leaf_cursor + c) as u32;
                let mut prf_a = base_adrs.with_type_and_clear(Fips205AdrsType::ForsPrf);
                prf_a.key_pair = base_adrs.key_pair;
                prf_a.f6 = flat;
                prf_batch.push(prf_a);
                let mut leaf_a = base_adrs;
                leaf_a.adrs_type = Fips205AdrsType::ForsTree;
                leaf_a.f5 = 0;
                leaf_a.f6 = flat;
                leaf_batch.push(leaf_a);
            }
            let (cur_sh, cur_mac) = self.eval_prf_batch64_spdz(pk_seed, &prf_batch)?;
            let mut cur_sh = SecretBuffer(cur_sh);
            let mut cur_mac = SecretBuffer(cur_mac);
            self.eval_f_step_masked_batch64_spdz(
                pk_seed,
                &leaf_batch,
                batch_active_mask(chunk_len),
                &mut cur_sh,
                &mut cur_mac,
            )?;
            for p in 0..m {
                secret_vec_extend_from_slice(&mut cut_sh[p], &cur_sh[p]);
                secret_vec_extend_from_slice(&mut cut_mac[p], &cur_mac[p]);
            }
            chunk_sizes.push(chunk_len);
            leaf_cursor += chunk_len;
        }

        let (all_blocks, tok) =
            self.finalize_cut_batches_spdz("spdz_cut_fors_trees", &cut_sh, &cut_mac, &chunk_sizes)?;
        let revealed_sks = all_blocks[0..params.k].to_vec();
        let mut fors_all_leaves = Vec::with_capacity(params.k);
        for i in 0..params.k {
            let base = params.k + i * t_leaves;
            fors_all_leaves.push(all_blocks[base..base + t_leaves].to_vec());
        }
        Ok((revealed_sks, fors_all_leaves, tok))
    }

    fn eval_wots_pkgen_subtree_mpc(
        &mut self,
        params: &Fips205Params,
        pk_seed: &[u8],
        layer: u32,
        tree: u128,
    ) -> Result<(Vec<SlhBlock>, CutBoundaryMacToken), Fips205Error> {
        self.bind_key_params(params, pk_seed)?;
        let n_leaves = 1usize << params.hp;
        self.eval_wots_chains_batch64_spdz(
            "spdz_cut_wots_pkgen",
            params,
            pk_seed,
            layer,
            tree,
            |_, _| 15,
            n_leaves,
        )
    }

    fn eval_wots_layer_sign_and_siblings_mpc(
        &mut self,
        _authorization: crate::fips205::OracleCallToken,
        params: &Fips205Params,
        pk_seed: &[u8],
        layer: u32,
        tree: u128,
        active_kp: u32,
        msg_to_sign: &SlhBlock,
    ) -> Result<(Vec<SlhBlock>, CutBoundaryMacToken), Fips205Error> {
        self.bind_key_params(params, pk_seed)?;
        let n = params.n;
        let n_leaves = 1usize << params.hp;
        if msg_to_sign.len() != n || (active_kp as usize) >= n_leaves {
            return Err(Fips205Error::InvalidParameterSet);
        }
        let (digits, ell_check) = try_wots_base16_digits_and_csum(msg_to_sign.as_slice())?;
        if ell_check != params.ell() {
            return Err(Fips205Error::InvalidParameterSet);
        }
        self.eval_wots_chains_batch64_spdz(
            "spdz_cut_wots_layer",
            params,
            pk_seed,
            layer,
            tree,
            |kp, ch| {
                if kp == active_kp {
                    u32::from(digits[ch])
                } else {
                    15
                }
            },
            n_leaves,
        )
    }
}

impl SpdzSlhMpcCluster<'_> {
    /// All `n_leaves * ell` WOTS+ chains of one XMSS tree, 64 chains per permutation: chain
    /// `(kp, ch)` is advanced `target_steps(kp, ch)` times (public step counts) and its end value
    /// is opened at the cut.
    #[expect(
        clippy::too_many_arguments,
        reason = "One XMSS-layer evaluation: tree address, step schedule and cut label"
    )]
    fn eval_wots_chains_batch64_spdz(
        &mut self,
        phase: &'static str,
        params: &Fips205Params,
        pk_seed: &[u8],
        layer: u32,
        tree: u128,
        target_steps: impl Fn(u32, usize) -> u32,
        n_leaves: usize,
    ) -> Result<(Vec<SlhBlock>, CutBoundaryMacToken), Fips205Error> {
        self.ensure_live()?;
        let m = self.quorum_pts.len();
        let ell = params.ell();
        let total_chains = n_leaves * ell;
        let chain_adrs = |flat: usize, adrs_type: Fips205AdrsType, step: u32| {
            let mut a = Fips205Adrs::ZERO;
            a.layer = layer;
            a.set_tree_address(tree);
            a.adrs_type = adrs_type;
            a.key_pair = (flat / ell) as u32;
            a.f5 = (flat % ell) as u32;
            a.f6 = step;
            a
        };

        let mut cut_sh = SecretBuffer(vec![Vec::new(); m]);
        let mut cut_mac = SecretBuffer(vec![Vec::new(); m]);
        let mut chunk_sizes = Vec::new();
        let mut cursor = 0usize;
        while cursor < total_chains {
            let chunk_len = (total_chains - cursor).min(64);
            let prf_batch: Vec<Fips205Adrs> = (0..chunk_len)
                .map(|c| chain_adrs(cursor + c, Fips205AdrsType::WotsPrf, 0))
                .collect();
            let steps: Vec<u32> = (0..chunk_len)
                .map(|c| {
                    let flat = cursor + c;
                    target_steps((flat / ell) as u32, flat % ell)
                })
                .collect();
            let (cur_sh, cur_mac) = self.eval_prf_batch64_spdz(pk_seed, &prf_batch)?;
            let mut cur_sh = SecretBuffer(cur_sh);
            let mut cur_mac = SecretBuffer(cur_mac);
            for step in 0..15u32 {
                let mut exec_mask = 0u64;
                for (c, &target) in steps.iter().enumerate() {
                    if step < target {
                        exec_mask |= 1u64 << c;
                    }
                }
                let step_batch: Vec<Fips205Adrs> = (0..chunk_len)
                    .map(|c| chain_adrs(cursor + c, Fips205AdrsType::WotsHash, step))
                    .collect();
                self.eval_f_step_masked_batch64_spdz(
                    pk_seed,
                    &step_batch,
                    exec_mask,
                    &mut cur_sh,
                    &mut cur_mac,
                )?;
            }
            for p in 0..m {
                secret_vec_extend_from_slice(&mut cut_sh[p], &cur_sh[p]);
                secret_vec_extend_from_slice(&mut cut_mac[p], &cur_mac[p]);
            }
            chunk_sizes.push(chunk_len);
            cursor += chunk_len;
        }
        self.finalize_cut_batches_spdz(phase, &cut_sh, &cut_mac, &chunk_sizes)
    }
}

// ============================================================================
// 3. Distributed `Corduroy` / `Baggy` (`Cshake256Suite`) & `DkgCachedSubtrees`
// ============================================================================

/// Public XMSS subtree leaf cache constructed strictly via distributed cut-boundary MPC
/// (`0` `PqSecretKey`, bounded `max_cached_leaves` to prevent exponential memory DoS).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DkgCachedSubtrees {
    pub top_layer: u32,
    pub top_leaves: Vec<[u8; 32]>,
    pub pk: PqPublicKey,
}

impl DkgCachedSubtrees {
    /// Build the top-layer XMSS subtree leaf cache and [`PqPublicKey`] via distributed 2-of-3 RSS
    /// `cSHAKE256` cut-boundary evaluation (`0` `sk: &PqSecretKey` in cleartext!).
    ///
    /// This is key generation for the stateless hash signature: the root computed here from
    /// the shares, together with `params`, is recorded in the three key shares, and
    /// [`sign_stateless_tsw_rss_mpc`] signs only for that root and parameter set. Shares
    /// that are already bound are evaluated again only under the same parameter set (a
    /// different chain length would open interior chain values of the bound key), and the
    /// recomputed root must equal the bound one.
    pub fn build_distributed_rss(
        params: &PqHashParams,
        cluster: &mut RssSlhMpcCluster,
        max_cached_leaves: usize,
    ) -> Result<Self, KeccakMpcError> {
        if !params.is_well_formed() || cluster.keys[0].key_len != 32 {
            return Err(KeccakMpcError::InvalidParameters);
        }
        let n_leaves = 1usize << params.subtree_height;
        if n_leaves > max_cached_leaves {
            return Err(KeccakMpcError::SubtreeCacheCapExceeded {
                requested: n_leaves,
                max_allowed: max_cached_leaves,
            });
        }
        cluster.ensure_live()?;
        let params_digest = tsw_params_digest(params);
        let prior = cluster.tsw_binding()?;
        if prior.is_some_and(|b| !ct_eq_bytes32(&b.params_digest, &params_digest)) {
            return Err(KeccakMpcError::KeyBindingMismatch);
        }
        let top_layer = (params.num_layers - 1) as u32;
        let pk_seed = cluster.keys[0].pk_seed;
        let endpoints = eval_tsw_wots_subtree_rss(params, cluster, &pk_seed, top_layer, 0, None)?;

        let mut top_leaves = Vec::with_capacity(n_leaves);
        for kp in 0..n_leaves {
            let wotspk_adrs = HashAdrs {
                layer: top_layer,
                tree: 0,
                kind: AdrsKind::WotsPk,
                key_pair: kp as u32,
                chain_idx: 0,
                hash_step: 0,
            };
            let ep = &endpoints[kp * params.ell1..(kp + 1) * params.ell1];
            top_leaves.push(th_tweak_tl(Cshake256Suite, &pk_seed, &wotspk_adrs, ep));
        }
        let pk_root = build_tsw_merkle_root(
            Cshake256Suite,
            &pk_seed,
            top_layer,
            0,
            AdrsKind::Tree,
            0,
            params.subtree_height,
            0,
            &top_leaves,
            0,
        )
        .0;
        match prior {
            Some(bound) => {
                if !ct_eq_bytes32(&bound.pk_root, &pk_root) {
                    return Err(KeccakMpcError::KeyBindingMismatch);
                }
            }
            None => {
                for key in &mut cluster.keys {
                    key.tsw_binding = Some(TswKeyBinding {
                        params_digest,
                        pk_root,
                    });
                }
            }
        }
        Ok(Self {
            top_layer,
            top_leaves,
            pk: PqPublicKey { pk_seed, pk_root },
        })
    }
}

#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the existing explicit protocol interface for callers"
)]
fn build_tsw_merkle_root<S: TweakableHashSuite>(
    suite: S,
    pk_seed: &[u8; 32],
    layer: u32,
    tree: u64,
    kind: AdrsKind,
    key_pair: u32,
    height: usize,
    tree_idx_offset: usize,
    leaves: &[[u8; 32]],
    target_idx: usize,
) -> ([u8; 32], Vec<[u8; 32]>) {
    // Same node hash, node addressing and root-first path order as the verifier's
    // `walk_merkle_auth_path`: the public tree must never be rebuilt by a second convention.
    build_merkle_from_leaves_topdown(
        suite,
        pk_seed,
        layer,
        tree,
        kind,
        key_pair,
        leaves,
        height,
        tree_idx_offset >> height,
        target_idx,
    )
}

/// Sponge state after the `Cshake256Suite` customization block, shared by every tweakable-hash
/// role (the role tag travels inside the preimage frame).
pub(crate) const TSW_SUITE_MIDSTATE: [u64; 25] =
    crate::sponge::keccak::cshake256_static_midstate(PQ_CSHAKE_SUITE_CUSTOM);

/// Byte offset of the 32-byte secret argument inside `th_preimage(tag, pk_seed, adrs, [secret])`:
/// field count, three length-prefixed public fields, and the secret's own length prefix.
pub(crate) const fn tsw_secret32_offset(tag_len: usize) -> usize {
    1 + (1 + tag_len) + (1 + 32) + (1 + 32) + 1
}
pub(crate) const TSW_PRF_SECRET_OFFSET: usize = tsw_secret32_offset(TAG_PRF.len());
pub(crate) const TSW_F_SECRET_OFFSET: usize = tsw_secret32_offset(TAG_TH_F.len());

/// Public bytes of the single rate block that the reference suite absorbs for
/// `th_call_secret(role_tag, pk_seed, adrs, [secret32])`: the exact reference preimage with a
/// zeroed secret slot, followed by `cSHAKE256` padding. The shared secret is XORed into the
/// slot at [`tsw_secret32_offset`].
pub(crate) fn tsw_secret32_frame(
    role_tag: &[u8],
    pk_seed: &[u8; 32],
    adrs: &HashAdrs,
) -> [u8; SHAKE256_RATE_BYTES] {
    let (template, offset) = build_single_secret32_template(role_tag, pk_seed, adrs);
    assert_eq!(offset, tsw_secret32_offset(role_tag.len()));
    assert!(template.len() < SHAKE256_RATE_BYTES);
    let mut frame = [0u8; SHAKE256_RATE_BYTES];
    frame[..template.len()].copy_from_slice(&template);
    frame[template.len()] = 0x04;
    frame[SHAKE256_RATE_BYTES - 1] ^= 0x80;
    frame
}

/// Evaluate the reference suite's `th_secret_prf` (`TAG_PRF`) and subsequent `th_chain_f`
/// (`TAG_TH_F`) chain steps in 64-way 2-of-3 RSS (`active_sign = Some((active_kp, &digits))` for signing, `None` for pkgen).
fn eval_tsw_wots_subtree_rss(
    params: &PqHashParams,
    cluster: &mut RssSlhMpcCluster,
    pk_seed: &[u8; 32],
    layer: u32,
    tree: u64,
    active_sign: Option<(usize, &[usize])>,
) -> Result<Vec<[u8; 32]>, KeccakMpcError> {
    let n_leaves = 1usize << params.subtree_height;
    let ell1 = params.ell1;
    let total_chains = n_leaves * ell1;
    let max_steps = params.w - 1;

    // Both roles share the suite customization block; the role tag is the first frame field.
    let prf_midstate = TSW_SUITE_MIDSTATE;
    let tweak_midstate = TSW_SUITE_MIDSTATE;

    let mut cut = RssCutBuffer::new();
    let mut chunk_sizes = Vec::new();

    let mut cursor = 0usize;
    while cursor < total_chains {
        let chunk_len = (total_chains - cursor).min(64);
        let active_mask = batch_active_mask(chunk_len);

        // Block 0 absorbs `cshake_customization_prefix(136 B)` (identical public block across all 64 lanes,
        // precomputed in `prf_midstate`!)
        // Block 1 absorbs `encode_multi_frame(&[pk_seed(32B), adrs(32B), sk_seed(32B)])`:
        // frame = `[3, 32, pk_seed(32), 32, adrs(32), 32, sk_seed(32)]` = `1 + 1 + 32 + 1 + 32 + 1 + 32 = 100 bytes < 136`!
        let mut st_p = SecretBuffer([[0u64; 1600]; 3]);
        let mut st_s = SecretBuffer([[0u64; 1600]; 3]);
        init_rss_state_from_public_midstate(&prf_midstate, active_mask, &mut st_p, &mut st_s);

        let mut targets = [0usize; 64];
        let mut b = 0;
        while b < chunk_len {
            let flat = cursor + b;
            let kp = flat / ell1;
            let ch = flat % ell1;
            targets[b] = match active_sign {
                Some((act_kp, digs)) if kp == act_kp => digs[ch],
                _ => max_steps,
            };
            let adrs = HashAdrs {
                layer,
                tree,
                kind: AdrsKind::WotsPrf,
                key_pair: kp as u32,
                chain_idx: ch as u32,
                hash_step: 0,
            };
            let pub_frame = tsw_secret32_frame(TAG_PRF, pk_seed, &adrs);

            let bit_b = 1u64 << b;
            for byte_idx in 0..SHAKE256_RATE_BYTES {
                let v = pub_frame[byte_idx];
                for bit in 0..8 {
                    if ((v >> bit) & 1) == 1 {
                        st_p[0][8 * byte_idx + bit] ^= bit_b;
                        st_s[2][8 * byte_idx + bit] ^= bit_b;
                    }
                }
            }
            b += 1;
        }
        for p in 0..3 {
            let (sk_p, sk_s) = cluster.keys[p].sk_seed_shares();
            for byte_idx in 0..32 {
                for bit in 0..8 {
                    let mp = 0u64.wrapping_sub(((sk_p[byte_idx] >> bit) & 1) as u64) & active_mask;
                    let ms = 0u64.wrapping_sub(((sk_s[byte_idx] >> bit) & 1) as u64) & active_mask;
                    st_p[p][8 * (TSW_PRF_SECRET_OFFSET + byte_idx) + bit] ^= mp;
                    st_s[p][8 * (TSW_PRF_SECRET_OFFSET + byte_idx) + bit] ^= ms;
                }
            }
        }
        cluster.permute_batch64_deferred(chunk_len, &mut st_p, &mut st_s)?;

        let mut cur_p = SecretBuffer([[0u64; 256]; 3]);
        let mut cur_s = SecretBuffer([[0u64; 256]; 3]);
        for p in 0..3 {
            cur_p[p].copy_from_slice(&st_p[p][..256]);
            cur_s[p].copy_from_slice(&st_s[p][..256]);
            wipe_u64s(&mut st_p[p]);
            wipe_u64s(&mut st_s[p]);
        }

        // Advance `step = 0..max_steps` via `cSHAKE256("QSAG.TH.TWEAK/v1", [3, 32, pk_seed, 32, adrs, 32, cur])`
        for step in 0..max_steps {
            let mut exec_mask = 0u64;
            let mut b = 0;
            while b < chunk_len {
                if step < targets[b] {
                    exec_mask |= 1u64 << b;
                }
                b += 1;
            }
            if exec_mask == 0 {
                continue;
            }
            let mut sp = SecretBuffer([[0u64; 1600]; 3]);
            let mut ss = SecretBuffer([[0u64; 1600]; 3]);
            init_rss_state_from_public_midstate(&tweak_midstate, active_mask, &mut sp, &mut ss);

            for b in 0..chunk_len {
                let flat = cursor + b;
                let kp = flat / ell1;
                let ch = flat % ell1;
                let adrs = HashAdrs {
                    layer,
                    tree,
                    kind: AdrsKind::WotsHash,
                    key_pair: kp as u32,
                    chain_idx: ch as u32,
                    hash_step: step as u32,
                };
                let pub_frame = tsw_secret32_frame(TAG_TH_F, pk_seed, &adrs);

                let bit_b = 1u64 << b;
                for byte_idx in 0..SHAKE256_RATE_BYTES {
                    let v = pub_frame[byte_idx];
                    for bit in 0..8 {
                        if ((v >> bit) & 1) == 1 {
                            sp[0][8 * byte_idx + bit] ^= bit_b;
                            ss[2][8 * byte_idx + bit] ^= bit_b;
                        }
                    }
                }
            }
            for p in 0..3 {
                for bit_idx in 0..256 {
                    sp[p][8 * TSW_F_SECRET_OFFSET + bit_idx] ^= cur_p[p][bit_idx];
                    ss[p][8 * TSW_F_SECRET_OFFSET + bit_idx] ^= cur_s[p][bit_idx];
                }
            }
            if let Err(e) = cluster.permute_batch64_deferred(chunk_len, &mut sp, &mut ss) {
                wipe_rss_states(&mut cur_p, &mut cur_s);
                return Err(e);
            }

            let keep = !exec_mask;
            for p in 0..3 {
                for bit_idx in 0..256 {
                    cur_p[p][bit_idx] = (cur_p[p][bit_idx] & keep) | (sp[p][bit_idx] & exec_mask);
                    cur_s[p][bit_idx] = (cur_s[p][bit_idx] & keep) | (ss[p][bit_idx] & exec_mask);
                }
                wipe_u64s(&mut sp[p]);
                wipe_u64s(&mut ss[p]);
            }
        }

        for p in 0..3 {
            cut.push_party_slices(p, &cur_p[p], &cur_s[p]);
            wipe_u64s(&mut cur_p[p]);
            wipe_u64s(&mut cur_s[p]);
        }
        chunk_sizes.push(chunk_len);
        cursor += chunk_len;
    }

    let (opened_words, _tok) = cluster.flush_verify_and_open_cut("rss_tsw_wots_subtree", &cut)?;

    let mut out = Vec::with_capacity(total_chains);
    let mut off = 0usize;
    for &c_len in &chunk_sizes {
        let slice = &opened_words[off..off + 256];
        for b in 0..c_len {
            let mut node = [0u8; 32];
            for byte_idx in 0..32 {
                let mut v = 0u8;
                for bit in 0..8 {
                    v |= (((slice[8 * byte_idx + bit] >> b) & 1) as u8) << bit;
                }
                node[byte_idx] = v;
            }
            out.push(node);
        }
        off += 256;
    }
    Ok(out)
}

/// Public `opt_rand` input of the randomizer PRF: fixed by the public key, as in FIPS 205
/// deterministic signing where `opt_rand = PK.seed`.
fn tsw_rss_opt_rand(pk: &PqPublicKey) -> [u8; 32] {
    cshake256_32(
        b"QSAG.TSW.RSS.OPT_RAND/v1",
        &encode_multi_frame(&[&pk.pk_seed, &pk.pk_root]),
    )
}

/// Sign a message under stateless `Corduroy` / `Baggy` (`Cshake256Suite`) via distributed
/// 2-of-3 RSS cut-boundary MPC (`0` `PqSecretKey` reconstruction!), verifying the assembled
/// signature with [`verify_pq_hash_sig`] before returning!
///
/// The key shares must have been bound by [`DkgCachedSubtrees::build_distributed_rss`];
/// `params` and `pk` are checked against that binding before anything is evaluated, so the
/// FORS indices and WOTS digits are never derived from a root or parameter set the shares
/// were not generated for.
///
/// The randomizer is `R = PRF_msg(SK.prf, opt_rand, mu)` with `opt_rand` fixed by the public
/// key and `mu` the message digest, evaluated on the shared `SK.prf`. It is a function of
/// the key and the message only: a retry in another session, with other party randomness,
/// opens the same `R` and therefore the same FORS instance and indices. An aborting signer
/// gains no second choice of `R` for a message.
pub fn sign_stateless_tsw_rss_mpc(
    params: &PqHashParams,
    cluster: &mut RssSlhMpcCluster,
    pk: &PqPublicKey,
    msg: &[u8],
    max_grind: u32,
) -> Result<PqHashSig, KeccakMpcError> {
    if !params.is_well_formed()
        || params.stateful
        || cluster.keys[0].key_len != 32
        || !ct_eq_bytes(&pk.pk_seed, &cluster.keys[0].pk_seed)
    {
        return Err(KeccakMpcError::InvalidParameters);
    }
    cluster.ensure_live()?;
    let binding = cluster
        .tsw_binding()?
        .ok_or(KeccakMpcError::KeyBindingMismatch)?;
    if !ct_eq_bytes32(&binding.params_digest, &tsw_params_digest(params))
        || !ct_eq_bytes32(&binding.pk_root, &pk.pk_root)
    {
        return Err(KeccakMpcError::KeyBindingMismatch);
    }

    let mu = th_pre_hash(Cshake256Suite, &pk.pk_seed, &pk.pk_root, msg);
    let transcript = encode_multi_frame(&[&cluster.session_id, &mu]);
    for rng in &mut cluster.party_rngs { rng.hedge_transcript(&transcript); }
    cluster.mask_session.hedge_transcript(&transcript);
    let opt_rand = tsw_rss_opt_rand(pk);
    let (r_blk, _tok_r) = cluster.prf_msg_shared(32, &opt_rand, &mu)?;
    let mut r_rand = [0u8; 32];
    r_rand.copy_from_slice(r_blk.as_slice());

    let (leaf_global_idx, idxs) = derive_stateless_leaf_and_fors_indices(
        Cshake256Suite,
        params,
        &r_rand,
        &pk.pk_seed,
        &pk.pk_root,
        &mu,
    )
    .ok_or(KeccakMpcError::InvalidParameters)?;

    let sub_leaves = 1usize << params.subtree_height;
    let kp0 = (leaf_global_idx % sub_leaves) as u32;
    let tree0 = (leaf_global_idx / sub_leaves) as u64;

    // Evaluate FORS trees in 64-way RSS (`cSHAKE256("QSAG.TH.PRF/v1", ...)` -> `cSHAKE256("QSAG.TH.TWEAK/v1", ...)`)
    let t_leaves = 1usize << params.fors_height;
    let total_fors = params.fors_trees * t_leaves;
    // Both roles share the suite customization block; the role tag is the first frame field.
    let prf_midstate = TSW_SUITE_MIDSTATE;
    let tweak_midstate = TSW_SUITE_MIDSTATE;

    let mut cut = RssCutBuffer::new();
    let mut fors_chunks = Vec::new();

    // First batch: `params.fors_trees` (`<= 64`) revealed FORS `secret_val`s
    {
        let mut st_p = SecretBuffer([[0u64; 1600]; 3]);
        let mut st_s = SecretBuffer([[0u64; 1600]; 3]);
        let mask_k = batch_active_mask(params.fors_trees);
        init_rss_state_from_public_midstate(&prf_midstate, mask_k, &mut st_p, &mut st_s);
        let mut j = 0;
        while j < params.fors_trees {
            let adrs = HashAdrs {
                layer: 0,
                tree: tree0,
                kind: AdrsKind::ForsPrf,
                key_pair: kp0,
                chain_idx: j as u32,
                hash_step: idxs[j] as u32,
            };
            let pub_frame = tsw_secret32_frame(TAG_PRF, &pk.pk_seed, &adrs);
            let bit_b = 1u64 << j;
            for byte_idx in 0..SHAKE256_RATE_BYTES {
                let v = pub_frame[byte_idx];
                for bit in 0..8 {
                    if ((v >> bit) & 1) == 1 {
                        st_p[0][8 * byte_idx + bit] ^= bit_b;
                        st_s[2][8 * byte_idx + bit] ^= bit_b;
                    }
                }
            }
            j += 1;
        }
        for p in 0..3 {
            let (sk_p, sk_s) = cluster.keys[p].sk_seed_shares();
            for byte_idx in 0..32 {
                for bit in 0..8 {
                    let mp = 0u64.wrapping_sub(((sk_p[byte_idx] >> bit) & 1) as u64) & mask_k;
                    let ms = 0u64.wrapping_sub(((sk_s[byte_idx] >> bit) & 1) as u64) & mask_k;
                    st_p[p][8 * (TSW_PRF_SECRET_OFFSET + byte_idx) + bit] ^= mp;
                    st_s[p][8 * (TSW_PRF_SECRET_OFFSET + byte_idx) + bit] ^= ms;
                }
            }
        }
        cluster.permute_batch64_deferred(params.fors_trees, &mut st_p, &mut st_s)?;
        for p in 0..3 {
            cut.push_party_slices(p, &st_p[p][..256], &st_s[p][..256]);
            wipe_u64s(&mut st_p[p]);
            wipe_u64s(&mut st_s[p]);
        }
    }

    // All `total_fors` leaf hashes `T_l(pk_seed, ForsTree_adrs, [secret_val])` (`PRF -> TWEAK` inside MPC!)
    let mut f_cur = 0usize;
    while f_cur < total_fors {
        let c_len = (total_fors - f_cur).min(64);
        let mask_c = batch_active_mask(c_len);
        let mut st_p = SecretBuffer([[0u64; 1600]; 3]);
        let mut st_s = SecretBuffer([[0u64; 1600]; 3]);
        init_rss_state_from_public_midstate(&prf_midstate, mask_c, &mut st_p, &mut st_s);
        for b in 0..c_len {
            let flat = f_cur + b;
            let tree_j = flat / t_leaves;
            let leaf_i = flat % t_leaves;
            let adrs = HashAdrs {
                layer: 0,
                tree: tree0,
                kind: AdrsKind::ForsPrf,
                key_pair: kp0,
                chain_idx: tree_j as u32,
                hash_step: leaf_i as u32,
            };
            let pub_frame = tsw_secret32_frame(TAG_PRF, &pk.pk_seed, &adrs);
            let bit_b = 1u64 << b;
            for byte_idx in 0..SHAKE256_RATE_BYTES {
                let v = pub_frame[byte_idx];
                for bit in 0..8 {
                    if ((v >> bit) & 1) == 1 {
                        st_p[0][8 * byte_idx + bit] ^= bit_b;
                        st_s[2][8 * byte_idx + bit] ^= bit_b;
                    }
                }
            }
        }
        for p in 0..3 {
            let (sk_p, sk_s) = cluster.keys[p].sk_seed_shares();
            for byte_idx in 0..32 {
                for bit in 0..8 {
                    let mp = 0u64.wrapping_sub(((sk_p[byte_idx] >> bit) & 1) as u64) & mask_c;
                    let ms = 0u64.wrapping_sub(((sk_s[byte_idx] >> bit) & 1) as u64) & mask_c;
                    st_p[p][8 * (TSW_PRF_SECRET_OFFSET + byte_idx) + bit] ^= mp;
                    st_s[p][8 * (TSW_PRF_SECRET_OFFSET + byte_idx) + bit] ^= ms;
                }
            }
        }
        cluster.permute_batch64_deferred(c_len, &mut st_p, &mut st_s)?;

        // Hash `secret_val` -> `leaf_hash` via `cSHAKE256("QSAG.TH.TWEAK/v1", [3, 32, pk_seed, 32, leaf_adrs, 32, secret_val])`
        let mut sp = SecretBuffer([[0u64; 1600]; 3]);
        let mut ss = SecretBuffer([[0u64; 1600]; 3]);
        init_rss_state_from_public_midstate(&tweak_midstate, mask_c, &mut sp, &mut ss);
        for b in 0..c_len {
            let flat = f_cur + b;
            let tree_j = flat / t_leaves;
            let leaf_i = flat % t_leaves;
            let leaf_adrs = HashAdrs {
                layer: 0,
                tree: tree0,
                kind: AdrsKind::ForsTree,
                key_pair: kp0,
                chain_idx: tree_j as u32,
                hash_step: leaf_i as u32,
            };
            let pub_frame = tsw_secret32_frame(TAG_TH_F, &pk.pk_seed, &leaf_adrs);
            let bit_b = 1u64 << b;
            for byte_idx in 0..SHAKE256_RATE_BYTES {
                let v = pub_frame[byte_idx];
                for bit in 0..8 {
                    if ((v >> bit) & 1) == 1 {
                        sp[0][8 * byte_idx + bit] ^= bit_b;
                        ss[2][8 * byte_idx + bit] ^= bit_b;
                    }
                }
            }
        }
        for p in 0..3 {
            for bit_idx in 0..256 {
                sp[p][8 * TSW_F_SECRET_OFFSET + bit_idx] ^= st_p[p][bit_idx];
                ss[p][8 * TSW_F_SECRET_OFFSET + bit_idx] ^= st_s[p][bit_idx];
            }
            wipe_u64s(&mut st_p[p]);
            wipe_u64s(&mut st_s[p]);
        }
        cluster.permute_batch64_deferred(c_len, &mut sp, &mut ss)?;
        for p in 0..3 {
            cut.push_party_slices(p, &sp[p][..256], &ss[p][..256]);
            wipe_u64s(&mut sp[p]);
            wipe_u64s(&mut ss[p]);
        }
        fors_chunks.push(c_len);
        f_cur += c_len;
    }

    let (fors_opened, _tok_f) = cluster.flush_verify_and_open_cut("rss_tsw_fors_cut", &cut)?;

    let mut rev_secrets = Vec::with_capacity(params.fors_trees);
    for j in 0..params.fors_trees {
        let mut s_val = [0u8; 32];
        for byte_idx in 0..32 {
            let mut v = 0u8;
            for bit in 0..8 {
                v |= (((fors_opened[8 * byte_idx + bit] >> j) & 1) as u8) << bit;
            }
            s_val[byte_idx] = v;
        }
        rev_secrets.push(s_val);
    }

    let mut flat_fors_leaves = Vec::with_capacity(total_fors);
    let mut f_off = 256usize;
    for &c_len in &fors_chunks {
        let slice = &fors_opened[f_off..f_off + 256];
        for b in 0..c_len {
            let mut l_val = [0u8; 32];
            for byte_idx in 0..32 {
                let mut v = 0u8;
                for bit in 0..8 {
                    v |= (((slice[8 * byte_idx + bit] >> b) & 1) as u8) << bit;
                }
                l_val[byte_idx] = v;
            }
            flat_fors_leaves.push(l_val);
        }
        f_off += 256;
    }

    let mut fors_openings = Vec::with_capacity(params.fors_trees);
    let mut fors_roots = Vec::with_capacity(params.fors_trees);
    for j in 0..params.fors_trees {
        let tree_leaves = &flat_fors_leaves[j * t_leaves..(j + 1) * t_leaves];
        let (root_j, auth_path) = build_tsw_merkle_root(
            Cshake256Suite,
            &pk.pk_seed,
            0,
            tree0,
            AdrsKind::ForsTree,
            kp0,
            params.fors_height,
            j * t_leaves,
            tree_leaves,
            idxs[j],
        );
        // Verify Merkle path matches `walk_merkle_auth_path`
        let check_root = walk_merkle_auth_path(
            Cshake256Suite,
            &pk.pk_seed,
            0,
            tree0,
            AdrsKind::ForsTree,
            kp0,
            params.fors_height,
            j,
            idxs[j],
            tree_leaves[idxs[j]],
            &auth_path,
        )
        .ok_or(KeccakMpcError::PostVerifyFailed)?;
        if !ct_eq_bytes32(&root_j, &check_root) {
            return Err(KeccakMpcError::PostVerifyFailed);
        }
        fors_roots.push(root_j);
        fors_openings.push(ForsTreeOpening {
            secret_val: rev_secrets[j],
            auth_path,
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
    let mut cur_root = th_tweak_tl(Cshake256Suite, &pk.pk_seed, &fors_pk_adrs, &fors_roots);

    // Evaluate hypertree layers `0..num_layers` with public TSW target-sum grinding (`0` r_rand on internal nodes `[P0-02]`)
    let target_sum = canonical_target_sum(params.w, params.ell1);
    let mut cur_global = leaf_global_idx;
    let mut layer_sigs = Vec::with_capacity(params.num_layers);

    for layer_idx in 0..params.num_layers {
        let kp_idx = cur_global % sub_leaves;
        let tree_idx_nat = cur_global / sub_leaves;
        let tree_idx = tree_idx_nat as u64;
        let layer_u32 = layer_idx as u32;
        let kp_u32 = kp_idx as u32;

        let mut found: Option<(u32, Vec<usize>)> = None;
        for ctr in 0..max_grind {
            let hmsg = th_hash_internal_node(
                Cshake256Suite,
                &pk.pk_seed,
                &pk.pk_root,
                &cur_root,
                layer_u32,
                tree_idx,
                kp_u32,
                ctr,
            );
            if let Some(digs) = extract_base_w_digits_checked(params.w, params.ell1, &hmsg)
                && check_target_sum(params.w, params.ell1, target_sum, &digs)
            {
                found = Some((ctr, digs));
                break;
            }
        }
        let (tsw_ctr, digits) = found.ok_or(KeccakMpcError::GrindExhausted)?;

        let opened_nodes = eval_tsw_wots_subtree_rss(
            params,
            cluster,
            &pk.pk_seed,
            layer_u32,
            tree_idx,
            Some((kp_idx, &digits)),
        )?;
        let wots_chains = opened_nodes[kp_idx * params.ell1..(kp_idx + 1) * params.ell1].to_vec();

        let mut leaves = Vec::with_capacity(sub_leaves);
        for kp in 0..sub_leaves {
            let ep = if kp == kp_idx {
                let mut completed = Vec::with_capacity(params.ell1);
                for ch in 0..params.ell1 {
                    let mut x = wots_chains[ch];
                    for step in digits[ch]..(params.w - 1) {
                        let step_adrs = HashAdrs {
                            layer: layer_u32,
                            tree: tree_idx,
                            kind: AdrsKind::WotsHash,
                            key_pair: kp as u32,
                            chain_idx: ch as u32,
                            hash_step: step as u32,
                        };
                        x = th_chain_f(Cshake256Suite, &pk.pk_seed, &step_adrs, &x);
                    }
                    completed.push(x);
                }
                completed
            } else {
                opened_nodes[kp * params.ell1..(kp + 1) * params.ell1].to_vec()
            };
            let pk_adrs = HashAdrs {
                layer: layer_u32,
                tree: tree_idx,
                kind: AdrsKind::WotsPk,
                key_pair: kp as u32,
                chain_idx: 0,
                hash_step: 0,
            };
            leaves.push(th_tweak_tl(Cshake256Suite, &pk.pk_seed, &pk_adrs, &ep));
        }
        let (next_root, auth_path) = build_tsw_merkle_root(
            Cshake256Suite,
            &pk.pk_seed,
            layer_u32,
            tree_idx,
            AdrsKind::Tree,
            0,
            params.subtree_height,
            0,
            &leaves,
            kp_idx,
        );
        layer_sigs.push(LayerXmssSig {
            tsw_ctr,
            wots_chains,
            auth_path,
        });
        cur_root = next_root;
        cur_global = tree_idx_nat;
    }

    let sig = PqHashSig {
        r_rand,
        msg_tsw_ctr: 0,
        leaf_global_idx,
        fors_openings,
        layer_sigs,
    };
    if !verify_pq_hash_sig(Cshake256Suite, params, pk, msg, &sig) {
        return Err(KeccakMpcError::PostVerifyFailed);
    }
    Ok(sig)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fips205::{
        fips205_prf_msg, slh_keygen_internal, slh_keygen_mpc, slh_sign_mpc, slh_verify,
    };
    use crate::preprocessing::KeccakBitTripleShare64;
    use crate::sponge::keccak::keccak_f1600;
    use crate::tsw_baggy::{PqSecretKey, derive_public_key, sign_hypertree_core};

    #[test]
    fn slh_oracle_binds_profile_and_seed_before_computation() {
        let sid = [0x81; 32];
        let mut rngs = make_rngs3(0x52);
        let (keys, seed) = run_dealerless_rss_dkg_2of3(sid, 16, &mut rngs).unwrap();
        let mut cluster = RssSlhMpcCluster::new(sid, keys, rngs).unwrap();
        cluster.bind_slh_params(&Fips205Params::SLH_DSA_SHAKE_128F, &seed[..16]).unwrap();
        assert!(cluster.bind_slh_params(&Fips205Params::SLH_DSA_SHAKE_128S, &seed[..16]).is_err());
        let mut wrong = seed; wrong[0] ^= 1;
        assert!(cluster.bind_slh_params(&Fips205Params::SLH_DSA_SHAKE_128F, &wrong[..16]).is_err());
        let wrong_pk = crate::fips205::SlhPublicKey::new(&wrong[..16], &[0; 16]).unwrap();
        assert!(slh_sign_mpc(&Fips205Params::SLH_DSA_SHAKE_128F, &mut cluster,
            b"message", b"", &wrong_pk, None).is_err());
        assert_eq!(cluster.lane_permutations(), 0);
    }

    #[test]
    fn rss_partial_prf_and_masked_f_match_fips_and_reject_bad_replica() {
        let sid = [0x44; 32];
        let mut rngs = make_rngs3(0x23);
        let (keys, _) = run_dealerless_rss_dkg_2of3(sid, 16, &mut rngs).unwrap();
        let seed: [u8; 16] = core::array::from_fn(|i| {
            keys[0].sk_seed_primary[i] ^ keys[1].sk_seed_primary[i] ^ keys[2].sk_seed_primary[i]
        });
        let pk_seed = keys[0].pk_seed[..16].to_vec();
        let mut cluster = RssSlhMpcCluster::new(sid, keys, rngs).unwrap();
        let adrs: [Fips205Adrs; 3] = core::array::from_fn(|i| {
            let mut a = Fips205Adrs::ZERO;
            a.adrs_type = Fips205AdrsType::WotsPrf;
            a.f5 = i as u32;
            a
        });
        let (mut p, mut s) = cluster.eval_prf_batch64_secret(&pk_seed, &adrs).unwrap();
        let step = adrs.map(|mut a| {
            a.adrs_type = Fips205AdrsType::WotsHash;
            a
        });
        cluster
            .eval_f_step_masked_batch64(&pk_seed, &step, 0b101, &mut p, &mut s)
            .unwrap();
        let (opened, _) = cluster
            .verify_and_open_cut_blocks("rss_partial_regression", 3, &p, &s)
            .unwrap();
        for i in 0..3 {
            let prf = crate::fips205::fips205_prf(16, &pk_seed, &seed, &adrs[i]);
            let expected = if i == 1 {
                prf
            } else {
                crate::fips205::fips205_f(16, &pk_seed, &step[i], &prf)
            };
            assert_eq!(opened[i], expected);
        }
        cluster.keys[0].sk_seed_secondary[0] ^= 1;
        assert!(matches!(
            cluster.eval_prf_batch64_secret(&pk_seed, &adrs),
            Err(KeccakMpcError::RssShareEqualityFailed(_))
        ));
        assert!(cluster.is_poisoned());
    }

    fn cut_of(p: &[[u64; 256]; 3], s: &[[u64; 256]; 3], words: usize) -> RssCutBuffer {
        let mut cut = RssCutBuffer::new();
        for party in 0..3 {
            cut.prim[party].extend_from_slice(&p[party][..words]);
            cut.sec[party].extend_from_slice(&s[party][..words]);
        }
        cut
    }

    /// Every evaluation, verification and opening entry point refuses a poisoned cluster
    /// and leaves its counters where they were.
    fn assert_rss_cluster_dead(
        cluster: &mut RssSlhMpcCluster,
        pk_seed: &[u8],
        adrs: &[Fips205Adrs],
        p: &[[u64; 256]; 3],
        s: &[[u64; 256]; 3],
    ) {
        assert!(cluster.is_poisoned());
        let before = (cluster.batch_ctr, cluster.lane_permutations());
        let cut = cut_of(p, s, 128);
        // A second barrier finds no pending relations; it must not pass.
        assert!(matches!(
            cluster.flush_verify_and_open_cut("latch_again", &cut),
            Err(KeccakMpcError::Poisoned)
        ));
        assert!(matches!(
            cluster.verify_and_open_cut_blocks("latch_open", adrs.len(), p, s),
            Err(KeccakMpcError::Poisoned)
        ));
        assert!(matches!(
            cluster.eval_prf_batch64_secret(pk_seed, adrs),
            Err(KeccakMpcError::Poisoned)
        ));
        let (mut cp, mut cs) = (*p, *s);
        assert_eq!(
            cluster.eval_f_step_masked_batch64(pk_seed, adrs, 0b11, &mut cp, &mut cs),
            Err(KeccakMpcError::Poisoned)
        );
        assert_eq!((cp, cs), ([[0u64; 256]; 3], [[0u64; 256]; 3]));
        let mut st_p = SecretBuffer([[0u64; 1600]; 3]);
        let mut st_s = SecretBuffer([[0u64; 1600]; 3]);
        assert_eq!(
            cluster.permute_batch64(1, &mut st_p, &mut st_s),
            Err(KeccakMpcError::Poisoned)
        );
        assert!(matches!(
            cluster.prf_msg_shared(16, &[0u8; 16], b"m"),
            Err(KeccakMpcError::Poisoned)
        ));
        assert_eq!(
            cluster.eval_prf_msg_mpc(16, &[0u8; 16], b"m").unwrap_err(),
            Fips205Error::MpcActiveTamperDetected
        );
        let p128f = Fips205Params::SLH_DSA_SHAKE_128F;
        assert_eq!(
            cluster.eval_wots_pkgen_subtree_mpc(&p128f, pk_seed, 0, 0).unwrap_err(),
            Fips205Error::MpcActiveTamperDetected
        );
        assert_eq!(
            cluster
                .eval_fors_trees_mpc(&p128f, pk_seed, Fips205Adrs::ZERO, &vec![0u32; p128f.k])
                .unwrap_err(),
            Fips205Error::MpcActiveTamperDetected
        );
        assert_eq!((cluster.batch_ctr, cluster.lane_permutations()), before);
        assert!(cluster.is_poisoned());
    }

    #[test]
    fn rss_cluster_latches_a_failed_check_and_refuses_every_later_check_and_opening() {
        let prf_adrs: [Fips205Adrs; 2] = core::array::from_fn(|i| {
            let mut a = Fips205Adrs::ZERO;
            a.adrs_type = Fips205AdrsType::WotsPrf;
            a.f5 = i as u32;
            a
        });
        let fresh = |tag: u8| {
            let sid = [tag; 32];
            let mut rngs = make_rngs3(tag);
            let (keys, _) = run_dealerless_rss_dkg_2of3(sid, 16, &mut rngs).unwrap();
            let pk_seed = keys[0].pk_seed[..16].to_vec();
            (RssSlhMpcCluster::new(sid, keys, rngs).unwrap(), pk_seed)
        };

        // 1. A false AND relation is pending when the barrier runs: the check fails, and a
        //    second check on the now empty relation set must not open the cut.
        let (mut cluster, pk_seed) = fresh(0x61);
        let (p, s) = cluster.eval_prf_batch64_secret(&pk_seed, &prf_adrs).unwrap();
        assert!(!cluster.is_poisoned());
        let mut bad = random_relations(b"latch", 3, u64::MAX);
        bad.c[1][2] ^= 1 << 17;
        for slot in 0..3 {
            cluster.pending_dzk.a[slot].extend_from_slice(&bad.a[slot]);
            cluster.pending_dzk.b[slot].extend_from_slice(&bad.b[slot]);
            cluster.pending_dzk.c[slot].extend_from_slice(&bad.c[slot]);
        }
        let cut = cut_of(&p, &s, 128);
        assert!(matches!(
            cluster.flush_verify_and_open_cut("latch", &cut),
            Err(KeccakMpcError::RssSacrificeFailed)
        ));
        assert_eq!(cluster.pending_dzk.len_words(), 0);
        assert_rss_cluster_dead(&mut cluster, &pk_seed, &prf_adrs, &p, &s);

        // 2. A holder pair whose mask streams disagree: the fault is caught inside the
        //    evaluation, and the cluster is dead from then on.
        let (mut cluster, pk_seed) = fresh(0x64);
        let (p, s) = cluster.eval_prf_batch64_secret(&pk_seed, &prf_adrs).unwrap();
        cluster.mask_session.sec[2][0] ^= 1;
        cluster.mask_session.shared = false;
        let err = cluster.eval_prf_batch64_secret(&pk_seed, &prf_adrs).unwrap_err();
        assert!(matches!(
            err,
            KeccakMpcError::RssSacrificeFailed | KeccakMpcError::RssShareEqualityFailed(_)
        ));
        assert_rss_cluster_dead(&mut cluster, &pk_seed, &prf_adrs, &p, &s);

        // 3. An inconsistent replica in the opening itself.
        let (mut cluster, pk_seed) = fresh(0x67);
        let (p, mut s) = cluster.eval_prf_batch64_secret(&pk_seed, &prf_adrs).unwrap();
        s[1][3] ^= 1;
        assert!(matches!(
            cluster.verify_and_open_cut_blocks("latch_replica", 2, &p, &s),
            Err(KeccakMpcError::RssShareEqualityFailed(_))
        ));
        s[1][3] ^= 1;
        assert_rss_cluster_dead(&mut cluster, &pk_seed, &prf_adrs, &p, &s);

        // 4. A cluster poisoned by an engine built on its parts.
        let (mut cluster, pk_seed) = fresh(0x6a);
        let (p, s) = cluster.eval_prf_batch64_secret(&pk_seed, &prf_adrs).unwrap();
        cluster.poison();
        assert_rss_cluster_dead(&mut cluster, &pk_seed, &prf_adrs, &p, &s);
    }

    #[test]
    fn rss_relation_accumulator_never_verifies_again_after_a_failure() {
        let sid = [0x9b; 32];
        let mut rngs = make_rngs3(0x6d);
        let (keys, _) = run_dealerless_rss_dkg_2of3(sid, 16, &mut rngs).unwrap();
        let mask = RssMaskSession::derive(&sid, &keys, &mut rngs).unwrap();
        let mut pending = random_relations(b"acc", 5, u64::MAX);
        pending.c[0][4] ^= 1;
        assert!(!pending.is_poisoned());
        assert_eq!(
            verify_rss_boolean_triples_seeded(&sid, 0, &mut pending, &mask, &mut rngs, None),
            Err(KeccakMpcError::RssSacrificeFailed)
        );
        assert!(pending.is_poisoned());
        assert_eq!(pending.len_words(), 0);
        // Empty accumulator, same or new counter, with or without a caller seed.
        for (ctr, seed) in [(0u64, None), (1, None), (2, Some(&[9u8; 32]))] {
            assert_eq!(
                verify_rss_boolean_triples_seeded(&sid, ctr, &mut pending, &mask, &mut rngs, seed),
                Err(KeccakMpcError::Poisoned)
            );
        }
        // Honest relations recorded afterwards do not revive it.
        let honest = random_relations(b"acc2", 4, u64::MAX);
        for slot in 0..3 {
            pending.a[slot].extend_from_slice(&honest.a[slot]);
            pending.b[slot].extend_from_slice(&honest.b[slot]);
            pending.c[slot].extend_from_slice(&honest.c[slot]);
        }
        assert_eq!(
            verify_rss_boolean_triples_seeded(&sid, 3, &mut pending, &mask, &mut rngs, None),
            Err(KeccakMpcError::Poisoned)
        );
        assert_eq!(pending.len_words(), 0);
        let mut prim = [[0u64; 1600]; 3];
        let mut sec = [[0u64; 1600]; 3];
        assert_eq!(
            eval_rss_keccak_f1600_batch64_record(&sid, 4, 1, &mut prim, &mut sec, &mask, &mut pending),
            Err(KeccakMpcError::Poisoned)
        );
        assert_eq!(pending.len_words(), 0);
    }

    #[test]
    fn rss_tensor_partition_preserves_every_sum() {
        let groups = 131;
        let mut pending = RssPendingDzkTriples::new();
        let mut rng = PartyPrivateRng::from_seed([0x98; 32], b"rss-tensor-partition");
        for slot in 0..3 {
            pending.a[slot] = (0..groups * RSS_DZK_GROUP_WORDS).map(|_| rng.next_u64()).collect();
            pending.b[slot] = (0..groups * RSS_DZK_GROUP_WORDS).map(|_| rng.next_u64()).collect();
        }
        let weights: Vec<_> = (0..groups).map(|_| [rng.next_u128(), rng.next_u128()]).collect();
        let reference = rss_dzk_tensor_tables_range(&pending, 0, &weights);
        assert_eq!(rss_dzk_tensor_tables(&pending, groups, &weights), reference);
        let mut partitioned = rss_dzk_tensor_tables_range(&pending, 0, &weights[..63]);
        let tail = rss_dzk_tensor_tables_range(&pending, 63, &weights[63..]);
        for (dst, src) in partitioned.iter_mut().zip(tail) {
            for (dst, src) in dst.iter_mut().zip(src) {
                dst[0] ^= src[0]; dst[1] ^= src[1];
            }
        }
        assert_eq!(partitioned, reference);
    }

    #[test]
    fn rss_batched_poly_dot_matches_two_lane_reference() {
        let mut rng = PartyPrivateRng::from_seed([0x97; 32], b"rss-dot-parity");
        for len in [0, 1, 15, 16, 17, 255, 256, 257, 1024] {
            let lhs: Vec<_> = (0..len).map(|_| [rng.next_u128(), rng.next_u128()]).collect();
            let rhs: Vec<_> = (0..len).map(|_| [rng.next_u128(), rng.next_u128()]).collect();
            assert_eq!(rss_poly_dot(&lhs, &rhs),
                qsag_asm::tower128_bdoz_2lane_poly_mac(&lhs, &rhs));
        }
    }

    #[test]
    fn rss_proof_field_matches_polynomial_reference_on_every_basis_product() {
        let mut xof = Cshake256Xof::new(b"RSS.FIELD.REGRESSION");
        let mut bytes = [0u8; 32];
        for _ in 0..256 {
            xof.squeeze(&mut bytes);
            let a = u128::from_le_bytes(bytes[..16].try_into().unwrap());
            let b = u128::from_le_bytes(bytes[16..].try_into().unwrap());
            assert_eq!(
                RssProofField(a).mul(RssProofField(b)).0,
                qsag_asm::portable::poly128_mul_const(a, b)
            );
        }
        assert_eq!(
            RssProofField(u128::MAX).mul(RssProofField(u128::MAX)).0,
            qsag_asm::portable::poly128_mul_const(u128::MAX, u128::MAX)
        );
        for i in 0..128 {
            for j in 0..128 {
                let a = 1u128 << i;
                let b = 1u128 << j;
                assert_eq!(
                    RssProofField(a).mul(RssProofField(b)).0,
                    qsag_asm::portable::poly128_mul_const(a, b)
                );
            }
        }
        assert_ne!(RssProofField(1 << 127).mul(RssProofField(2)).0, 0);
    }

    /// Random consistent relation words: slot shares of `a`, `b` and of `c = a & b`.
    fn random_relations(tag: &[u8], words: usize, active: u64) -> RssPendingDzkTriples {
        let mut xof = Cshake256Xof::new(b"RSS.RELATION.FIXTURE");
        xof.absorb(tag);
        let mut next = || {
            let mut bytes = [0u8; 8];
            xof.squeeze(&mut bytes);
            u64::from_le_bytes(bytes) & active
        };
        let mut pending = RssPendingDzkTriples::new();
        for _ in 0..words {
            let a: [u64; 3] = core::array::from_fn(|_| next());
            let b: [u64; 3] = core::array::from_fn(|_| next());
            let c0 = next();
            let c1 = next();
            let c2 = ((a[0] ^ a[1] ^ a[2]) & (b[0] ^ b[1] ^ b[2])) ^ c0 ^ c1;
            for (s, c) in [c0, c1, c2].into_iter().enumerate() {
                pending.a[s].push(a[s]);
                pending.b[s].push(b[s]);
                pending.c[s].push(c);
            }
        }
        pending
    }

    fn clone_relations(src: &RssPendingDzkTriples) -> RssPendingDzkTriples {
        RssPendingDzkTriples {
            a: src.a.clone(),
            b: src.b.clone(),
            c: src.c.clone(),
            lane_perms: src.lane_perms,
            poison: RssPoisonLatch::new(),
        }
    }

    #[test]
    fn rss_proof_helpers_match_bit_references() {
        let mut xof = Cshake256Xof::new(b"RSS.HELPER.REGRESSION");
        let mut word = || {
            let mut bytes = [0u8; 8];
            xof.squeeze(&mut bytes);
            u64::from_le_bytes(bytes)
        };
        // Transpose.
        let rows: [u64; 64] = core::array::from_fn(|_| word());
        let mut t = rows;
        rss_transpose64(&mut t);
        for (i, row) in rows.iter().enumerate() {
            for (j, col) in t.iter().enumerate() {
                assert_eq!((col >> i) & 1, (row >> j) & 1);
            }
        }
        // Ternary expansion: digit 0/1 selects a half, digit 2 is the XOR of both.
        let src: [u64; RSS_DZK_GROUP_WORDS] = core::array::from_fn(|_| word());
        let mut cur = [0u64; RSS_DZK_TERNARY];
        rss_ternary_expand(&src, &mut cur);
        for (e, got) in cur.iter().enumerate() {
            let mut expected = 0u64;
            for (u, value) in src.iter().enumerate() {
                let mut digits = e;
                let mut included = true;
                for l in 0..RSS_DZK_TENSOR_BITS {
                    let digit = digits % 3;
                    digits /= 3;
                    included &= digit == 2 || digit == (u >> l) & 1;
                }
                if included {
                    expected ^= value;
                }
            }
            assert_eq!(*got, expected, "point {e}");
        }
        // Group binding against per-bit accumulation.
        let beta: [u128; RSS_DZK_GROUP_WORDS] = core::array::from_fn(|_| u128::from(word()) | (u128::from(word()) << 64));
        let mut pattern = [[0u8; RSS_DZK_NIBBLES]; 128];
        for (bit, nibbles) in pattern.iter_mut().enumerate() {
            for g in 0..RSS_DZK_NIBBLES {
                for d in 0..4 {
                    nibbles[g] |= (((beta[4 * g + d] >> bit) & 1) as u8) << d;
                }
            }
        }
        let mut planes = [[0u64; 64]; 2];
        let mut out = [0u128; 64];
        rss_bind_group(&src, &pattern, &mut planes, &mut out);
        for (lane, got) in out.iter().enumerate() {
            let mut expected = 0u128;
            for (word, weight) in src.iter().zip(&beta) {
                if (word >> lane) & 1 == 1 {
                    expected ^= weight;
                }
            }
            assert_eq!(*got, expected);
        }
        // Monomial multiplication and public inversion.
        let v = RssProofField(u128::from(word()) | (u128::from(word()) << 64));
        for shift in 0..64u32 {
            let mut mono = RssProofField::ONE;
            for _ in 0..shift {
                mono = mono.mul(RssProofField(2));
            }
            assert_eq!(v.mul_t_pow(shift).0, v.mul(mono).0);
        }
        assert_eq!(v.mul(v.inv_public()).0, 1);
    }

    #[test]
    fn rss_proof_accepts_honest_and_rejects_every_bit_position_and_operand() {
        let sid = [0x97; 32];
        let mut rngs = make_rngs3(0x39);
        let (keys, _) = run_dealerless_rss_dkg_2of3(sid, 16, &mut rngs).unwrap();
        let mask = RssMaskSession::derive(&sid, &keys, &mut rngs).unwrap();
        let mut ctr = 0u64;
        // Word counts cover one partial group, exact groups, and a non-power-of-two group count.
        for (words, active) in [(1usize, 1u64), (3, 0x7f), (64, u64::MAX), (130, u64::MAX), (321, u64::MAX >> 1)] {
            let honest = random_relations(&[words as u8], words, active);
            let mut pending = clone_relations(&honest);
            verify_rss_boolean_triples_bbcggi19(&sid, ctr, &mut pending, &mask, &mut rngs).unwrap();
            assert_eq!(pending.len_words(), 0);
            ctr += 1;
            for bit in 0..64usize {
                // Rotate the corrupted word, slot and operand with the bit position.
                let word = (bit * 37 + words / 2) % words;
                let slot = bit % 3;
                let mut bad = clone_relations(&honest);
                match (bit / 3) % 3 {
                    0 => bad.c[slot][word] ^= 1u64 << bit,
                    1 => {
                        // Flipping `a` breaks the relation exactly where `b` is set.
                        bad.a[slot][word] ^= 1u64 << bit;
                        for (s, row) in bad.b.iter_mut().enumerate() {
                            row[word] |= u64::from(s == 0) << bit;
                            row[word] &= !(u64::from(s != 0) << bit);
                        }
                        let a_bit = ((bad.a[0][word] ^ bad.a[1][word] ^ bad.a[2][word]) >> bit) & 1;
                        let c_bit = ((bad.c[0][word] ^ bad.c[1][word] ^ bad.c[2][word]) >> bit) & 1;
                        if a_bit == c_bit {
                            bad.c[slot][word] ^= 1u64 << bit;
                        }
                    }
                    _ => {
                        bad.b[slot][word] ^= 1u64 << bit;
                        for (s, row) in bad.a.iter_mut().enumerate() {
                            row[word] |= u64::from(s == 0) << bit;
                            row[word] &= !(u64::from(s != 0) << bit);
                        }
                        let b_bit = ((bad.b[0][word] ^ bad.b[1][word] ^ bad.b[2][word]) >> bit) & 1;
                        let c_bit = ((bad.c[0][word] ^ bad.c[1][word] ^ bad.c[2][word]) >> bit) & 1;
                        if b_bit == c_bit {
                            bad.c[slot][word] ^= 1u64 << bit;
                        }
                    }
                }
                let x = |v: &[Vec<u64>; 3]| ((v[0][word] ^ v[1][word] ^ v[2][word]) >> bit) & 1;
                assert_ne!(x(&bad.a) & x(&bad.b), x(&bad.c), "fixture must be a false relation");
                assert!(matches!(
                    verify_rss_boolean_triples_bbcggi19(&sid, ctr, &mut bad, &mask, &mut rngs),
                    Err(KeccakMpcError::RssSacrificeFailed)
                ));
                assert_eq!(bad.len_words(), 0);
                ctr += 1;
            }
        }
    }

    #[test]
    fn rss_keccak_proof_rejects_a_flipped_product_in_every_round_and_bit_position() {
        let sid = [0x95; 32];
        let mut rngs = make_rngs3(0x3b);
        let (keys, _) = run_dealerless_rss_dkg_2of3(sid, 16, &mut rngs).unwrap();
        let mask = RssMaskSession::derive(&sid, &keys, &mut rngs).unwrap();
        let mut prim = [[0u64; 1600]; 3];
        for (s, share) in prim.iter_mut().enumerate() {
            for (idx, word) in share.iter_mut().enumerate() {
                *word = (idx as u64 + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15 ^ (s as u64) << 7);
            }
        }
        let mut sec = [prim[1], prim[2], prim[0]];
        let mut honest = RssPendingDzkTriples::new();
        eval_rss_keccak_f1600_batch64_record(&sid, 0, 64, &mut prim, &mut sec, &mask, &mut honest)
            .unwrap();
        assert_eq!(honest.len_words(), 24 * 1600);
        let mut pending = clone_relations(&honest);
        verify_rss_boolean_triples_bbcggi19(&sid, 0, &mut pending, &mask, &mut rngs).unwrap();
        // Cover every round and every bit with 64 probes. The primitive proof
        // test above separately exhausts operand/bit combinations; repeating a
        // complete Keccak proof for their Cartesian product adds no new branch.
        for (ctr, bit) in (1u64..).zip(0..64usize) {
                let round = bit % 24;
                // A different state position for every (round, bit) pair.
                let word = round * 1600 + (bit * 25 + round * 67) % 1600;
                let mut bad = clone_relations(&honest);
                bad.c[(round + bit) % 3][word] ^= 1u64 << bit;
                assert!(matches!(
                    verify_rss_boolean_triples_bbcggi19(&sid, ctr, &mut bad, &mask, &mut rngs),
                    Err(KeccakMpcError::RssSacrificeFailed)
                ));
        }
    }

    #[test]
    fn rss_mask_session_is_hedged_by_party_entropy_and_bound_to_shares() {
        let sid = [0x93; 32];
        let mut rngs = make_rngs3(0x3d);
        let (mut keys, _) = run_dealerless_rss_dkg_2of3(sid, 16, &mut rngs).unwrap();
        let first = RssMaskSession::derive(&sid, &keys, &mut rngs).unwrap();
        assert!(first.shared);
        let mut fork_a = RssMaskSession { prim: first.prim, sec: first.sec, shared: first.shared };
        let mut fork_b = RssMaskSession { prim: first.prim, sec: first.sec, shared: first.shared };
        fork_a.hedge_transcript(b"same session/message one");
        fork_b.hedge_transcript(b"same session/message two");
        assert_ne!(fork_a.prim, fork_b.prim);
        for p in 0..3 { assert_eq!(fork_a.prim[p], fork_a.sec[(p + 2) % 3]); }
        // Same session identifier and keys, fresh party entropy: every stream key changes.
        let second = RssMaskSession::derive(&sid, &keys, &mut rngs).unwrap();
        for p in 0..3 {
            assert_ne!(first.prim[p], second.prim[p]);
            assert_eq!(second.sec[p], second.prim[(p + 1) % 3]);
            for q in 0..3 {
                assert!(p == q || second.prim[p] != second.prim[q]);
            }
        }
        // One party repeating its entropy is not enough to repeat the joint coin.
        let mut replay_a = make_rngs3(0x50);
        let mut replay_b = make_rngs3(0x50);
        replay_b[1] = PartyPrivateRng::from_seed([0x99; 32], b"rss-test");
        let a = RssMaskSession::derive(&sid, &keys, &mut replay_a).unwrap();
        let b = RssMaskSession::derive(&sid, &keys, &mut replay_b).unwrap();
        assert_ne!(a.prim, b.prim);
        // Identical entropy but a different replicated secret share: the slot key changes.
        let mut replay_c = make_rngs3(0x50);
        keys[0].sk_seed_primary[0] ^= 1;
        keys[2].sk_seed_secondary[0] ^= 1;
        let c = RssMaskSession::derive(&sid, &keys, &mut replay_c).unwrap();
        assert!(c.shared);
        assert_ne!(a.prim[0], c.prim[0]);
        assert_eq!(a.prim[1], c.prim[1]);
        // A holder pair that disagrees is detected and loses the shared-stream path.
        keys[1].sk_prf_secondary[3] ^= 0x10;
        let mut replay_d = make_rngs3(0x50);
        assert!(!RssMaskSession::derive(&sid, &keys, &mut replay_d).unwrap().shared);
    }

    #[test]
    fn rss_batch_rejects_invalid_lengths_and_inconsistent_replicas_without_mutation() {
        let sid = [0x98; 32];
        let mut rngs = make_rngs3(0x41);
        let (keys, _) = run_dealerless_rss_dkg_2of3(sid, 16, &mut rngs).unwrap();
        let mut primary = [[7u64; 1600]; 3];
        let mut secondary = primary;
        for len in [0, 65, usize::MAX] {
            assert!(matches!(
                eval_rss_keccak_f1600_batch64(
                    &sid,
                    0,
                    len,
                    &mut primary,
                    &mut secondary,
                    &keys,
                    &mut rngs
                ),
                Err(KeccakMpcError::InvalidBatchSize(_))
            ));
            assert_eq!(primary, [[7; 1600]; 3]);
        }
        secondary[0][0] ^= 1;
        assert!(matches!(
            eval_rss_keccak_f1600_batch64(
                &sid,
                0,
                1,
                &mut primary,
                &mut secondary,
                &keys,
                &mut rngs
            ),
            Err(KeccakMpcError::RssShareEqualityFailed(_))
        ));
        assert_eq!(primary, [[7; 1600]; 3]);
    }

    #[test]
    fn rss_chi_rejects_mismatched_pairwise_mask_seed() {
        let sid = [0x91; 32];
        let mut rngs = make_rngs3(0x42);
        let (mut keys, _) = run_dealerless_rss_dkg_2of3(sid, 16, &mut rngs).unwrap();
        keys[0].prg_seed_secondary[0] ^= 1;
        let mut primary = [[1u64; 1600]; 3];
        let mut secondary = primary;
        assert!(
            eval_rss_keccak_f1600_batch64(
                &sid,
                0,
                1,
                &mut primary,
                &mut secondary,
                &keys,
                &mut rngs
            )
            .is_err()
        );
        // The permutation ran, its proof failed: no unverified output share is handed back.
        assert_eq!(primary, [[0u64; 1600]; 3]);
        assert_eq!(secondary, [[0u64; 1600]; 3]);
    }

    fn make_rngs3(tag: u8) -> [PartyPrivateRng; 3] {
        core::array::from_fn(|p| {
            PartyPrivateRng::from_seed([tag.wrapping_add(p as u8); 32], b"rss-test")
        })
    }

    #[test]
    fn test_batch_active_mask_zero_shift_overflow_and_rss_64way_keccak_parity() {
        assert_eq!(batch_active_mask(0), 0);
        assert_eq!(batch_active_mask(1), 1);
        assert_eq!(batch_active_mask(63), (1u64 << 63) - 1);
        assert_eq!(batch_active_mask(64), u64::MAX);

        let sid = [0x33; 32];
        let mut rngs = make_rngs3(0x10);
        let (keys, _) = run_dealerless_rss_dkg_2of3(sid, 16, &mut rngs).unwrap();

        // Check all 64 parallel Keccak-f[1600] instances against native `keccak_f1600`!
        let mut ref_states = [[0u64; 25]; 64];
        let mut st_p = SecretBuffer([[0u64; 1600]; 3]);
        let mut st_s = SecretBuffer([[0u64; 1600]; 3]);
        let mut inst = 0;
        while inst < 64 {
            for lane in 0..25 {
                let w = ((inst as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15))
                    .wrapping_add(lane as u64 * 17);
                ref_states[inst][lane] = w;
                let s0 = rngs[0].next_u64() & (1u64 << inst);
                let s1 = rngs[1].next_u64() & (1u64 << inst);
                for z in 0..64 {
                    let bit = ((w >> z) & 1) << inst;
                    let s2 = bit ^ s0 ^ s1;
                    st_p[0][lane * 64 + z] |= s0;
                    st_s[0][lane * 64 + z] |= s1;
                    st_p[1][lane * 64 + z] |= s1;
                    st_s[1][lane * 64 + z] |= s2;
                    st_p[2][lane * 64 + z] |= s2;
                    st_s[2][lane * 64 + z] |= s0;
                }
            }
            keccak_f1600(&mut ref_states[inst]);
            inst += 1;
        }

        eval_rss_keccak_f1600_batch64(&sid, 0, 64, &mut st_p, &mut st_s, &keys, &mut rngs).unwrap();

        let mut inst = 0;
        while inst < 64 {
            for lane in 0..25 {
                let mut got = 0u64;
                for z in 0..64 {
                    let b = ((st_p[0][lane * 64 + z]
                        ^ st_p[1][lane * 64 + z]
                        ^ st_p[2][lane * 64 + z])
                        >> inst)
                        & 1;
                    got |= b << z;
                }
                assert_eq!(got, ref_states[inst][lane]);
            }
            inst += 1;
        }

        // Active RSS share lie MUST emit `RssSlashingReceipt` with probability 1!
        let mut bad_sec = [vec![st_s[0][0]], vec![st_s[1][0]], vec![st_s[2][0] ^ 1]];
        let prim = [vec![st_p[0][0]], vec![st_p[1][0]], vec![st_p[2][0]]];
        let latch = RssPoisonLatch::new();
        assert_eq!(
            rss_commit_and_open_u64_batch(&sid, "tamper", &prim, &bad_sec, &mut rngs, &latch)
                .unwrap_err(),
            KeccakMpcError::RssShareEqualityFailed(RssSlashingReceipt {
                share_slot: 0,
                primary_party: 0,
                secondary_party: 2,
            })
        );
        assert!(latch.is_set());
        bad_sec[2][0] ^= 1;
        let latch = RssPoisonLatch::new();
        rss_commit_and_open_u64_batch(&sid, "honest", &prim, &bad_sec, &mut rngs, &latch).unwrap();
        assert!(!latch.is_set());
    }

    #[test]
    #[ignore = "Full FIPS 205 production-height MPC soak; compact multilayer signatures and FIPS KATs run by default"]
    fn test_rss_slh_dsa_mpc_128f_exact_kat_parity_and_distributed_tsw() {
        let sid = [0x51; 32];
        let mut rngs = make_rngs3(0x20);
        let (keys, _) = run_dealerless_rss_dkg_2of3(sid, 16, &mut rngs).unwrap();

        // Verify distributed `SLH-DSA-SHAKE-128f` (`17,088 B` official NIST parameter set!)
        let sk_seed: [u8; 16] = core::array::from_fn(|b| {
            keys[0].sk_seed_primary[b] ^ keys[1].sk_seed_primary[b] ^ keys[2].sk_seed_primary[b]
        });
        let sk_prf: [u8; 16] = core::array::from_fn(|b| {
            keys[0].sk_prf_primary[b] ^ keys[1].sk_prf_primary[b] ^ keys[2].sk_prf_primary[b]
        });
        let pk_seed_16 = &keys[0].pk_seed[..16].to_vec();
        let p128f = Fips205Params::SLH_DSA_SHAKE_128F;
        let (ref_sk, ref_pk) = slh_keygen_internal(&p128f, &sk_seed, &sk_prf, pk_seed_16).unwrap();

        let mut cluster = RssSlhMpcCluster::new(sid, keys, rngs).unwrap();
        let mpc_pk = slh_keygen_mpc(&p128f, &mut cluster, pk_seed_16).unwrap();
        assert_eq!(mpc_pk, ref_pk);

        let msg = b"distributed-threshold-slh-dsa-128f";
        let ctx = b"qsag-mpc-ctx";
        let mpc_sig = slh_sign_mpc(&p128f, &mut cluster, msg, ctx, &mpc_pk, None).unwrap();
        let ref_sig = crate::fips205::slh_sign(&p128f, msg, ctx, &ref_sk, None).unwrap();
        assert_eq!(mpc_sig.len(), 17_088);
        // Deterministic (`addrnd = None`) MPC signature MUST be 100% BIT-FOR-BIT IDENTICAL to FIPS 205!
        assert_eq!(mpc_sig, ref_sig);
        assert!(slh_verify(&p128f, msg, &mpc_sig, ctx, &mpc_pk));

        // Also test distributed `DkgCachedSubtrees::build_distributed_rss` + `sign_stateless_tsw_rss_mpc`
        let mut rngs32 = make_rngs3(0x40);
        let (keys32, _) = run_dealerless_rss_dkg_2of3([0x52; 32], 32, &mut rngs32).unwrap();
        // Reference-only reconstruction of the test fixture; the cluster keeps its shares.
        let xor3 = |pick: fn(&RssKeyShare256) -> [u8; 32]| -> [u8; 32] {
            let parts = [pick(&keys32[0]), pick(&keys32[1]), pick(&keys32[2])];
            core::array::from_fn(|b| parts[0][b] ^ parts[1][b] ^ parts[2][b])
        };
        let tsw_sk = PqSecretKey {
            sk_seed: xor3(|k| k.sk_seed_primary),
            sk_prf: xor3(|k| k.sk_prf_primary),
            pk_seed: keys32[0].pk_seed,
        };
        let mut cluster32 = RssSlhMpcCluster::new([0x52; 32], keys32, rngs32).unwrap();
        let tsw_params = PqHashParams::COMPACT_GOLDEN;
        let cached =
            DkgCachedSubtrees::build_distributed_rss(&tsw_params, &mut cluster32, 64).unwrap();
        // The distributed public key is the reference key of the same seeds.
        assert_eq!(
            cached.pk,
            derive_public_key(Cshake256Suite, &tsw_params, &tsw_sk)
        );
        let tsw_msg = b"distributed-corduroy-msg";
        let tsw_sig =
            sign_stateless_tsw_rss_mpc(&tsw_params, &mut cluster32, &cached.pk, tsw_msg, 100_000)
                .unwrap();
        assert!(verify_pq_hash_sig(
            Cshake256Suite,
            &tsw_params,
            &cached.pk,
            tsw_msg,
            &tsw_sig
        ));
        // Given the same randomizer, the distributed signature equals the reference signature
        // in every FORS opening, WOTS chain value, grind counter and authentication path.
        let mu = th_pre_hash(Cshake256Suite, &cached.pk.pk_seed, &cached.pk.pk_root, tsw_msg);
        let (leaf, fors_idxs) = derive_stateless_leaf_and_fors_indices(
            Cshake256Suite,
            &tsw_params,
            &tsw_sig.r_rand,
            &cached.pk.pk_seed,
            &cached.pk.pk_root,
            &mu,
        )
        .unwrap();
        let reference_sig = sign_hypertree_core(
            Cshake256Suite,
            &tsw_params,
            &tsw_sk,
            &cached.pk,
            &mu,
            tsw_sig.r_rand,
            leaf,
            Some(&fors_idxs),
            100_000,
        )
        .unwrap();
        assert_eq!(tsw_sig, reference_sig);
        let mut forged = tsw_sig;
        forged.layer_sigs[0].wots_chains[0][0] ^= 1;
        assert!(!verify_pq_hash_sig(
            Cshake256Suite,
            &tsw_params,
            &cached.pk,
            tsw_msg,
            &forged
        ));
    }

    #[test]
    fn tsw_rss_signer_randomizer_is_deterministic_and_bound_to_the_generated_key() {
        // Smallest well-formed stateless profile: 2 layers of 2 leaves, 2 FORS trees of 2 leaves.
        let params = PqHashParams {
            w: 4,
            ell1: 128,
            subtree_height: 1,
            num_layers: 2,
            fors_trees: 2,
            fors_height: 1,
            max_sigs_log2: 2,
            stateful: false,
        };
        assert!(params.is_well_formed());
        let mut dkg_rngs = make_rngs3(0x71);
        let (keys, _) = run_dealerless_rss_dkg_2of3([0x71; 32], 32, &mut dkg_rngs).unwrap();
        let sk_prf: [u8; 32] = core::array::from_fn(|b| {
            keys[0].sk_prf_primary[b] ^ keys[1].sk_prf_primary[b] ^ keys[2].sk_prf_primary[b]
        });
        let msg = b"one message, two sessions";
        let untouched = |c: &RssSlhMpcCluster| (c.batch_ctr, c.lane_permutations());

        // Shares that were never bound to a public key sign nothing.
        let mut first = RssSlhMpcCluster::new([0xa1; 32], keys, make_rngs3(0x81)).unwrap();
        let before = untouched(&first);
        let unbound_pk = PqPublicKey {
            pk_seed: first.keys[0].pk_seed,
            pk_root: [7u8; 32],
        };
        assert_eq!(
            sign_stateless_tsw_rss_mpc(&params, &mut first, &unbound_pk, msg, 100_000).unwrap_err(),
            KeccakMpcError::KeyBindingMismatch
        );
        assert_eq!(untouched(&first), before);

        let pk = DkgCachedSubtrees::build_distributed_rss(&params, &mut first, 64).unwrap().pk;

        // A root or parameter set other than the generated one is refused before any
        // evaluation or opening.
        let before = untouched(&first);
        let mut wrong_root = PqPublicKey {
            pk_seed: pk.pk_seed,
            pk_root: pk.pk_root,
        };
        wrong_root.pk_root[31] ^= 0x80;
        assert_eq!(
            sign_stateless_tsw_rss_mpc(&params, &mut first, &wrong_root, msg, 100_000).unwrap_err(),
            KeccakMpcError::KeyBindingMismatch
        );
        let mut other_params = params;
        other_params.fors_height = 2;
        assert_eq!(
            sign_stateless_tsw_rss_mpc(&other_params, &mut first, &pk, msg, 100_000).unwrap_err(),
            KeccakMpcError::KeyBindingMismatch
        );
        // Shorter chains under the bound key would open interior chain values.
        let short_chains = PqHashParams {
            w: 2,
            ell1: 256,
            ..params
        };
        assert!(short_chains.is_well_formed());
        assert_eq!(
            DkgCachedSubtrees::build_distributed_rss(&short_chains, &mut first, 64).unwrap_err(),
            KeccakMpcError::KeyBindingMismatch
        );
        assert_eq!(untouched(&first), before);
        assert!(!first.is_poisoned());

        let sig_first = sign_stateless_tsw_rss_mpc(&params, &mut first, &pk, msg, 100_000).unwrap();

        // Second session on the same key shares: another session id, other party randomness.
        let RssSlhMpcCluster { keys, .. } = first;
        let mut second = RssSlhMpcCluster::new([0xa2; 32], keys, make_rngs3(0x91)).unwrap();
        assert_ne!(second.mask_session.prim, [[0u8; 32]; 3]);
        let sig_second =
            sign_stateless_tsw_rss_mpc(&params, &mut second, &pk, msg, 100_000).unwrap();
        assert_eq!(sig_first.r_rand, sig_second.r_rand);
        assert_eq!(sig_first, sig_second);
        assert!(verify_pq_hash_sig(Cshake256Suite, &params, &pk, msg, &sig_first));

        // `R` is the PRF of the shared key on public inputs fixed by the key and message.
        let mu = th_pre_hash(Cshake256Suite, &pk.pk_seed, &pk.pk_root, msg);
        let expected_r = fips205_prf_msg(32, &sk_prf, &tsw_rss_opt_rand(&pk), &mu);
        assert_eq!(sig_first.r_rand.as_slice(), expected_r.as_slice());
    }

    /// Test-only trusted dealer for authenticated SPDZ Shamir material: degree-`< t` shares over
    /// `TowerGf256` and matching 2-lane `Tower128` MAC shares under one global key. It replaces
    /// dealerless preprocessing in these tests, which exercise the online protocol only.
    struct SpdzTestDealer {
        t: usize,
        pts: Vec<TowerGf256>,
        alpha: [Tower128; 2],
        stream: Cshake256WordStream4,
    }

    impl SpdzTestDealer {
        fn new(tag: &[u8], t: usize, pts: &[TowerGf256]) -> Self {
            let mid = crate::sponge::keccak::cshake256_static_midstate(b"QSAG.TEST.SPDZ.DEALER/v1");
            let mut dealer = Self {
                t,
                pts: pts.to_vec(),
                alpha: [Tower128::ZERO; 2],
                stream: Cshake256WordStream4::new(&mid, tag),
            };
            dealer.alpha = [dealer.tower(), dealer.tower()];
            dealer
        }

        fn word(&mut self) -> u64 {
            let mut w = [0u64; 1];
            self.stream.fill_words(&mut w);
            w[0]
        }

        fn tower(&mut self) -> Tower128 {
            Tower128(u128::from(self.word()) | (u128::from(self.word()) << 64))
        }

        fn share_tower(&mut self, secret: Tower128) -> Vec<Tower128> {
            let coeffs: Vec<Tower128> = (1..self.t).map(|_| self.tower()).collect();
            self.pts
                .iter()
                .map(|&pt| {
                    let mut acc = secret;
                    let mut power = pt;
                    for c in &coeffs {
                        acc = acc.add(c.mul_gf256(power));
                        power = power.mul(pt);
                    }
                    acc
                })
                .collect()
        }

        fn alpha_shares(&mut self) -> Vec<[Tower128; 2]> {
            let lanes = [self.share_tower(self.alpha[0]), self.share_tower(self.alpha[1])];
            (0..self.pts.len()).map(|p| [lanes[0][p], lanes[1][p]]).collect()
        }

        /// Authenticated sharing of 64 bits: per-party share word and MAC word.
        #[expect(
            clippy::needless_range_loop,
            reason = "bit, lane and party indices each address several parallel tables"
        )]
        fn auth_word(&mut self, bits: u64) -> (Vec<BitslicedGf256x64>, Vec<SpdzMacWord>) {
            let n = self.pts.len();
            let mut sh = vec![[0u64; 8]; n];
            let mut mac = vec![[[Tower128::ZERO; 64]; 2]; n];
            // Reuse polynomial storage across lanes instead of allocating six
            // vectors per bit of every test triple (millions of tiny allocations).
            let mut coeffs = vec![TowerGf256::ZERO; self.t];
            let mut mac_coeffs = vec![Tower128::ZERO; self.t];
            for i in 0..64 {
                let bit = (bits >> i) & 1 == 1;
                coeffs[0] = TowerGf256(u8::from(bit));
                for c in &mut coeffs[1..] { *c = TowerGf256(self.word() as u8); }
                for (p, &pt) in self.pts.iter().enumerate() {
                    let mut value = coeffs[self.t - 1];
                    for &c in coeffs[..self.t - 1].iter().rev() { value = value.mul(pt).add(c); }
                    bs_gf256_insert_lane(&mut sh[p], i, value);
                }
                for l in 0..2 {
                    mac_coeffs[0] = if bit { self.alpha[l] } else { Tower128::ZERO };
                    for c in &mut mac_coeffs[1..] { *c = self.tower(); }
                    for (p, &pt) in self.pts.iter().enumerate() {
                        let mut value = mac_coeffs[self.t - 1];
                        for &c in mac_coeffs[..self.t - 1].iter().rev() { value = value.mul_gf256(pt).add(c); }
                        mac[p][l][i] = value;
                    }
                }
            }
            (sh, mac)
        }

        fn vaults(&mut self, triples: usize) -> Vec<PreprocessedKeccakPartyVault> {
            let n = self.pts.len();
            let alpha_shares = self.alpha_shares();
            let mut per_party: Vec<Vec<KeccakBitTripleShare64>> =
                (0..n).map(|_| Vec::with_capacity(triples)).collect();
            for _ in 0..triples {
                let a = self.word();
                let b = self.word();
                let (a_sh, a_mac) = self.auth_word(a);
                let (b_sh, b_mac) = self.auth_word(b);
                let (c_sh, c_mac) = self.auth_word(a & b);
                for p in 0..n {
                    per_party[p].push(KeccakBitTripleShare64 {
                        a: a_sh[p],
                        b: b_sh[p],
                        c: c_sh[p],
                        a_mac: a_mac[p],
                        b_mac: b_mac[p],
                        c_mac: c_mac[p],
                    });
                }
            }
            per_party
                .into_iter()
                .enumerate()
                .map(|(p, triples)| PreprocessedKeccakPartyVault {
                    party_id: p,
                    eval_point: self.pts[p],
                    mac_alpha_lanes: alpha_shares[p],
                    triples,
                    cursor: 0,
                    poisoned: false,
                })
                .collect()
        }

        fn key_shares(
            &mut self,
            key_len: usize,
            pk_seed: [u8; 32],
            sk_seed: &[u8; 32],
            sk_prf: &[u8; 32],
        ) -> Vec<SpdzAuthenticatedKeyShare> {
            let n = self.pts.len();
            let auth = |dealer: &mut Self, key: &[u8; 32]| {
                let mut words = vec![[[0u64; 8]; 4]; n];
                let mut macs = vec![[[[Tower128::ZERO; 64]; 2]; 4]; n];
                for w in 0..4 {
                    let mut bits = u64::from_le_bytes(key[8 * w..8 * w + 8].try_into().unwrap());
                    if 8 * w >= key_len {
                        bits = 0;
                    }
                    let (sh, mac) = dealer.auth_word(bits);
                    for p in 0..n {
                        words[p][w] = sh[p];
                        macs[p][w] = mac[p];
                    }
                }
                (words, macs)
            };
            let (seed_words, seed_macs) = auth(self, sk_seed);
            let (prf_words, prf_macs) = auth(self, sk_prf);
            (0..n)
                .map(|p| SpdzAuthenticatedKeyShare {
                    party_id: p,
                    eval_point: self.pts[p],
                    key_len,
                    pk_seed,
                    sk_seed_words: seed_words[p],
                    sk_seed_macs: seed_macs[p],
                    sk_prf_words: prf_words[p],
                    sk_prf_macs: prf_macs[p],
                    slh_profile: SlhProfileLatch::new(),
                })
                .collect()
        }
    }

    fn spdz_test_rngs(n: usize, tag: u8) -> Vec<PartyPrivateRng> {
        (0..n)
            .map(|p| PartyPrivateRng::from_seed([tag + p as u8; 32], b"spdz-k"))
            .collect()
    }

    #[test]
    fn test_spdz_shamir_keccak_dishonest_majority_prf_msg_and_poison_abort() {
        // Dishonest-majority 3-of-4 Shamir (`2t - 1 = 5 > 4`, up to `2` active Byzantine signers!)
        let t = 3usize;
        let n = 4usize;
        let pts: Vec<TowerGf256> = (1..=n as u8).map(TowerGf256).collect();
        let mut rngs = spdz_test_rngs(n, 0x70);
        let mut dealer = SpdzTestDealer::new(b"prf-msg", t, &pts);
        let sk_seed = [0x5a; 32];
        let sk_prf: [u8; 32] = core::array::from_fn(|i| (i as u8).wrapping_mul(29) ^ 0xc3);
        let mut pk_seed = [0u8; 32];
        pk_seed[..16].copy_from_slice(&[0x11; 16]);
        let mut auth_keys = dealer.key_shares(16, pk_seed, &sk_seed, &sk_prf);
        // 1200 triples = 2 Keccak-f[1600] blocks (`600` per permutation: 1 honest + 1 tamper test!)
        let mut vaults = dealer.vaults(1200);

        let opt_rand = [0xABu8; 16];
        let m_prime = b"\x00\x04ctx!spdz-shamir-keccak-test";
        let expected_r = fips205_prf_msg(16, &sk_prf[..16], &opt_rand, m_prime);

        // 1. Honest `t = 3` quorum (`parties 0, 1, 2`) matches `fips205_prf_msg` bit-for-bit!
        {
            let mut cluster = SpdzSlhMpcCluster::new(
                [0x67; 32],
                t,
                &auth_keys[..t],
                &mut vaults[..t],
                &mut rngs[..t],
            )
            .unwrap();
            let (got_r, _tok) = cluster.eval_prf_msg_mpc(16, &opt_rand, m_prime).unwrap();
            assert_eq!(got_r, expected_r);
        }
        assert!(vaults[..t].iter().all(|v| !v.poisoned && v.remaining() == 600));

        // 2. Dishonest-majority active share tamper (`parties 0 and 1` collude and forge `sk_prf_words`)
        //    MUST be caught by SPDZ `MacCheck` BEFORE opening `R` AND permanently poison all vaults!
        auth_keys[0].sk_prf_words[0][0] ^= 1;
        auth_keys[0].sk_prf_words[0][1] ^= 1;
        auth_keys[1].sk_prf_words[0][1] ^= 1;
        {
            let mut bad_cluster = SpdzSlhMpcCluster::new(
                [0x68; 32],
                t,
                &auth_keys[..t],
                &mut vaults[..t],
                &mut rngs[..t],
            )
            .unwrap();
            assert_eq!(
                bad_cluster
                    .eval_prf_msg_mpc(16, &opt_rand, m_prime)
                    .unwrap_err(),
                Fips205Error::MpcActiveTamperDetected
            );
        }
        assert!(vaults[0].poisoned && vaults[1].poisoned && vaults[2].poisoned);
        assert_eq!(vaults[2].mac_alpha_lanes, [Tower128::ZERO; 2]);
    }

    #[test]
    fn spdz_batch64_prf_and_masked_f_match_fips_and_cut_tamper_poisons() {
        let t = 2usize;
        let pts: Vec<TowerGf256> = (1..=2u8).map(TowerGf256).collect();
        let mut rngs = spdz_test_rngs(2, 0x80);
        let mut dealer = SpdzTestDealer::new(b"batch64", t, &pts);
        let sk_seed: [u8; 32] = core::array::from_fn(|i| (i as u8).wrapping_mul(37) ^ 0x6d);
        let sk_prf = [0x21; 32];
        let mut pk_seed = [0u8; 32];
        pk_seed[..16].copy_from_slice(&[0x33; 16]);
        let keys = dealer.key_shares(16, pk_seed, &sk_seed, &sk_prf);
        // Two 64-instance permutations: 24 rounds of 1600 triple words each.
        let per_batch = 24 * SPDZ_BATCH_POSITIONS;
        let mut vaults = dealer.vaults(2 * per_batch);
        let mut cluster =
            SpdzSlhMpcCluster::new([0x69; 32], t, &keys, &mut vaults, &mut rngs).unwrap();

        let prf_adrs: Vec<Fips205Adrs> = (0..64u32)
            .map(|i| {
                let mut a = Fips205Adrs::ZERO;
                a.layer = i % 3;
                a.adrs_type = Fips205AdrsType::WotsPrf;
                a.key_pair = i / 7;
                a.f5 = i;
                a
            })
            .collect();
        let step_adrs: Vec<Fips205Adrs> = prf_adrs
            .iter()
            .map(|a| {
                let mut s = *a;
                s.adrs_type = Fips205AdrsType::WotsHash;
                s.f6 = 5;
                s
            })
            .collect();
        // Every third instance keeps its PRF value; the others take one F step.
        let exec_mask = (0..64).fold(0u64, |m, i| if i % 3 == 0 { m } else { m | (1 << i) });

        let (mut cur_sh, mut cur_mac) = cluster.eval_prf_batch64_spdz(&pk_seed[..16], &prf_adrs).unwrap();
        cluster
            .eval_f_step_masked_batch64_spdz(
                &pk_seed[..16],
                &step_adrs,
                exec_mask,
                &mut cur_sh,
                &mut cur_mac,
            )
            .unwrap();
        assert!(cluster.vaults.iter().all(|v| v.remaining() == 0));

        let (blocks, _tok) = cluster
            .finalize_cut_batches_spdz("spdz_cut_batch64_test", &cur_sh, &cur_mac, &[64])
            .unwrap();
        assert_eq!(blocks.len(), 64);
        for i in 0..64 {
            let prf = crate::fips205::fips205_prf(16, &pk_seed[..16], &sk_seed[..16], &prf_adrs[i]);
            let expected = if (exec_mask >> i) & 1 == 1 {
                crate::fips205::fips205_f(16, &pk_seed[..16], &step_adrs[i], &prf)
            } else {
                prf
            };
            assert_eq!(blocks[i], expected, "instance {i}");
        }

        // A forged cut share (consistent polynomial, wrong value) fails the cut `MacCheck`.
        cur_sh[0][5][0] ^= 1 << 9;
        assert_eq!(
            cluster
                .finalize_cut_batches_spdz("spdz_cut_batch64_test", &cur_sh, &cur_mac, &[64])
                .unwrap_err(),
            Fips205Error::MpcActiveTamperDetected
        );
        assert!(cluster.vaults.iter().all(|v| v.poisoned));
    }

    #[test]
    fn spdz_batch64_aborts_and_poisons_on_corrupted_triple_and_exhaustion() {
        let t = 2usize;
        let pts: Vec<TowerGf256> = (1..=2u8).map(TowerGf256).collect();
        let mut dealer = SpdzTestDealer::new(b"batch64-tamper", t, &pts);
        let mut pk_seed = [0u8; 32];
        pk_seed[..16].copy_from_slice(&[0x44; 16]);
        let keys = dealer.key_shares(16, pk_seed, &[0x17; 32], &[0x18; 32]);
        let adrs = [Fips205Adrs::ZERO; 3];
        let per_batch = 24 * SPDZ_BATCH_POSITIONS;

        // A wrong product bit in a first-round triple share reaches the Beaver openings of the
        // next round, so the batched `MacCheck` inside the evaluation rejects it.
        let mut vaults = dealer.vaults(per_batch);
        vaults[1].triples[77].c[0] ^= 1 << 2;
        let mut rngs = spdz_test_rngs(2, 0x90);
        {
            let mut cluster =
                SpdzSlhMpcCluster::new([0x6a; 32], t, &keys, &mut vaults, &mut rngs).unwrap();
            assert_eq!(
                cluster.eval_prf_batch64_spdz(&pk_seed[..16], &adrs).unwrap_err(),
                Fips205Error::MpcActiveTamperDetected
            );
        }
        assert!(vaults.iter().all(|v| v.poisoned));

        // A wrong product bit in a last-round triple share of an output position is never
        // opened inside the batch: the shares come back, and the cut `MacCheck` rejects them
        // before anything is revealed.
        let mut vaults = dealer.vaults(per_batch);
        vaults[1].triples[23 * SPDZ_BATCH_POSITIONS + 5].c[0] ^= 1 << 1;
        {
            let mut cluster =
                SpdzSlhMpcCluster::new([0x6c; 32], t, &keys, &mut vaults, &mut rngs).unwrap();
            let (out_sh, out_mac) = cluster.eval_prf_batch64_spdz(&pk_seed[..16], &adrs).unwrap();
            assert_eq!(
                cluster
                    .finalize_cut_batches_spdz("spdz_cut_batch64_test", &out_sh, &out_mac, &[3])
                    .unwrap_err(),
                Fips205Error::MpcActiveTamperDetected
            );
        }
        assert!(vaults.iter().all(|v| v.poisoned));

        // Too few triples for a whole batch: abort and poison rather than a partial evaluation.
        let mut short = dealer.vaults(SPDZ_BATCH_POSITIONS);
        let mut cluster =
            SpdzSlhMpcCluster::new([0x6b; 32], t, &keys, &mut short, &mut rngs).unwrap();
        assert_eq!(
            cluster.eval_prf_batch64_spdz(&pk_seed[..16], &adrs).unwrap_err(),
            Fips205Error::MpcActiveTamperDetected
        );
        assert!(cluster.vaults.iter().all(|v| v.poisoned));
    }

    #[test]
    fn spdz_poisoned_quorum_refuses_every_later_evaluation_and_opening() {
        let t = 2usize;
        let pts: Vec<TowerGf256> = (1..=2u8).map(TowerGf256).collect();
        let mut dealer = SpdzTestDealer::new(b"batch64-latch", t, &pts);
        let mut pk_seed = [0u8; 32];
        pk_seed[..16].copy_from_slice(&[0x55; 16]);
        let keys = dealer.key_shares(16, pk_seed, &[0x27; 32], &[0x28; 32]);
        let adrs = [Fips205Adrs::ZERO; 3];
        let mut vaults = dealer.vaults(24 * SPDZ_BATCH_POSITIONS);
        let mut rngs = spdz_test_rngs(2, 0xa0);
        {
            let mut cluster =
                SpdzSlhMpcCluster::new([0x6d; 32], t, &keys, &mut vaults, &mut rngs).unwrap();
            let (out_sh, out_mac) = cluster.eval_prf_batch64_spdz(&pk_seed[..16], &adrs).unwrap();
            let mut forged = out_sh.clone();
            forged[0][5][0] ^= 1 << 1;
            assert_eq!(
                cluster
                    .finalize_cut_batches_spdz("spdz_latch_test", &forged, &out_mac, &[3])
                    .unwrap_err(),
                Fips205Error::MpcActiveTamperDetected
            );
            assert!(cluster.vaults.iter().all(|v| v.poisoned));

            // Poisoning zeroed the MAC key shares, so all-zero MAC shares now satisfy the MAC
            // relation of the true cut shares. The opening must be refused all the same.
            let zero_mac: Vec<Vec<SpdzMacWord>> = out_mac
                .iter()
                .map(|words| vec![[[Tower128::ZERO; 64]; 2]; words.len()])
                .collect();
            assert_eq!(
                cluster
                    .finalize_cut_batches_spdz("spdz_latch_test", &out_sh, &zero_mac, &[3])
                    .unwrap_err(),
                Fips205Error::MpcActiveTamperDetected
            );
            assert_eq!(
                cluster
                    .finalize_cut_blocks_spdz("spdz_latch_test", &[], &zero_mac, &out_sh, &zero_mac)
                    .unwrap_err(),
                Fips205Error::MpcActiveTamperDetected
            );
            let (mut cur_sh, mut cur_mac) = (out_sh.clone(), out_mac.clone());
            for exec_mask in [0u64, 0b111] {
                assert_eq!(
                    cluster
                        .eval_f_step_masked_batch64_spdz(
                            &pk_seed[..16],
                            &adrs,
                            exec_mask,
                            &mut cur_sh,
                            &mut cur_mac
                        )
                        .unwrap_err(),
                    Fips205Error::MpcActiveTamperDetected
                );
            }
            assert_eq!(
                cluster.eval_prf_batch64_spdz(&pk_seed[..16], &adrs).unwrap_err(),
                Fips205Error::MpcActiveTamperDetected
            );
            assert_eq!(
                cluster.eval_prf_msg_mpc(16, &[0u8; 16], b"m").unwrap_err(),
                Fips205Error::MpcActiveTamperDetected
            );
        }
        // The poisoned vaults cannot be put behind a new cluster either.
        assert!(matches!(
            SpdzSlhMpcCluster::new([0x6e; 32], t, &keys, &mut vaults, &mut rngs),
            Err(KeccakMpcError::Poisoned)
        ));
    }

    #[test]
    fn test_spdz_key_share_profile_binding_persists_across_clusters() {
        let t = 2usize;
        let n = 3usize;
        let pts: Vec<TowerGf256> = (1..=n as u8).map(TowerGf256).collect();
        let mut rngs = spdz_test_rngs(n, 0x91);
        let mut dealer = SpdzTestDealer::new(b"spdz-bind", t, &pts);
        let sk_seed = [0x42; 32];
        let sk_prf = [0x24; 32];
        let pk_seed = [0x11; 32];
        let keys = dealer.auth_key_shares(16, pk_seed, &sk_seed, &sk_prf);
        let mut vaults = dealer.vaults(4);

        let p_128s = Fips205Params::SLH_DSA_SHAKE_128S;
        let p_128f = Fips205Params::SLH_DSA_SHAKE_128F;
        {
            let mut cluster =
                SpdzSlhMpcCluster::new([0x01; 32], t, &keys, &mut vaults, &mut rngs).unwrap();
            cluster.bind_key_params(&p_128s, &pk_seed[..16]).unwrap();
            cluster.bind_key_params(&p_128s, &pk_seed[..16]).unwrap();
            assert_eq!(
                cluster.bind_key_params(&p_128f, &pk_seed[..16]),
                Err(Fips205Error::InvalidParameterSet)
            );
        }
        // Constructing a fresh cluster over the same key shares must still enforce `p_128s`.
        let mut cluster2 =
            SpdzSlhMpcCluster::new([0x02; 32], t, &keys, &mut vaults, &mut rngs).unwrap();
        assert_eq!(
            cluster2.bind_key_params(&p_128f, &pk_seed[..16]),
            Err(Fips205Error::InvalidParameterSet)
        );
        cluster2.bind_key_params(&p_128s, &pk_seed[..16]).unwrap();
    }
}
