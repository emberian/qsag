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
use core::sync::atomic::{AtomicBool, Ordering};

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
    SHAKE256_RATE_BYTES, cshake256_32, encode_multi_frame,
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
use crate::wipe::SecretBuffer;
use crate::wipe::{ct_eq_bytes, ct_eq_bytes32, wipe_bytes, wipe_bytes32, wipe_u64s};

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
        pk_coms[i] = cshake256_32(
            b"QSAG.RSS.DKG.PK.COM/v1",
            &encode_multi_frame(&[&session_id, &i_be, &pk_salts[i], &pk_contribs[i]]),
        );
    }
    // Round 2: Verify `pk_seed` openings
    let mut pk_seed = [0u8; 32];
    for i in 0..3 {
        let i_be = (i as u64).to_be_bytes();
        let exp = cshake256_32(
            b"QSAG.RSS.DKG.PK.COM/v1",
            &encode_multi_frame(&[&session_id, &i_be, &pk_salts[i], &pk_contribs[i]]),
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
            let mut frame = encode_multi_frame(&[session_id, &coin, &slot_be, prg, seed, prf]);
            let key = cshake256_32(b"QSAG.RSS.MASK.HEDGE/v1", &frame);
            wipe_bytes(&mut frame);
            key
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

/// Bits of a 64-bit operand at positions congruent to `r` modulo 5.
const RSS_CLMUL_IN_MASKS: [u64; 5] = {
    let mut masks = [0u64; 5];
    let mut bit = 0;
    while bit < 64 {
        masks[bit % 5] |= 1u64 << bit;
        bit += 1;
    }
    masks
};

/// Bits of a 128-bit product at positions congruent to `k` modulo 5.
const RSS_CLMUL_OUT_MASKS: [u128; 5] = {
    let mut masks = [0u128; 5];
    let mut bit = 0;
    while bit < 128 {
        masks[bit % 5] |= 1u128 << bit;
        bit += 1;
    }
    masks
};

// Carryless 64x64 multiplication from integer multiplications. Each residue class modulo 5
// holds at most 13 operand bits, so in an integer product of two classes every coefficient
// is at most 13 < 32 and stays inside its own 5-bit field. The low bit of each field is the
// carryless coefficient; XOR combines the class pairs with the same residue sum.
#[inline]
fn rss_clmul_classes(v: u64) -> [u64; 5] {
    RSS_CLMUL_IN_MASKS.map(|m| v & m)
}

#[inline]
fn rss_clmul64_classes(am: &[u64; 5], bm: &[u64; 5]) -> u128 {
    let mut out = 0u128;
    for k in 0..5 {
        let mut z = 0u128;
        for r in 0..5 {
            z ^= u128::from(am[r]) * u128::from(bm[(k + 5 - r) % 5]);
        }
        out |= z & RSS_CLMUL_OUT_MASKS[k];
    }
    out
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

/// One operand of a field multiplication, split once into the residue classes used by
/// [`rss_clmul64_classes`] so that it can multiply many elements.
struct RssFieldMultiplier {
    lo: [u64; 5],
    hi: [u64; 5],
    mid: [u64; 5],
}

impl RssFieldMultiplier {
    #[inline]
    fn new(v: RssProofField) -> Self {
        let b0 = v.0 as u64;
        let b1 = (v.0 >> 64) as u64;
        Self {
            lo: rss_clmul_classes(b0),
            hi: rss_clmul_classes(b1),
            mid: rss_clmul_classes(b0 ^ b1),
        }
    }

    #[inline]
    fn mul(&self, x: RssProofField) -> RssProofField {
        let a0 = x.0 as u64;
        let a1 = (x.0 >> 64) as u64;
        let p0 = rss_clmul64_classes(&rss_clmul_classes(a0), &self.lo);
        let p2 = rss_clmul64_classes(&rss_clmul_classes(a1), &self.hi);
        let p1 = rss_clmul64_classes(&rss_clmul_classes(a0 ^ a1), &self.mid) ^ p0 ^ p2;
        let lo = p0 ^ (p1 << 64);
        let hi = p2 ^ (p1 >> 64);
        // Reduce hi * t^128 using t^128 = t^7 + t^2 + t + 1. The
        // overflow has degree at most six, so the second fold cannot overflow.
        let carry = (hi >> 127) ^ (hi >> 126) ^ (hi >> 121);
        RssProofField(
            lo ^ hi
                ^ (hi << 1)
                ^ (hi << 2)
                ^ (hi << 7)
                ^ carry
                ^ (carry << 1)
                ^ (carry << 2)
                ^ (carry << 7),
        )
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
    nu_bits: Vec<RssProofField>,
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
/// elements; `hi_groups` blocks exist in the upper half, which starts at block `half`. With
/// public block weights `w` on the lower half (the upper half carries the extra factor `mu`)
/// the invariant `claim = sum_g w_g <x_g, y_g>` is preserved by
/// `x' = x_lo + gamma * mu * x_hi`, `y' = y_lo + gamma^-1 * y_hi`,
/// `claim' = claim + gamma^-1 * L + gamma * R`, where `L = sum_g w_g <x_lo, y_hi>` and
/// `R = mu * sum_g w_g <x_hi, y_lo>` are sent as masked additive shares before `gamma` is drawn.
#[expect(
    clippy::too_many_arguments,
    reason = "One protocol round: tables, weights, claim, randomness and challenge context"
)]
fn rss_dzk_fold_round(
    ctx: &RssDzkCtx<'_>,
    pass: usize,
    step: usize,
    tables: &mut RssDzkTables,
    unit: usize,
    hi_groups: usize,
    half: usize,
    weights: Option<&[RssProofField]>,
    mu: RssProofField,
    claim: &mut [RssProofField; 3],
    streams: &mut RssProofStreams,
    party_rngs: &mut [PartyPrivateRng; 3],
) -> Result<(), KeccakMpcError> {
    let mut l_msg = SecretBuffer(streams.zero_share());
    let mut r_msg = SecretBuffer(streams.zero_share());
    let RssDzkTables { x, y, lhs, rhs } = tables;
    let call_groups = if weights.is_some() { 1 } else { hi_groups };
    let need = 2 * unit * call_groups;
    if lhs.len() < need {
        lhs.resize(need, [0; 2]);
        rhs.resize(need, [0; 2]);
    }
    for p in 0..3 {
        let q = (p + 1) % 3;
        let mut l_acc = RssProofField::ZERO;
        let mut r_acc = RssProofField::ZERO;
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
            if let Some(w) = weights {
                let out = qsag_asm::tower128_bdoz_2lane_poly_mac(&lhs[..filled], &rhs[..filled]);
                l_acc = l_acc.add(w[g].mul(RssProofField(out[0])));
                r_acc = r_acc.add(w[g].mul(RssProofField(out[1])));
                filled = 0;
            }
        }
        if weights.is_none() {
            let out = qsag_asm::tower128_bdoz_2lane_poly_mac(&lhs[..filled], &rhs[..filled]);
            l_acc = RssProofField(out[0]);
            r_acc = RssProofField(out[1]);
        }
        l_msg[p] = l_msg[p].add(l_acc);
        r_msg[p] = r_msg[p].add(mu.mul(r_acc));
    }

    let gamma = ctx
        .coin(b"RSS_DZK_POLY_FOLD_COIN/v3", pass, step, party_rngs)?
        .nonzero();
    let gamma_inv = gamma.inv_public();
    let gamma_mu = gamma.mul(mu);
    let scale_x = RssFieldMultiplier::new(gamma_mu);
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
        let w0 = g * RSS_DZK_GROUP_WORDS;
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
                tabs[p][e0 + j] = qsag_asm::tower128_bdoz_2lane_poly_mac(
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
            let out = qsag_asm::tower128_bdoz_2lane_poly_mac(&lhs, nu_pairs);
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
    let total = groups * RSS_DZK_LANES;
    let mut tables = RssDzkTables {
        x: [vec![0u128; total], vec![0u128; total], vec![0u128; total]],
        y: [vec![0u128; total], vec![0u128; total], vec![0u128; total]],
        lhs: Vec::new(),
        rhs: Vec::new(),
    };
    let mut planes = [[0u64; 64]; 2];
    for s in 0..3 {
        for g in 0..groups {
            let words = g * RSS_DZK_GROUP_WORDS..(g + 1) * RSS_DZK_GROUP_WORDS;
            let lanes = g * RSS_DZK_LANES..(g + 1) * RSS_DZK_LANES;
            rss_bind_group(
                &pending.a[s][words.clone()],
                &pattern,
                &mut planes,
                &mut tables.x[s][lanes.clone()],
            );
            for (lane, value) in tables.x[s][lanes.clone()].iter_mut().enumerate() {
                *value = RssProofField(*value).mul_t_pow(lane as u32).0;
            }
            rss_bind_group(
                &pending.b[s][words],
                &pattern,
                &mut planes,
                &mut tables.y[s][lanes],
            );
        }
    }
    qsag_asm::volatile_fill(&mut planes, [0; 64]);

    // Halve the group index under the public weights `bound_weight * nu[g]`.
    let block_weights: Vec<RssProofField> =
        weights.nu.iter().map(|v| bound_weight.mul(*v)).collect();
    let mut step = 0usize;
    let mut size = groups.next_power_of_two();
    let mut cur = groups;
    while size > 1 {
        let half = size / 2;
        let hi_groups = cur.saturating_sub(half);
        let mu = weights.nu_bits[half.trailing_zeros() as usize];
        rss_dzk_fold_round(
            ctx,
            pass,
            step,
            &mut tables,
            RSS_DZK_LANES,
            hi_groups,
            half,
            Some(&block_weights),
            mu,
            &mut claim,
            streams,
            party_rngs,
        )?;
        cur = cur.min(half);
        size = half;
        step += 1;
    }
    // One group remains; absorb its public weight and halve the 64 lanes.
    for row in &mut tables.x {
        for word in row.iter_mut().take(RSS_DZK_LANES) {
            *word = block_weights[0].mul(RssProofField(*word)).0;
        }
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
            None,
            RssProofField::ONE,
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
        RssDzkWeights { mu, nu_bits, nu }
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
                pending_dzk.a[s].extend_from_slice(&b[s][l1..l1 + 64]);
                pending_dzk.b[s].extend_from_slice(&b[s][l2..l2 + 64]);
            }
            pending_dzk.c[s].extend_from_slice(&prod[s]);
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
    fn eval_prf_batch64_secret(
        &mut self,
        pk_seed: &[u8],
        adrs_batch: &[Fips205Adrs],
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

        self.permute_batch64(batch_len, &mut st_p, &mut st_s)?;

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

        if let Err(e) = self.permute_batch64(batch_len, &mut st_p, &mut st_s) {
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
            cut.prim[p].extend_from_slice(&blocks_p[p][..n_bits]);
            cut.sec[p].extend_from_slice(&blocks_s[p][..n_bits]);
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
        let mut chunk_sizes = Vec::new();

        // First evaluate the `k` revealed FORS `sk` values (`1` batch of `<= 64` since `k <= 35`!)
        let mut rev_prf_adrs = Vec::with_capacity(params.k);
        let mut i = 0;
        while i < params.k {
            let idx_i = fors_indices[i] as usize;
            if idx_i >= t_leaves {
                return Err(Fips205Error::MpcActiveTamperDetected);
            }
            let mut prf_adrs = base_adrs.with_type_and_clear(Fips205AdrsType::ForsPrf);
            prf_adrs.key_pair = base_adrs.key_pair;
            prf_adrs.f6 = (i * t_leaves + idx_i) as u32;
            rev_prf_adrs.push(prf_adrs);
            i += 1;
        }
        let (mut rev_p, mut rev_s) = self
            .eval_prf_batch64_secret(pk_seed, &rev_prf_adrs)
            .map_err(rss_oracle_abort)?;
        for p in 0..3 {
            cut.prim[p].extend_from_slice(&rev_p[p][..8 * n]);
            cut.sec[p].extend_from_slice(&rev_s[p][..8 * n]);
        }
        wipe_rss_states(&mut rev_p, &mut rev_s);

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
                .eval_prf_batch64_secret(pk_seed, &prf_batch)
                .map_err(rss_oracle_abort)?;
            let mut cur_p = SecretBuffer(cur_p);
            let mut cur_s = SecretBuffer(cur_s);
            let mask = batch_active_mask(chunk_len);
            self.eval_f_step_masked_batch64(pk_seed, &leaf_batch, mask, &mut cur_p, &mut cur_s)
                .map_err(rss_oracle_abort)?;
            for p in 0..3 {
                cut.prim[p].extend_from_slice(&cur_p[p][..8 * n]);
                cut.sec[p].extend_from_slice(&cur_s[p][..8 * n]);
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
        for b in 0..params.k {
            let mut blk = SlhBlock::zero(n);
            for byte_idx in 0..n {
                let mut v = 0u8;
                for bit in 0..8 {
                    v |= (((opened_words[8 * byte_idx + bit] >> b) & 1) as u8) << bit;
                }
                blk.bytes[byte_idx] = v;
            }
            revealed_sks.push(blk);
        }

        let mut flat_leaves = Vec::with_capacity(total_leaves);
        let mut word_off = n_bits;
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
                .eval_prf_batch64_secret(pk_seed, &prf_batch)
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
                cut.prim[p].extend_from_slice(&cur_p[p][..n_bits]);
                cut.sec[p].extend_from_slice(&cur_s[p][..n_bits]);
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
                .eval_prf_batch64_secret(pk_seed, &prf_batch)
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
                cut.prim[p].extend_from_slice(&cur_p[p][..n_bits]);
                cut.sec[p].extend_from_slice(&cur_s[p][..n_bits]);
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
            pending_macs[p].push(de_macs[p][w]);
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
        let chis: [[u128; 2]; 64] = core::array::from_fn(|bit| core::array::from_fn(|lane| {
            let off = (2 * bit + lane) * 16;
            let value = u128::from_le_bytes(core::array::from_fn(|i| chi_buf[off + i]));
            if value == 0 { 1 } else { value }
        }));
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
        let com = cshake256_32(
            b"QSAG.SPDZ.KECCAK.PEND.MAC.COM/v1",
            &encode_multi_frame(&[session_id, phase.as_bytes(), &q_be, &s0_b, &s1_b, &salt]),
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
        let exp = cshake256_32(
            b"QSAG.SPDZ.KECCAK.PEND.MAC.COM/v1",
            &encode_multi_frame(&[
                session_id,
                phase.as_bytes(),
                &q_be,
                &s0_b,
                &s1_b,
                &sig_salts[q],
            ]),
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

    let all_macs = spdz_authenticate_bs_gf256_words(
        session_id,
        t,
        eval_points,
        ot_mesh,
        alpha_contribs,
        alpha_shamir,
        &packed_words,
        party_rngs,
    )?;

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
        for p in 0..m {
            if vaults[p].eval_point != quorum_pts[p] || keys[p].key_len != keys[0].key_len {
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
        let alpha_sh: Vec<[Tower128; 2]> = (0..m).map(|p| self.vaults[p].mac_alpha_lanes).collect();
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
        let alpha_sh: Vec<[Tower128; 2]> = (0..m).map(|p| self.vaults[p].mac_alpha_lanes).collect();
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
        let alpha_sh: Vec<[Tower128; 2]> = (0..m).map(|p| self.vaults[p].mac_alpha_lanes).collect();

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
        if !params.is_valid() || self.keys.iter().any(|key|
            key.key_len != params.n || key.pk_seed[..key.key_len] != *pk_seed) {
            return Err(Fips205Error::InvalidParameterSet);
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
                cut_sh[p].push(st_sh[p][w]);
                cut_mac[p].push(st_mac[p][w]);
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
        self.ensure_live()?;
        let m = self.quorum_pts.len();
        let n = params.n;
        if n != self.keys[0].key_len
            || pk_seed.len() != n
            || fors_indices.len() != params.k
            || params.k > 64
        {
            return Err(Fips205Error::InvalidParameterSet);
        }
        let t_leaves = 1usize << params.a;
        let total_leaves = params.k * t_leaves;

        let mut cut_sh = SecretBuffer(vec![Vec::new(); m]);
        let mut cut_mac = SecretBuffer(vec![Vec::new(); m]);
        let mut chunk_sizes = Vec::new();

        // The `k` revealed FORS secret values: one 64-instance batch.
        let mut rev_prf_adrs = Vec::with_capacity(params.k);
        for (i, &idx) in fors_indices.iter().enumerate() {
            let idx_i = idx as usize;
            if idx_i >= t_leaves {
                return Err(Fips205Error::MpcActiveTamperDetected);
            }
            let mut prf_adrs = base_adrs.with_type_and_clear(Fips205AdrsType::ForsPrf);
            prf_adrs.key_pair = base_adrs.key_pair;
            prf_adrs.f6 = (i * t_leaves + idx_i) as u32;
            rev_prf_adrs.push(prf_adrs);
        }
        let (rev_sh, rev_mac) = self.eval_prf_batch64_spdz(pk_seed, &rev_prf_adrs)?;
        for p in 0..m {
            cut_sh[p].extend_from_slice(&rev_sh[p]);
            cut_mac[p].extend_from_slice(&rev_mac[p]);
        }
        chunk_sizes.push(params.k);

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
                cut_sh[p].extend_from_slice(&cur_sh[p]);
                cut_mac[p].extend_from_slice(&cur_mac[p]);
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
        let n = params.n;
        if n != self.keys[0].key_len || pk_seed.len() != n {
            return Err(Fips205Error::InvalidParameterSet);
        }
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
                cut_sh[p].extend_from_slice(&cur_sh[p]);
                cut_mac[p].extend_from_slice(&cur_mac[p]);
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
        cluster.permute_batch64(chunk_len, &mut st_p, &mut st_s)?;

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
            if let Err(e) = cluster.permute_batch64(chunk_len, &mut sp, &mut ss) {
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
            cut.prim[p].extend_from_slice(&cur_p[p]);
            cut.sec[p].extend_from_slice(&cur_s[p]);
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
