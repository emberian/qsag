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
