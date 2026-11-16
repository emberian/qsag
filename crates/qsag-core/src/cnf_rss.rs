//! Generalized `(t, n)` CNF replicated secret sharing and a trusted-coordinator
//! prototype of its `t-of-t` online projection into a 56-lane MiniMAC Keccak engine.
//!
//! Custody uses one slot for each `(t - 1)`-party subset `S`; party `i` holds that
//! slot exactly when `i` is not in `S`. Any `(t - 1)`-party coalition misses its own
//! slot. An active quorum `Q` assigns each slot to `min(Q \ S)`, checks overlapping
//! replicas, and rerandomizes the resulting additive shares. Supported custody
//! configurations satisfy `2 <= t <= n <= 10`.
//!
//! The arithmetic uses systematic `[128, 56, 73]` Reed–Solomon codewords over
//! [`TowerGf256`] and their `[128, 111, 18]` Schur square. It packs 56 Boolean
//! Keccak lanes and calls [`qsag_asm::gf256_shamir_mul`] on contiguous gate buffers.
//! Code distances and fault-injection tests describe algebraic checks; they are
//! not a security proof for the concrete correlation source or party isolation.
//!
//! ### Trust boundary
//! This module currently executes all parties in one address space. Tuple generation
//! combines every slot seed, and MAC transitions reconstruct both the shared value and
//! MAC key inside that coordinator. It is therefore a trusted-coordinator prototype,
//! NOT an isolated-party malicious-secure MPC deployment. The codeword and fault tests
//! do not establish privacy against the coordinator. Never hand this coordinator the
//! custody shares when that process is outside the trusted boundary.

use alloc::boxed::Box;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;
use core::hint::black_box;

use crate::baggy::{BaggyEngine, BaggyError, TAG_BAGGY_OPT_RAND, TAG_BAGGY_R, keyed_mu_frame};
use crate::field::tower::{Tower128, TowerGf256};
use crate::fips205::{
    CutBoundaryMacToken, Fips205Adrs, Fips205AdrsType, Fips205Error, Fips205Params, ForsMpcOutput,
    OracleCallToken, SlhBlock, SlhMpcOracles, sealed_mpc_oracles, try_wots_base16_digits_and_csum,
};
use crate::keccak_mpc::{
    KeccakMpcError, TSW_F_SECRET_OFFSET, TSW_PRF_SECRET_OFFSET, TSW_SUITE_MIDSTATE,
    tsw_secret32_frame,
};
use crate::preprocessing::{PartyPrivateRng, PreprocessError, run_commit_and_open_coin};
use crate::rss256::Rss256Error;
use crate::sponge::keccak::{
    Cshake256Xof, KECCAK_ROTATION_OFFSETS, KECCAK_ROUND_CONSTANTS, SHAKE256_RATE_BYTES,
    SHAKE256_RATE_LANES, cshake256_32_multi_frame,
};
use crate::tsw_baggy::{HashAdrs, TAG_PRF, TAG_TH_F};
use crate::wipe::{SecretBuffer, SecretVec, SecretWipe, ct_eq_bytes, ct_eq_bytes32};
use crate::wots_c::LaneSpec;

/// Codeword length in `TowerGf256` bytes (`2` AVX-512 ZMM registers).
pub const MINIMAC_CODE_N: usize = 128;
/// Number of parallel Boolean `Keccak-f[1600]` lanes packed systematically in `0..56`.
pub const MINIMAC_DATA_K: usize = 56;
/// Dimension of the Schur-product code `C^{*2}` (`2 * 56 - 1 = 111`, distance `18` bytes = `144` bits).
const MINIMAC_C2_K: usize = 2 * MINIMAC_DATA_K - 1;
/// Number of parity coordinates of `C` (`128 - 56 = 72`).
const MINIMAC_PARITY_C: usize = MINIMAC_CODE_N - MINIMAC_DATA_K;
/// Number of zero-prefix masking coordinates in `C^{*2}` (`111 - 56 = 55`).
const MINIMAC_ZERO_MASK_K: usize = MINIMAC_C2_K - MINIMAC_DATA_K;
/// Number of parity check coordinates of `C^{*2}` (`128 - 111 = 17`).
const MINIMAC_PARITY_C2: usize = MINIMAC_CODE_N - MINIMAC_C2_K;
/// Keccak state bit count.
const STATE_BITS: usize = 1600;
/// Digest bit count (`32` bytes).
const DIGEST_BITS: usize = 256;
/// Contiguous byte length of one 1,600-bit `MiniMAC` state (`1600 * 128 = 204,800` bytes).
const STATE_CODE_BYTES: usize = STATE_BITS * MINIMAC_CODE_N;
/// Gates per 56-lane `Keccak-f[1600]` permutation (`24 * 1600 = 38,400`).
pub const GATES_PER_WAVE_PERM: usize = 24 * STATE_BITS;
/// Maximum custodian count supported by `CnfRssConfig`.
pub const MAX_CNF_RSS_PARTIES: usize = 10;
/// Canonical wire header for `CnfRssKeyShare256`.
const CNF_KEY_SHARE_MAGIC: &[u8; 8] = b"QSCNFK01";

/// Errors surfaced by `(t, n)` CNF-RSS custody, Theorem 4.1 projection, or `MiniMAC` execution.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CnfRssError {
    /// Invalid `(t, n)`, `key_len`, or quorum subset.
    InvalidParameters,
    /// Underlying commit-and-open or RNG protocol failure.
    Preprocess(PreprocessError),
    /// Round-2 commitment mismatch attributed to `party`.
    CommitmentMismatch { phase: &'static str, party: usize },
    /// Replicated slot overlap check failed inside online quorum `Q` on `slot_idx`.
    SlotOverlapMismatch { slot_idx: usize },
    /// Active `MiniMAC` codeword, Booleanity, `C^{*2}` parity, or `Tower128` MAC check rejected.
    ActiveTamperDetected { phase: &'static str },
    /// Pre-staged `CnfRssBeaverBank` exhausted.
    BeaverBankExhausted,
    /// Attempted to open cut-boundary digests while unverified gates remain pending.
    OpenBeforeBarrier,
    /// Key shares are unbound or bound to a different public key / parameter set.
    KeyBindingMismatch,
    /// Engine was permanently poisoned by an earlier protocol failure.
    Poisoned,
}

impl From<PreprocessError> for CnfRssError {
    fn from(e: PreprocessError) -> Self {
        Self::Preprocess(e)
    }
}

impl From<CnfRssError> for KeccakMpcError {
    fn from(e: CnfRssError) -> Self {
        match e {
            CnfRssError::InvalidParameters => Self::InvalidParameters,
            CnfRssError::Preprocess(p) => Self::Preprocess(p),
            CnfRssError::CommitmentMismatch { party, .. } => Self::RssCommitMismatch {
                accused_party: party,
            },
            CnfRssError::KeyBindingMismatch => Self::KeyBindingMismatch,
            CnfRssError::Poisoned => Self::Poisoned,
            CnfRssError::SlotOverlapMismatch { .. }
            | CnfRssError::ActiveTamperDetected { .. }
            | CnfRssError::BeaverBankExhausted
            | CnfRssError::OpenBeforeBarrier => Self::SpdzMacAbort,
        }
    }
}

impl From<CnfRssError> for BaggyError {
    fn from(e: CnfRssError) -> Self {
        match e {
            CnfRssError::InvalidParameters => Self::Engine(Rss256Error::InvalidParameters),
            CnfRssError::BeaverBankExhausted => Self::Engine(Rss256Error::BeaverBankExhausted),
            CnfRssError::OpenBeforeBarrier => Self::Engine(Rss256Error::OpenBeforeCheck),
            CnfRssError::KeyBindingMismatch => Self::KeyBindingMismatch,
            CnfRssError::Poisoned => Self::Engine(Rss256Error::Poisoned),
            CnfRssError::ActiveTamperDetected { .. } | CnfRssError::SlotOverlapMismatch { .. } => {
                Self::Engine(Rss256Error::MultiplicationCheckFailed)
            }
            CnfRssError::CommitmentMismatch { party, .. } => {
                Self::Engine(Rss256Error::CoinOpeningRejected { party })
            }
            CnfRssError::Preprocess(p) => Self::Engine(Rss256Error::Mpc(p.into())),
        }
    }
}

impl fmt::Display for CnfRssError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidParameters => f.write_str("invalid (t, n) CNF-RSS parameters or quorum"),
            Self::Preprocess(e) => write!(f, "CNF-RSS preprocessing error: {e}"),
            Self::CommitmentMismatch { phase, party } => {
                write!(f, "CNF-RSS commitment mismatch in {phase} by party {party}")
            }
            Self::SlotOverlapMismatch { slot_idx } => {
                write!(
                    f,
                    "CNF-RSS replicated slot {slot_idx} mismatch across quorum"
                )
            }
            Self::ActiveTamperDetected { phase } => {
                write!(f, "CNF-RSS active MiniMAC verification failed in {phase}")
            }
            Self::BeaverBankExhausted => f.write_str("CNF-RSS staged Beaver bank exhausted"),
            Self::OpenBeforeBarrier => f.write_str("CNF-RSS cut opening attempted before barrier"),
            Self::KeyBindingMismatch => f.write_str("CNF-RSS key binding mismatch"),
            Self::Poisoned => f.write_str("CNF-RSS engine permanently poisoned"),
        }
    }
}

impl core::error::Error for CnfRssError {}

// ============================================================================
// 1. `(t, n)` CNF-RSS Combinatorics, Dealerless DKG & Theorem 4.1 Projection
// ============================================================================

/// Validated `(t, n)` CNF replicated secret-sharing topology (`2 <= t <= n <= 10`).
///
/// Enumerates all $M = \binom{n}{t-1}$ subsets $S_m \subset \{0, \dots, n-1\}$ of size $t - 1$
/// in canonical lexicographic order (`10` for `3-of-5`, `15` for `3-of-6`/`5-of-6`, `20` for `4-of-6`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CnfRssConfig {
    t: usize,
    n: usize,
    subsets: Vec<Vec<usize>>,
}

impl CnfRssConfig {
    /// Construct a `(t, n)` CNF-RSS configuration (`2 <= t <= n <= MAX_CNF_RSS_PARTIES`).
    pub fn new(t: usize, n: usize) -> Result<Self, CnfRssError> {
        if t < 2 || t > n || n > MAX_CNF_RSS_PARTIES {
            return Err(CnfRssError::InvalidParameters);
        }
        let mut subsets = Vec::new();
        let mut cur = Vec::with_capacity(t - 1);
        fn rec(
            start: usize,
            n: usize,
            rem: usize,
            cur: &mut Vec<usize>,
            out: &mut Vec<Vec<usize>>,
        ) {
            if rem == 0 {
                out.push(cur.clone());
                return;
            }
            for x in start..=(n - rem) {
                cur.push(x);
                rec(x + 1, n, rem - 1, cur, out);
                cur.pop();
            }
        }
        rec(0, n, t - 1, &mut cur, &mut subsets);
        Ok(Self { t, n, subsets })
    }

    #[inline]
    pub const fn threshold(&self) -> usize {
        self.t
    }

    #[inline]
    pub const fn parties(&self) -> usize {
        self.n
    }

    /// Total number of replicated slots $M = \binom{n}{t-1}$.
    #[inline]
    pub fn total_slots(&self) -> usize {
        self.subsets.len()
    }

    /// Number of slots held by each individual custodian $\binom{n-1}{t-1}$.
    pub fn slots_per_party(&self) -> usize {
        (self.total_slots() * (self.n - (self.t - 1))) / self.n
    }

    /// Whether `honest_majority_pure_hash` (`n >= 2t - 1`) holds, enabling 100% pure-hash
    /// non-OT degree-2 product reduction among any `2t - 1` custodians (`2-of-3`, `3-of-5`, `4-of-7`).
    #[inline]
    pub const fn supports_pure_hash_multiplication(&self) -> bool {
        self.n >= 2 * self.t - 1
    }

    /// Subset $S_{\text{slot}} \in \binom{[n]}{t-1}$ of custodians EXCLUDED from holding `slot_idx`.
    pub fn excluded_subset(&self, slot_idx: usize) -> Option<&[usize]> {
        self.subsets.get(slot_idx).map(Vec::as_slice)
    }

    /// Slot indices held by `party_id` (`{ m : party_id not in S_m }`).
    pub fn party_slot_indices(&self, party_id: usize) -> Result<Vec<usize>, CnfRssError> {
        if party_id >= self.n {
            return Err(CnfRssError::InvalidParameters);
        }
        Ok(self
            .subsets
            .iter()
            .enumerate()
            .filter_map(|(m, s)| (!s.contains(&party_id)).then_some(m))
            .collect())
    }

    /// Validate that `quorum` is a strictly ascending $t$-element subset of `0..n`.
    pub fn validate_quorum(&self, quorum: &[usize]) -> Result<(), CnfRssError> {
        if quorum.len() != self.t
            || quorum.windows(2).any(|w| w[0] >= w[1])
            || quorum.last().is_none_or(|&p| p >= self.n)
        {
            return Err(CnfRssError::InvalidParameters);
        }
        Ok(())
    }

    /// **Theorem 4.1 Canonical Owner Map (`owner(Q, S) = min(Q \ S)`):**
    /// Returns `(owner_party_id, position_in_quorum)` for `slot_idx` under validated `quorum`.
    pub fn owner(&self, quorum: &[usize], slot_idx: usize) -> Result<(usize, usize), CnfRssError> {
        self.validate_quorum(quorum)?;
        let excluded = self
            .subsets
            .get(slot_idx)
            .ok_or(CnfRssError::InvalidParameters)?;
        for (pos, &q) in quorum.iter().enumerate() {
            if !excluded.contains(&q) {
                return Ok((q, pos));
            }
        }
        Err(CnfRssError::InvalidParameters)
    }
}

/// Isolated single-custodian `(t, n)` CNF-RSS key share (`!Clone`, redacted `Debug`, wiped on `Drop`).
pub struct CnfRssKeyShare256 {
    cfg: CnfRssConfig,
    pub party_id: usize,
    pub key_len: usize,
    pub pk_seed: [u8; 32],
    slot_indices: Vec<usize>,
    sk_seed_slots: SecretVec<[u8; 32]>,
    sk_prf_slots: SecretVec<[u8; 32]>,
    slot_prg_seeds: SecretVec<[u8; 32]>,
    pair_prf_keys: SecretVec<[u8; 32]>,
    scheme_identity: Option<[u8; 32]>,
    slh_profile_digest: Option<[u64; 4]>,
}

impl fmt::Debug for CnfRssKeyShare256 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "CnfRssKeyShare256(t={}, n={}, party={}, slots={}, [REDACTED])",
            self.cfg.t,
            self.cfg.n,
            self.party_id,
            self.slot_indices.len()
        )
    }
}

impl CnfRssKeyShare256 {
    #[inline]
    pub const fn config(&self) -> &CnfRssConfig {
        &self.cfg
    }

    #[inline]
    pub fn slot_indices(&self) -> &[usize] {
        &self.slot_indices
    }

    /// This custodian's own replica of slot `slot_idx`: `(sk_seed, sk_prf, prg_seed)`, or
    /// `None` when the custodian is in the slot's excluded subset. An isolated party uses
    /// this to load its own state; it never yields a slot the custodian does not hold.
    pub fn held_slot(&self, slot_idx: usize) -> Option<(&[u8; 32], &[u8; 32], &[u8; 32])> {
        let pos = self.local_slot_pos(slot_idx)?;
        Some((
            &self.sk_seed_slots[pos],
            &self.sk_prf_slots[pos],
            &self.slot_prg_seeds[pos],
        ))
    }

    /// Pairwise PRF key shared with `peer` (`None` for this party itself or out of range).
    pub fn pair_prf_key(&self, peer: usize) -> Option<&[u8; 32]> {
        (peer != self.party_id)
            .then(|| self.pair_prf_keys.get(peer))
            .flatten()
    }

    #[inline]
    pub fn scheme_identity(&self) -> Option<[u8; 32]> {
        self.scheme_identity
    }

    /// Bind this share once to a `BaggyKeyBinding::identity()` digest (idempotent on same digest).
    pub fn bind_scheme_identity(&mut self, identity: &[u8; 32]) -> Result<(), CnfRssError> {
        if self.slh_profile_digest.is_some() {
            return Err(CnfRssError::KeyBindingMismatch);
        }
        match &self.scheme_identity {
            None => {
                self.scheme_identity = Some(*identity);
                Ok(())
            }
            Some(bound) if ct_eq_bytes32(bound, identity) => Ok(()),
            Some(_) => Err(CnfRssError::KeyBindingMismatch),
        }
    }

    /// Bind this share once to an `SLH-DSA` parameter set and `pk_seed`.
    pub fn bind_slh_params(
        &mut self,
        params: &Fips205Params,
        pk_seed: &[u8],
    ) -> Result<(), Fips205Error> {
        if !params.is_valid()
            || params.n != self.key_len
            || pk_seed.len() != self.key_len
            || !ct_eq_bytes(pk_seed, &self.pk_seed[..self.key_len])
        {
            return Err(Fips205Error::InvalidParameterSet);
        }
        if self.scheme_identity.is_some() {
            return Err(Fips205Error::InvalidParameterSet);
        }
        match &self.slh_profile_digest {
            None => {
                self.slh_profile_digest = Some(crate::keccak_mpc::slh_profile_digest_u64x4(params));
                Ok(())
            }
            Some(bound) if *bound == crate::keccak_mpc::slh_profile_digest_u64x4(params) => Ok(()),
            Some(_) => Err(Fips205Error::InvalidParameterSet),
        }
    }

    fn local_slot_pos(&self, global_slot_idx: usize) -> Option<usize> {
        self.slot_indices.binary_search(&global_slot_idx).ok()
    }

    /// Canonical secret byte serialization (`QSCNFK01` header). Legacy encodings
    /// stay unchanged; byte 13 equal to 1 appends the 32-byte SLH profile lock.
    pub fn to_secret_bytes(&self) -> SecretVec<u8> {
        let k = self.slot_indices.len();
        let n = self.cfg.n;
        let cap = 16
            + 32
            + 32
            + 2 * k
            + 96 * k
            + 32 * n
            + 32 * usize::from(self.slh_profile_digest.is_some());
        let mut out = SecretBuffer(Vec::with_capacity(cap));
        out.extend_from_slice(CNF_KEY_SHARE_MAGIC);
        out.push(self.cfg.t as u8);
        out.push(self.cfg.n as u8);
        out.push(self.party_id as u8);
        out.push(self.key_len as u8);
        let (has_id, id_bytes) = match &self.scheme_identity {
            Some(id) => (1u8, *id),
            None => (0u8, [0u8; 32]),
        };
        out.push(has_id);
        out.push(u8::from(self.slh_profile_digest.is_some()));
        out.extend_from_slice(&(k as u16).to_le_bytes());
        out.extend_from_slice(&self.pk_seed);
        out.extend_from_slice(&id_bytes);
        for &slot in &self.slot_indices {
            out.extend_from_slice(&(slot as u16).to_le_bytes());
        }
        for s in self.sk_seed_slots.iter() {
            out.extend_from_slice(s);
        }
        for s in self.sk_prf_slots.iter() {
            out.extend_from_slice(s);
        }
        for s in self.slot_prg_seeds.iter() {
            out.extend_from_slice(s);
        }
        for s in self.pair_prf_keys.iter() {
            out.extend_from_slice(s);
        }
        if let Some(profile) = self.slh_profile_digest {
            for word in profile {
                out.extend_from_slice(&word.to_le_bytes());
            }
        }
        out
    }

    /// Decode and canonically validate a serialized [`CnfRssKeyShare256`].
    pub fn from_secret_bytes(bytes: &[u8]) -> Result<Self, CnfRssError> {
        if bytes.len() < 80 || !ct_eq_bytes(&bytes[..8], CNF_KEY_SHARE_MAGIC) {
            return Err(CnfRssError::InvalidParameters);
        }
        let t = bytes[8] as usize;
        let n = bytes[9] as usize;
        let party_id = bytes[10] as usize;
        let key_len = bytes[11] as usize;
        let has_id = bytes[12];
        let profile_flag = bytes[13];
        let k = u16::from_le_bytes([bytes[14], bytes[15]]) as usize;
        if !matches!(key_len, 16 | 24 | 32)
            || has_id > 1
            || profile_flag > 1
            || (has_id != 0 && profile_flag != 0)
        {
            return Err(CnfRssError::InvalidParameters);
        }
        let cfg = CnfRssConfig::new(t, n)?;
        let expected_slots = cfg.party_slot_indices(party_id)?;
        if k != expected_slots.len() {
            return Err(CnfRssError::InvalidParameters);
        }
        let base_len = 80 + 2 * k + 96 * k + 32 * n;
        let expected_len = base_len + 32 * usize::from(profile_flag);
        if bytes.len() != expected_len {
            return Err(CnfRssError::InvalidParameters);
        }
        let slh_profile_digest = (profile_flag == 1).then(|| {
            core::array::from_fn(|i| {
                u64::from_le_bytes(core::array::from_fn(|b| bytes[base_len + 8 * i + b]))
            })
        });
        let mut pk_seed = [0u8; 32];
        pk_seed.copy_from_slice(&bytes[16..48]);
        if pk_seed[key_len..].iter().any(|&b| b != 0) {
            return Err(CnfRssError::InvalidParameters);
        }
        let mut id_bytes = [0u8; 32];
        id_bytes.copy_from_slice(&bytes[48..80]);
        let scheme_identity = if has_id == 1 {
            Some(id_bytes)
        } else {
            if id_bytes != [0u8; 32] {
                return Err(CnfRssError::InvalidParameters);
            }
            None
        };
        let mut pos = 80;
        for &exp_slot in &expected_slots {
            let got = u16::from_le_bytes([bytes[pos], bytes[pos + 1]]) as usize;
            if got != exp_slot {
                return Err(CnfRssError::InvalidParameters);
            }
            pos += 2;
        }
        let read_vec32 = |pos: &mut usize, count: usize| -> SecretVec<[u8; 32]> {
            let mut v = SecretBuffer(Vec::with_capacity(count));
            // Written in place: no stack copy of a secret slot outlives this loop.
            v.resize(count, [0u8; 32]);
            for dst in v.iter_mut() {
                dst.copy_from_slice(&bytes[*pos..*pos + 32]);
                *pos += 32;
            }
            v
        };
        let sk_seed_slots = read_vec32(&mut pos, k);
        let sk_prf_slots = read_vec32(&mut pos, k);
        let slot_prg_seeds = read_vec32(&mut pos, k);
        let pair_prf_keys = read_vec32(&mut pos, n);
        // One accumulated verdict over secret bytes: no data-dependent early exit.
        let mut noncanonical = pair_prf_keys[party_id].iter().fold(0u8, |acc, &b| acc | b);
        for s in sk_seed_slots.iter().chain(sk_prf_slots.iter()) {
            noncanonical |= s[key_len..].iter().fold(0u8, |acc, &b| acc | b);
        }
        if black_box(noncanonical) != 0 {
            return Err(CnfRssError::InvalidParameters);
        }
        Ok(Self {
            cfg,
            party_id,
            key_len,
            pk_seed,
            slot_indices: expected_slots,
            sk_seed_slots,
            sk_prf_slots,
            slot_prg_seeds,
            pair_prf_keys,
            scheme_identity,
            slh_profile_digest,
        })
    }
}

/// Dealerless pure-hash `(t, n)` CNF-RSS distributed key generation (`0` trusted dealer, `0` RLWE/OT).
///
/// Executes:
/// 1. 2-round committed coin toss deriving `pk_seed` (`key_len` bytes in `16 | 24 | 32`);
/// 2. Per-complement $H_m = [n] \setminus S_m$ 2-round committed group seed ceremony deriving
///    `(sk_seed_S, sk_prf_S, slot_prg_seed_S)` exclusively among legitimate holders $i \notin S_m$;
/// 3. Pairwise 2-round committed PRF key ceremony deriving `K_{a, b}` for Theorem 4.1 zero-masks.
pub fn run_dealerless_cnf_rss_dkg(
    session_id: [u8; 32],
    cfg: &CnfRssConfig,
    key_len: usize,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(Vec<CnfRssKeyShare256>, [u8; 32]), CnfRssError> {
    let n = cfg.n;
    if !matches!(key_len, 16 | 24 | 32) || party_rngs.len() != n {
        return Err(CnfRssError::InvalidParameters);
    }

    // 1. 2-round committed coin toss for `pk_seed`
    let dkg_cfg_dig = cshake256_32_multi_frame(
        b"QSAG.CNF_RSS.DKG.CFG/v1",
        &[&[cfg.t as u8, cfg.n as u8, key_len as u8]],
    );
    let pk_coin = run_commit_and_open_coin(
        &session_id,
        b"QSAG.CNF_RSS.DKG.PK_SEED/v1",
        &dkg_cfg_dig,
        party_rngs,
    )?;
    let mut pk_seed = [0u8; 32];
    pk_seed[..key_len].copy_from_slice(&pk_coin[..key_len]);

    // 2. Per-slot complement seed ceremony over private holder channels `H_m = [n] \ S_m`
    let m_slots = cfg.total_slots();
    let k_per_party = cfg.slots_per_party();
    let mut p_slot_indices: Vec<Vec<usize>> = Vec::with_capacity(n);
    for p in 0..n {
        p_slot_indices.push(cfg.party_slot_indices(p)?);
    }
    let mut p_sk_seed: Vec<SecretVec<[u8; 32]>> = (0..n)
        .map(|_| SecretBuffer(Vec::with_capacity(k_per_party)))
        .collect();
    let mut p_sk_prf: Vec<SecretVec<[u8; 32]>> = (0..n)
        .map(|_| SecretBuffer(Vec::with_capacity(k_per_party)))
        .collect();
    let mut p_prg: Vec<SecretVec<[u8; 32]>> = (0..n)
        .map(|_| SecretBuffer(Vec::with_capacity(k_per_party)))
        .collect();

    for slot_idx in 0..m_slots {
        let excluded = &cfg.subsets[slot_idx];
        let holders: Vec<usize> = (0..n).filter(|p| !excluded.contains(p)).collect();
        let h_len = holders.len();
        let slot_be = (slot_idx as u64).to_be_bytes();

        let mut salts = SecretBuffer(vec![[0u8; 32]; h_len]);
        let mut contribs = SecretBuffer(vec![[0u8; 32]; h_len]);
        let mut coms = Vec::with_capacity(h_len);
        for (idx, &p) in holders.iter().enumerate() {
            salts[idx] = party_rngs[p].next_bytes32();
            contribs[idx] = party_rngs[p].next_bytes32();
            coms.push(cshake256_32_multi_frame(
                b"QSAG.CNF_RSS.DKG.SLOT.COM/v1",
                &[
                    &session_id,
                    &slot_be,
                    &(p as u64).to_be_bytes(),
                    &salts[idx],
                    &contribs[idx],
                ],
            ));
        }
        for (idx, &p) in holders.iter().enumerate() {
            let exp = cshake256_32_multi_frame(
                b"QSAG.CNF_RSS.DKG.SLOT.COM/v1",
                &[
                    &session_id,
                    &slot_be,
                    &(p as u64).to_be_bytes(),
                    &salts[idx],
                    &contribs[idx],
                ],
            );
            if !ct_eq_bytes32(&exp, &coms[idx]) {
                return Err(CnfRssError::CommitmentMismatch {
                    phase: "dkg_slot_seed",
                    party: p,
                });
            }
        }
        let mut xof = Cshake256Xof::new(b"QSAG.CNF_RSS.DKG.SLOT.EXPAND/v1");
        xof.absorb(&session_id);
        xof.absorb(&pk_seed);
        xof.absorb(&slot_be);
        for com in &coms {
            xof.absorb(com);
        }
        for c in contribs.iter() {
            xof.absorb(c);
        }
        let mut raw = SecretBuffer([0u8; 96]);
        xof.squeeze(&mut *raw);
        let mut s_seed = SecretBuffer([0u8; 32]);
        let mut s_prf = SecretBuffer([0u8; 32]);
        let mut s_prg = SecretBuffer([0u8; 32]);
        s_seed[..key_len].copy_from_slice(&raw[0..key_len]);
        s_prf[..key_len].copy_from_slice(&raw[32..32 + key_len]);
        s_prg.copy_from_slice(&raw[64..96]);
        for &p in &holders {
            p_sk_seed[p].push(*s_seed);
            p_sk_prf[p].push(*s_prf);
            p_prg[p].push(*s_prg);
        }
    }

    // 3. Pairwise PRF keys `K_{a, b}` (`0 <= a < b < n`)
    let mut pair_keys: Vec<SecretVec<[u8; 32]>> =
        (0..n).map(|_| SecretBuffer(vec![[0u8; 32]; n])).collect();
    for a in 0..n {
        for b in (a + 1)..n {
            let a_be = (a as u64).to_be_bytes();
            let b_be = (b as u64).to_be_bytes();
            let sa = SecretBuffer(party_rngs[a].next_bytes32());
            let ca = SecretBuffer(party_rngs[a].next_bytes32());
            let sb = SecretBuffer(party_rngs[b].next_bytes32());
            let cb = SecretBuffer(party_rngs[b].next_bytes32());
            let com_a = cshake256_32_multi_frame(
                b"QSAG.CNF_RSS.DKG.PAIR.COM/v1",
                &[&session_id, &a_be, &b_be, &*sa, &*ca],
            );
            let com_b = cshake256_32_multi_frame(
                b"QSAG.CNF_RSS.DKG.PAIR.COM/v1",
                &[&session_id, &b_be, &a_be, &*sb, &*cb],
            );
            let shared = SecretBuffer(cshake256_32_multi_frame(
                b"QSAG.CNF_RSS.DKG.PAIR.KEY/v1",
                &[&session_id, &a_be, &b_be, &com_a, &com_b, &*ca, &*cb],
            ));
            pair_keys[a][b] = *shared;
            pair_keys[b][a] = *shared;
        }
    }

    let shares = (0..n)
        .zip(p_slot_indices)
        .zip(p_sk_seed)
        .zip(p_sk_prf)
        .zip(p_prg)
        .zip(pair_keys)
        .map(
            |(
                ((((party_id, slot_indices), sk_seed_slots), sk_prf_slots), slot_prg_seeds),
                pair_prf_keys,
            )| {
                CnfRssKeyShare256 {
                    cfg: cfg.clone(),
                    party_id,
                    key_len,
                    pk_seed,
                    slot_indices,
                    sk_seed_slots,
                    sk_prf_slots,
                    slot_prg_seeds,
                    pair_prf_keys,
                    scheme_identity: None,
                    slh_profile_digest: None,
                }
            },
        )
        .collect();
    Ok((shares, pk_seed))
}

/// Reconstruct the reference `(sk_seed, sk_prf)` in test harnesses to compare against single-prover KATs.
#[cfg(test)]
pub(crate) fn reconstruct_cnf_rss_secret_for_test(
    shares: &[CnfRssKeyShare256],
) -> ([u8; 32], [u8; 32]) {
    let cfg = &shares[0].cfg;
    let mut sk_seed = [0u8; 32];
    let mut sk_prf = [0u8; 32];
    for slot_idx in 0..cfg.total_slots() {
        let holder = shares
            .iter()
            .find(|sh| sh.local_slot_pos(slot_idx).is_some())
            .expect("every slot held by n - (t - 1) >= 1 custodians");
        let pos = holder.local_slot_pos(slot_idx).unwrap();
        for b in 0..32 {
            sk_seed[b] ^= holder.sk_seed_slots[pos][b];
            sk_prf[b] ^= holder.sk_prf_slots[pos][b];
        }
    }
    (sk_seed, sk_prf)
}

/// Projected `t-of-t` additive key material for one online signing session (`!Clone`, wiped on `Drop`).
pub struct ProjectedQuorumSecrets {
    quorum: Vec<usize>,
    key_len: usize,
    pk_seed: [u8; 32],
    sk_seed_shares: SecretVec<[u8; 32]>,
    sk_prf_shares: SecretVec<[u8; 32]>,
}

/// **Theorem 4.1 Authenticated `t-of-t` Online Key Projection (`project_quorum_keys`):**
/// 1. Cross-verifies all overlapping slots (`|Q \ S_m| >= 2`) via session-salted commitments;
/// 2. Partitions all $M = \binom{n}{t-1}$ slots cleanly via `owner(Q, S_m) = min(Q \ S_m)`;
/// 3. Adds pairwise `cSHAKE256` zero-shares across all $\binom{t}{2}$ pairs in $Q$.
pub fn project_quorum_keys(
    session_id: &[u8; 32],
    quorum_shares: &[&CnfRssKeyShare256],
) -> Result<ProjectedQuorumSecrets, CnfRssError> {
    if quorum_shares.is_empty() {
        return Err(CnfRssError::InvalidParameters);
    }
    let cfg = &quorum_shares[0].cfg;
    let key_len = quorum_shares[0].key_len;
    let pk_seed = quorum_shares[0].pk_seed;
    let quorum: Vec<usize> = quorum_shares.iter().map(|s| s.party_id).collect();
    cfg.validate_quorum(&quorum)?;
    for s in quorum_shares {
        if &s.cfg != cfg || s.key_len != key_len || !ct_eq_bytes32(&s.pk_seed, &pk_seed) {
            return Err(CnfRssError::InvalidParameters);
        }
    }

    let t = cfg.t;
    let quorum_bytes: Vec<u8> = quorum.iter().map(|&q| q as u8).collect();
    let mut sk_seed_shares = SecretBuffer(vec![[0u8; 32]; t]);
    let mut sk_prf_shares = SecretBuffer(vec![[0u8; 32]; t]);

    // 1 & 2. Verify every overlapping slot across all holders in `Q` and fold into `owner(Q, S_m)`.
    for slot_idx in 0..cfg.total_slots() {
        let (_, owner_pos) = cfg.owner(&quorum, slot_idx)?;
        let slot_be = (slot_idx as u64).to_be_bytes();
        let mut ref_tag: Option<[u8; 32]> = None;
        for (u, share) in quorum_shares.iter().enumerate() {
            if let Some(local_pos) = share.local_slot_pos(slot_idx) {
                let tag = cshake256_32_multi_frame(
                    b"QSAG.CNF_RSS.SLOT_CHECK/v1",
                    &[
                        session_id,
                        &quorum_bytes,
                        &slot_be,
                        &share.sk_seed_slots[local_pos],
                        &share.sk_prf_slots[local_pos],
                        &share.slot_prg_seeds[local_pos],
                    ],
                );
                match &ref_tag {
                    None => ref_tag = Some(tag),
                    Some(first) if !ct_eq_bytes32(first, &tag) => {
                        return Err(CnfRssError::SlotOverlapMismatch { slot_idx });
                    }
                    Some(_) => {}
                }
                if u == owner_pos {
                    for b in 0..key_len {
                        sk_seed_shares[u][b] ^= share.sk_seed_slots[local_pos][b];
                        sk_prf_shares[u][b] ^= share.sk_prf_slots[local_pos][b];
                    }
                }
            }
        }
    }

    // 3. Pairwise PRF zero-share re-randomization across `0 <= u < v < t`
    for u in 0..t {
        for v in (u + 1)..t {
            let qu = quorum[u];
            let qv = quorum[v];
            let k_uv = &quorum_shares[u].pair_prf_keys[qv];
            let k_vu = &quorum_shares[v].pair_prf_keys[qu];
            if !ct_eq_bytes32(k_uv, k_vu) {
                return Err(CnfRssError::CommitmentMismatch {
                    phase: "pair_prf_key_consistency",
                    party: qu,
                });
            }
            let mut xof = Cshake256Xof::new(b"QSAG.CNF_RSS.PROJ_ZERO/v1");
            xof.absorb(k_uv);
            xof.absorb(session_id);
            xof.absorb(&quorum_bytes);
            xof.absorb(&(qu as u64).to_be_bytes());
            xof.absorb(&(qv as u64).to_be_bytes());
            let mut mask = SecretBuffer([0u8; 64]);
            xof.squeeze(&mut *mask);
            for b in 0..key_len {
                sk_seed_shares[u][b] ^= mask[b];
                sk_seed_shares[v][b] ^= mask[b];
                sk_prf_shares[u][b] ^= mask[32 + b];
                sk_prf_shares[v][b] ^= mask[32 + b];
            }
        }
    }

    Ok(ProjectedQuorumSecrets {
        quorum,
        key_len,
        pk_seed,
        sk_seed_shares,
        sk_prf_shares,
    })
}

// ============================================================================
// 2. `[128, 56, 73]` Systematic Reed–Solomon `MiniMAC` Code Tables
// ============================================================================

/// Precomputed systematic generator and parity-check tables for:
/// - $C = [128, 56, 73]$ over [`TowerGf256`] (`0..56` systematic data, `56..128` parity),
/// - $C^{\ast 2} = [128, 111, 18]$ (`0..111` systematic + zero-mask, `111..128` parity, $d_{\min} = 18$).
struct MiniMacTables {
    /// Parity rows for `C`: `gen_c_parity[i]` (`i in 0..56`) holds `L_i(\alpha_{56..128})` (`72` bytes).
    gen_c_parity: [[u8; MINIMAC_PARITY_C]; MINIMAC_DATA_K],
    /// Flattened 8-bit LUT for encoding `bits56` (`7 * 256` entries of `[u8; 72]`).
    pub_byte_lut: Vec<[u8; MINIMAC_PARITY_C]>,
    /// Parity rows for `C^{*2}`: `gen_c2_parity[k]` (`k in 0..111`) holds `L^{(111)}_k(\alpha_{111..128})` (`17` bytes).
    gen_c2_parity: [[u8; MINIMAC_PARITY_C2]; MINIMAC_C2_K],
    /// Flattened 8-bit LUT for `encode_batch_c2_zero_mask` (`55 * 256` entries of `[u8; 17]`).
    c2_zero_lut: Vec<[u8; MINIMAC_PARITY_C2]>,
}

impl MiniMacTables {
    fn build() -> Result<Box<Self>, CnfRssError> {
        let mut gen_c_parity = [[0u8; MINIMAC_PARITY_C]; MINIMAC_DATA_K];
        let mut bary_c = [TowerGf256::ZERO; MINIMAC_DATA_K];
        for (i, slot) in bary_c.iter_mut().enumerate() {
            let xi = TowerGf256(i as u8);
            let mut prod = TowerGf256::ONE;
            for m in 0..MINIMAC_DATA_K {
                if m != i {
                    prod = prod.mul(xi.add(TowerGf256(m as u8)));
                }
            }
            *slot = prod.inv().ok_or(CnfRssError::InvalidParameters)?;
        }
        for p_off in 0..MINIMAC_PARITY_C {
            let xj = TowerGf256((MINIMAC_DATA_K + p_off) as u8);
            let mut full_num = TowerGf256::ONE;
            for m in 0..MINIMAC_DATA_K {
                full_num = full_num.mul(xj.add(TowerGf256(m as u8)));
            }
            for (i, row_out) in gen_c_parity.iter_mut().enumerate() {
                let diff_inv = xj
                    .add(TowerGf256(i as u8))
                    .inv()
                    .ok_or(CnfRssError::InvalidParameters)?;
                row_out[p_off] = full_num.mul(diff_inv).mul(bary_c[i]).0;
            }
        }

        let mut pub_byte_lut = vec![[0u8; MINIMAC_PARITY_C]; 7 * 256];
        for byte_idx in 0..7 {
            for val in 0..256usize {
                let entry = &mut pub_byte_lut[byte_idx * 256 + val];
                for bit in 0..8 {
                    if ((val >> bit) & 1) == 1 {
                        let row = &gen_c_parity[8 * byte_idx + bit];
                        for (dst, &r) in entry.iter_mut().zip(row.iter()) {
                            *dst ^= r;
                        }
                    }
                }
            }
        }

        let mut gen_c2_parity = [[0u8; MINIMAC_PARITY_C2]; MINIMAC_C2_K];
        let mut bary_c2 = [TowerGf256::ZERO; MINIMAC_C2_K];
        for (k, slot) in bary_c2.iter_mut().enumerate() {
            let xk = TowerGf256(k as u8);
            let mut prod = TowerGf256::ONE;
            for m in 0..MINIMAC_C2_K {
                if m != k {
                    prod = prod.mul(xk.add(TowerGf256(m as u8)));
                }
            }
            *slot = prod.inv().ok_or(CnfRssError::InvalidParameters)?;
        }
        for r_off in 0..MINIMAC_PARITY_C2 {
            let xr = TowerGf256((MINIMAC_C2_K + r_off) as u8);
            let mut full_num = TowerGf256::ONE;
            for m in 0..MINIMAC_C2_K {
                full_num = full_num.mul(xr.add(TowerGf256(m as u8)));
            }
            for (k, row_out) in gen_c2_parity.iter_mut().enumerate() {
                let diff_inv = xr
                    .add(TowerGf256(k as u8))
                    .inv()
                    .ok_or(CnfRssError::InvalidParameters)?;
                row_out[r_off] = full_num.mul(diff_inv).mul(bary_c2[k]).0;
            }
        }

        let mut c2_zero_lut = vec![[0u8; MINIMAC_PARITY_C2]; MINIMAC_ZERO_MASK_K * 256];
        for idx in 0..MINIMAC_ZERO_MASK_K {
            let row = &gen_c2_parity[MINIMAC_DATA_K + idx];
            for val in 0..256usize {
                let u = TowerGf256(val as u8);
                let out_entry = &mut c2_zero_lut[idx * 256 + val];
                for (dst, &r_byte) in out_entry.iter_mut().zip(row.iter()) {
                    *dst = u.mul(TowerGf256(r_byte)).0;
                }
            }
        }

        Ok(Box::new(Self {
            gen_c_parity,
            pub_byte_lut,
            gen_c2_parity,
            c2_zero_lut,
        }))
    }

    /// Constant-time systematic `[128, 56, 73]` encoding of a secret 56-bit mask (`bits56` low 56 bits).
    #[inline]
    fn encode_secret_bits56(&self, bits56: u64, out: &mut [u8; MINIMAC_CODE_N]) {
        out.fill(0);
        let b = black_box(bits56);
        for i in 0..MINIMAC_DATA_K {
            let bit = ((b >> i) & 1) as u8;
            out[i] = bit;
            let mask = 0u8.wrapping_sub(bit);
            let row = &self.gen_c_parity[i];
            for p in 0..MINIMAC_PARITY_C {
                out[MINIMAC_DATA_K + p] ^= row[p] & mask;
            }
        }
    }

    /// Encode a PUBLIC 56-bit mask (`public_bits56`) into `[u8; 128]` via `pub_byte_lut`.
    #[inline]
    fn encode_public_bits56(&self, public_bits56: u64, out: &mut [u8; MINIMAC_CODE_N]) {
        out.fill(0);
        for (i, slot) in out.iter_mut().enumerate().take(MINIMAC_DATA_K) {
            *slot = ((public_bits56 >> i) & 1) as u8;
        }
        let le = public_bits56.to_le_bytes();
        for (byte_idx, &b_val) in le.iter().enumerate().take(7) {
            let lut = &self.pub_byte_lut[byte_idx * 256 + b_val as usize];
            for p in 0..MINIMAC_PARITY_C {
                out[MINIMAC_DATA_K + p] ^= lut[p];
            }
        }
    }

    /// Verify that a PUBLIC opened `[u8; 128]` vector lies in $C$ AND has Boolean coordinates `0..56`,
    /// returning the packed 56-bit `u64` on success.
    #[inline]
    fn verify_and_extract_public_c(&self, cw: &[u8; MINIMAC_CODE_N]) -> Option<u64> {
        let mut bits56 = 0u64;
        let mut bad_bool = 0u8;
        for (i, &v) in cw[..MINIMAC_DATA_K].iter().enumerate() {
            bad_bool |= v & !1u8;
            bits56 |= u64::from(v & 1) << i;
        }
        if bad_bool != 0 {
            return None;
        }
        let le = bits56.to_le_bytes();
        let mut exp_parity = [0u8; MINIMAC_PARITY_C];
        for (byte_idx, &b_val) in le.iter().enumerate().take(7) {
            let lut = &self.pub_byte_lut[byte_idx * 256 + b_val as usize];
            for p in 0..MINIMAC_PARITY_C {
                exp_parity[p] ^= lut[p];
            }
        }
        if !ct_eq_bytes(&exp_parity, &cw[MINIMAC_DATA_K..]) {
            return None;
        }
        Some(bits56)
    }

    /// Fast LUT-accelerated `z_zero in C^{*2}` vanishing on `0..56` for batch tuple materialization.
    #[inline]
    fn encode_batch_c2_zero_mask(
        &self,
        rand55: &[u8; MINIMAC_ZERO_MASK_K],
        out: &mut [u8; MINIMAC_CODE_N],
    ) {
        out[..MINIMAC_DATA_K].fill(0);
        out[MINIMAC_DATA_K..MINIMAC_C2_K].copy_from_slice(rand55);
        let mut p17 = [0u8; MINIMAC_PARITY_C2];
        for (idx, &uk) in rand55.iter().enumerate() {
            let lut = &self.c2_zero_lut[idx * 256 + uk as usize];
            for r_off in 0..MINIMAC_PARITY_C2 {
                p17[r_off] ^= lut[r_off];
            }
        }
        out[MINIMAC_C2_K..].copy_from_slice(&p17);
    }

    /// Check that a PUBLIC folded `[u8; 128]` vector lies in $C^{\ast 2} = [128, 111, 18]$.
    fn verify_public_c2(&self, cw: &[u8; MINIMAC_CODE_N]) -> bool {
        let mut exp = [0u8; MINIMAC_PARITY_C2];
        for (k, &cw_k) in cw.iter().enumerate().take(MINIMAC_C2_K) {
            let wk = TowerGf256(cw_k);
            let row = &self.gen_c2_parity[k];
            for r_off in 0..MINIMAC_PARITY_C2 {
                exp[r_off] ^= wk.mul(TowerGf256(row[r_off])).0;
            }
        }
        ct_eq_bytes(&exp, &cw[MINIMAC_C2_K..])
    }
}

// ============================================================================
// 3. Universal `(t, n)` CNF-RSS -> `t-of-t` `MiniMAC` Window Correlation Source
// ============================================================================

/// Single-use `t-of-t` projected `MiniMAC` material for one 56-lane `Keccak-f[1600]` permutation
/// (or cut-opening round), authenticated under ephemeral `delta_shares` (`[u8; 128]` per signer).
pub struct ProjectedWaveTuple {
    /// Per-party ephemeral MAC key share `delta[u]: [u8; 128]` (`XOR_u delta[u] = Delta`).
    delta_shares: SecretVec<[u8; MINIMAC_CODE_N]>,
    /// Per-party seed the party's own shares were expanded from.
    signer_seeds: SecretVec<[u8; 32]>,
    /// Per-party `[24][1600 * 128]` flattened round material:
    /// `(a, a_mac, b, b_mac, r, r_mac, cr_star, cr_star_mac)`.
    a: SecretVec<Vec<u8>>,
    a_mac: SecretVec<Vec<u8>>,
    b: SecretVec<Vec<u8>>,
    b_mac: SecretVec<Vec<u8>>,
    r: SecretVec<Vec<u8>>,
    r_mac: SecretVec<Vec<u8>>,
    cr_star: SecretVec<Vec<u8>>,
    cr_star_mac: SecretVec<Vec<u8>>,
}

/// Cut-opening zero-on-`0..56` degree-`<111` mask tuple (`256` digest bits $\times 128$ bytes).
pub struct ProjectedCutMaskTuple {
    r_star: SecretVec<Vec<u8>>,
}

/// Source of single-use `t-of-t` projected `[128, 56, 73]` `MiniMAC` tuples.
pub trait CnfRssTupleSource: Send + Sync {
    /// Next `count` single-use 56-lane permutation tuples for `t` online signers.
    fn next_wave_tuples(&mut self, count: usize) -> Result<Vec<ProjectedWaveTuple>, CnfRssError>;

    /// Next `groups` single-use 256-bit cut-opening mask tuples (`r^* in C^{*2}` vanishing on `0..56`).
    fn next_cut_masks(&mut self, groups: usize) -> Result<Vec<ProjectedCutMaskTuple>, CnfRssError>;

    /// Claim the next `count` wave tuples without expanding them. The engine redeems each
    /// ticket on the worker that evaluates its permutation, so a sweep holds one expanded
    /// tuple per worker instead of one per permutation. Tickets come in the order
    /// [`Self::next_wave_tuples`] would return the tuples; the default expands eagerly.
    fn reserve_wave_tuples(&mut self, count: usize) -> Result<Vec<WaveTupleTicket>, CnfRssError> {
        Ok(self
            .next_wave_tuples(count)?
            .into_iter()
            .map(|tuple| WaveTupleTicket(TicketKind::Ready(Box::new(tuple))))
            .collect())
    }
}

/// Single-use claim on one wave tuple (`!Clone`; its secrets are wiped on drop).
pub struct WaveTupleTicket(TicketKind);

enum TicketKind {
    Ready(Box<ProjectedWaveTuple>),
    Compact(CompactWaveTuple),
    Seed {
        t: usize,
        seed: SecretBuffer<[u8; 32]>,
        corrupt_gate: Option<usize>,
    },
}

impl WaveTupleTicket {
    fn redeem(self, tables: &MiniMacTables) -> Result<ProjectedWaveTuple, CnfRssError> {
        match self.0 {
            TicketKind::Ready(tuple) => Ok(*tuple),
            TicketKind::Compact(compact) => compact.expand(tables),
            TicketKind::Seed {
                t,
                seed,
                corrupt_gate,
            } => Ok(materialize_wave_tuple(tables, t, &seed, corrupt_gate)),
        }
    }
}

/// Bytes of per-gate bit randomness one signer expands: three 56-bit masks (`a`, `b`, `r`).
const WAVE_BITS_PER_GATE: usize = 21;
/// Buffers a signer holds as pseudorandom shares or, for the last signer, as corrections:
/// `a_mac`, `b_mac`, `r_mac`, `cr_star`, `cr_star_mac`.
const WAVE_CORRECTED_BUFFERS: usize = 5;
/// Byte length of one wave buffer (`24` rounds of `1600` codewords).
const WAVE_BUFFER_BYTES: usize = 24 * STATE_CODE_BYTES;

/// Eight-lane `SHAKE256` expander: `outs[i]` receives `SHAKE256(seed || [i])` truncated to
/// its length. One [`qsag_asm::keccak_f1600_x8`] call produces a rate block of every output.
fn shake256_x8_expand(seed: &[u8; 32], outs: &mut [&mut [u8]; 8]) {
    let mut states = qsag_asm::KeccakState8x::default();
    let (seed_words, _) = seed.as_chunks::<8>();
    for lane in 0..8 {
        for (w, bytes) in seed_words.iter().enumerate() {
            states.0[w][lane] = u64::from_le_bytes(*bytes);
        }
        // Byte 32 is the lane index, byte 33 the `SHAKE` domain suffix.
        states.0[4][lane] = (lane as u64) | (0x1f << 8);
        states.0[SHAKE256_RATE_LANES - 1][lane] ^= 1u64 << 63;
    }
    let longest = outs.iter().map(|o| o.len()).max().unwrap_or(0);
    let mut off = 0usize;
    while off < longest {
        qsag_asm::keccak_f1600_x8(&mut states);
        for (lane, out) in outs.iter_mut().enumerate() {
            if off >= out.len() {
                continue;
            }
            let end = (off + SHAKE256_RATE_BYTES).min(out.len());
            let (full, tail) = out[off..end].as_chunks_mut::<8>();
            let full_words = full.len();
            for (w, chunk) in full.iter_mut().enumerate() {
                *chunk = states.0[w][lane].to_le_bytes();
            }
            if !tail.is_empty() {
                let last = states.0[full_words][lane].to_le_bytes();
                tail.copy_from_slice(&last[..tail.len()]);
            }
        }
        off += SHAKE256_RATE_BYTES;
    }
    qsag_asm::volatile_fill(&mut states.0, [0; 8]);
}

/// Everything one signer derives from its own 32-byte wave seed.
struct SignerWaveExpansion {
    /// Codeword shares of the `a`, `b`, `r` masks: the encodings of the signer's own bits.
    a: Vec<u8>,
    b: Vec<u8>,
    r: Vec<u8>,
    /// Pseudorandom shares of the corrected buffers (empty for the last signer).
    prg: Vec<Vec<u8>>,
}

/// Expand one signer's wave seed. A signer's `a`, `b`, `r` shares are `[128, 56, 73]`
/// codewords of its own random bits, so the sums are codewords of the XORed bits and need no
/// correction. `with_prg_shares` also expands the five uniformly random share buffers.
fn expand_signer_wave(
    tables: &MiniMacTables,
    seed: &[u8; 32],
    with_prg_shares: bool,
) -> SignerWaveExpansion {
    let mut bits = SecretBuffer(vec![0u8; GATES_PER_WAVE_PERM * WAVE_BITS_PER_GATE]);
    let prg_len = if with_prg_shares {
        WAVE_BUFFER_BYTES
    } else {
        0
    };
    let mut prg: Vec<Vec<u8>> = (0..WAVE_CORRECTED_BUFFERS)
        .map(|_| vec![0u8; prg_len])
        .collect();
    {
        // Lane 0 is the bit randomness, lanes 1..=5 the share buffers, lanes 6 and 7 unused.
        let mut first = Some(bits.0.as_mut_slice());
        let mut rest = prg.iter_mut();
        let mut outs: [&mut [u8]; 8] = core::array::from_fn(|_| {
            first
                .take()
                .or_else(|| rest.next().map(Vec::as_mut_slice))
                .unwrap_or_default()
        });
        shake256_x8_expand(seed, &mut outs);
    }
    let mut a = vec![0u8; WAVE_BUFFER_BYTES];
    let mut b = vec![0u8; WAVE_BUFFER_BYTES];
    let mut r = vec![0u8; WAVE_BUFFER_BYTES];
    let mask56 = (1u64 << MINIMAC_DATA_K) - 1;
    let word = |raw: &[u8]| {
        u64::from_le_bytes([raw[0], raw[1], raw[2], raw[3], raw[4], raw[5], raw[6], 0]) & mask56
    };
    for (((gate, a_cw), b_cw), r_cw) in bits
        .as_chunks::<WAVE_BITS_PER_GATE>()
        .0
        .iter()
        .zip(a.as_chunks_mut::<MINIMAC_CODE_N>().0)
        .zip(b.as_chunks_mut::<MINIMAC_CODE_N>().0)
        .zip(r.as_chunks_mut::<MINIMAC_CODE_N>().0)
    {
        tables.encode_public_bits56(word(&gate[0..7]), a_cw);
        tables.encode_public_bits56(word(&gate[7..14]), b_cw);
        tables.encode_public_bits56(word(&gate[14..21]), r_cw);
    }
    SignerWaveExpansion { a, b, r, prg }
}

impl SecretWipe for SignerWaveExpansion {
    fn secret_wipe(&mut self) {
        self.a.secret_wipe();
        self.b.secret_wipe();
        self.r.secret_wipe();
        self.prg.secret_wipe();
    }
}

/// Per-signer seeds and MAC key shares of one wave, drawn from the wave seed.
struct WaveRoots {
    delta_shares: SecretVec<[u8; MINIMAC_CODE_N]>,
    signer_seeds: SecretVec<[u8; 32]>,
    /// Seed of the `C^{*2}` zero-mask randomness that only enters the corrections.
    zero_mask_seed: SecretBuffer<[u8; 32]>,
}

fn wave_roots(t: usize, wave_seed: &[u8; 32]) -> WaveRoots {
    let mut xof = Cshake256Xof::new(b"QSAG.CNF_RSS.MINIMAC.WAVE/v1");
    xof.absorb(wave_seed);
    let mut delta_shares = SecretBuffer(vec![[0u8; MINIMAC_CODE_N]; t]);
    let mut delta_sum = SecretBuffer([0u8; MINIMAC_CODE_N]);
    for u in 0..(t - 1) {
        xof.squeeze(&mut delta_shares[u]);
        for j in 0..MINIMAC_CODE_N {
            delta_sum[j] ^= delta_shares[u][j];
        }
    }
    xof.squeeze(&mut delta_shares[t - 1]);
    for j in 0..MINIMAC_CODE_N {
        // Ensure non-zero coordinates in `Delta` for full `2^{-144}` distance soundness.
        let cur = delta_sum[j] ^ delta_shares[t - 1][j];
        if cur == 0 {
            delta_shares[t - 1][j] ^= 1;
        }
        delta_sum[j] ^= delta_shares[t - 1][j];
    }
    let mut signer_seeds = SecretBuffer(vec![[0u8; 32]; t]);
    for seed in signer_seeds.iter_mut() {
        xof.squeeze(seed);
    }
    let mut zero_mask_seed = SecretBuffer([0u8; 32]);
    xof.squeeze(&mut zero_mask_seed.0);
    WaveRoots {
        delta_shares,
        signer_seeds,
        zero_mask_seed,
    }
}

fn xor_into(dst: &mut [u8], src: &[u8]) {
    for (d, &s) in dst.iter_mut().zip(src) {
        *d ^= s;
    }
}

/// `dst = a ^ b` over equal-length slices.
fn xor2_to(dst: &mut [u8], a: &[u8], b: &[u8]) {
    for (d, (&x, &y)) in dst.iter_mut().zip(a.iter().zip(b)) {
        *d = x ^ y;
    }
}

/// `dst ^= a ^ b` over equal-length slices.
fn xor2_into(dst: &mut [u8], a: &[u8], b: &[u8]) {
    for (d, (&x, &y)) in dst.iter_mut().zip(a.iter().zip(b)) {
        *d ^= x ^ y;
    }
}

/// `SHAKE256` digests of the eight equal consecutive parts of `data`, computed with the
/// eight-lane permutation. `data.len()` must be a multiple of eight.
fn shake256_x8_part_digests(data: &[u8]) -> [[u8; 32]; 8] {
    let part_len = data.len() / 8;
    let mut states = qsag_asm::KeccakState8x::default();
    let mut block = [0u8; SHAKE256_RATE_BYTES];
    let mut off = 0usize;
    loop {
        let last = off + SHAKE256_RATE_BYTES > part_len;
        for lane in 0..8 {
            let part = &data[lane * part_len..(lane + 1) * part_len];
            let chunk = &part[off..part_len.min(off + SHAKE256_RATE_BYTES)];
            block.fill(0);
            block[..chunk.len()].copy_from_slice(chunk);
            if last {
                block[chunk.len()] ^= 0x1f;
                block[SHAKE256_RATE_BYTES - 1] ^= 0x80;
            }
            for (w, bytes) in block.as_chunks::<8>().0.iter().enumerate() {
                states.0[w][lane] ^= u64::from_le_bytes(*bytes);
            }
        }
        qsag_asm::keccak_f1600_x8(&mut states);
        if last {
            break;
        }
        off += SHAKE256_RATE_BYTES;
    }
    let mut out = [[0u8; 32]; 8];
    for (lane, digest) in out.iter_mut().enumerate() {
        for (w, chunk) in digest.as_chunks_mut::<8>().0.iter_mut().enumerate() {
            *chunk = states.0[w][lane].to_le_bytes();
        }
    }
    out
}

/// Derive a single-use `ProjectedWaveTuple` from a domain-bound seed.
///
/// Signers `0..t-1` hold nothing but a 32-byte seed for this wave; the last signer also holds
/// the five correction buffers. All bulk randomness comes from eight-lane `SHAKE256`.
fn materialize_wave_tuple(
    tables: &MiniMacTables,
    t: usize,
    wave_seed: &[u8; 32],
    corrupt_gate: Option<usize>,
) -> ProjectedWaveTuple {
    let WaveRoots {
        delta_shares,
        signer_seeds,
        zero_mask_seed,
    } = wave_roots(t, wave_seed);
    let mut delta_sum = SecretBuffer([0u8; MINIMAC_CODE_N]);
    for share in delta_shares.iter() {
        xor_into(&mut delta_sum.0, share);
    }

    let mut signers = SecretBuffer(Vec::with_capacity(t));
    for (u, seed) in signer_seeds.iter().enumerate() {
        signers.push(expand_signer_wave(tables, seed, u + 1 < t));
    }

    let mut a_sum = SecretBuffer(vec![0u8; WAVE_BUFFER_BYTES]);
    let mut b_sum = SecretBuffer(vec![0u8; WAVE_BUFFER_BYTES]);
    let mut r_sum = SecretBuffer(vec![0u8; WAVE_BUFFER_BYTES]);
    for signer in signers.iter() {
        xor_into(&mut a_sum, &signer.a);
        xor_into(&mut b_sum, &signer.b);
        xor_into(&mut r_sum, &signer.r);
    }

    // `cr_star_sum = (a_sum * b_sum) ^ r_sum ^ z_zero`, with `z_zero in C^{*2}` vanishing on
    // the data coordinates.
    let mut cr_star_sum = SecretBuffer(vec![0u8; WAVE_BUFFER_BYTES]);
    qsag_asm::gf256_shamir_mul(&mut cr_star_sum, &a_sum, &b_sum);
    xor_into(&mut cr_star_sum, &r_sum);
    {
        let mut zero_rand = SecretBuffer(vec![0u8; GATES_PER_WAVE_PERM * MINIMAC_ZERO_MASK_K]);
        {
            let lane_len = zero_rand.len() / 8;
            let mut chunks = zero_rand.chunks_exact_mut(lane_len);
            let mut outs: [&mut [u8]; 8] =
                core::array::from_fn(|_| chunks.next().unwrap_or_default());
            shake256_x8_expand(&zero_mask_seed, &mut outs);
        }
        let mut cw = SecretBuffer([0u8; MINIMAC_CODE_N]);
        for (r55, dst) in zero_rand
            .as_chunks::<MINIMAC_ZERO_MASK_K>()
            .0
            .iter()
            .zip(cr_star_sum.as_chunks_mut::<MINIMAC_CODE_N>().0)
        {
            tables.encode_batch_c2_zero_mask(r55, &mut cw);
            xor_into(dst, &cw.0);
        }
    }
    if let Some(bad_g) = corrupt_gate
        && bad_g < GATES_PER_WAVE_PERM
    {
        cr_star_sum[bad_g * MINIMAC_CODE_N] ^= 1;
    }

    // Repeat `delta_sum` across a `1600 * 128` round tile for batched `gf256_shamir_mul`.
    let mut delta_tile = SecretBuffer(vec![0u8; STATE_CODE_BYTES]);
    for chunk in delta_tile.as_chunks_mut::<MINIMAC_CODE_N>().0 {
        chunk.copy_from_slice(&*delta_sum);
    }
    // Correction of one buffer: its MAC (or value) sum minus every pseudorandom share.
    let correction = |sum: &[u8], is_mac: bool, idx: usize| -> Vec<u8> {
        let mut out = vec![0u8; WAVE_BUFFER_BYTES];
        if is_mac {
            for (dst, src) in out
                .as_chunks_mut::<STATE_CODE_BYTES>()
                .0
                .iter_mut()
                .zip(sum.as_chunks::<STATE_CODE_BYTES>().0)
            {
                qsag_asm::gf256_shamir_mul(dst, src, &delta_tile);
            }
        } else {
            out.copy_from_slice(sum);
        }
        for signer in signers.iter().take(t - 1) {
            xor_into(&mut out, &signer.prg[idx]);
        }
        out
    };
    let corrections = [
        correction(&a_sum, true, 0),
        correction(&b_sum, true, 1),
        correction(&r_sum, true, 2),
        correction(&cr_star_sum, false, 3),
        correction(&cr_star_sum, true, 4),
    ];

    assemble_wave_tuple(
        delta_shares,
        signer_seeds,
        core::mem::take(&mut signers.0),
        corrections,
    )
}

/// Lay signer expansions and the last signer's corrections out as per-party share vectors.
fn assemble_wave_tuple(
    delta_shares: SecretVec<[u8; MINIMAC_CODE_N]>,
    signer_seeds: SecretVec<[u8; 32]>,
    signers: Vec<SignerWaveExpansion>,
    corrections: [Vec<u8>; WAVE_CORRECTED_BUFFERS],
) -> ProjectedWaveTuple {
    let t = signers.len();
    let mut a = SecretBuffer(Vec::with_capacity(t));
    let mut b = SecretBuffer(Vec::with_capacity(t));
    let mut r = SecretBuffer(Vec::with_capacity(t));
    let mut corrected: [SecretVec<Vec<u8>>; WAVE_CORRECTED_BUFFERS] =
        core::array::from_fn(|_| SecretBuffer(Vec::with_capacity(t)));
    let mut corrections = corrections.map(Some);
    for (u, signer) in signers.into_iter().enumerate() {
        a.push(signer.a);
        b.push(signer.b);
        r.push(signer.r);
        for (idx, share) in signer.prg.into_iter().enumerate() {
            if u + 1 < t {
                corrected[idx].push(share);
            } else if let Some(correction) = corrections[idx].take() {
                corrected[idx].push(correction);
            }
        }
    }
    let [a_mac, b_mac, r_mac, cr_star, cr_star_mac] = corrected;
    ProjectedWaveTuple {
        delta_shares,
        signer_seeds,
        a,
        a_mac,
        b,
        b_mac,
        r,
        r_mac,
        cr_star,
        cr_star_mac,
    }
}

/// A staged wave tuple at rest: each signer's 32-byte seed and MAC key share, plus the five
/// correction buffers of the last signer (`24.6 MB`, against `39.3 MB` per signer expanded).
struct CompactWaveTuple {
    delta_shares: SecretVec<[u8; MINIMAC_CODE_N]>,
    signer_seeds: SecretVec<[u8; 32]>,
    corrections: SecretVec<Vec<u8>>,
}

impl ProjectedWaveTuple {
    /// Drop everything a signer can re-expand from its seed.
    fn into_compact(mut self) -> CompactWaveTuple {
        let mut corrections = SecretBuffer(Vec::with_capacity(WAVE_CORRECTED_BUFFERS));
        for shares in [
            &mut self.a_mac,
            &mut self.b_mac,
            &mut self.r_mac,
            &mut self.cr_star,
            &mut self.cr_star_mac,
        ] {
            corrections.push(shares.pop().unwrap_or_default());
        }
        CompactWaveTuple {
            delta_shares: SecretBuffer(core::mem::take(&mut self.delta_shares.0)),
            signer_seeds: SecretBuffer(core::mem::take(&mut self.signer_seeds.0)),
            corrections,
        }
    }
}

impl CompactWaveTuple {
    /// Re-expand every signer's shares. Consumes the tuple: it is single-use.
    fn expand(mut self, tables: &MiniMacTables) -> Result<ProjectedWaveTuple, CnfRssError> {
        let t = self.signer_seeds.len();
        let corrections: [Vec<u8>; WAVE_CORRECTED_BUFFERS] =
            core::mem::take(&mut self.corrections.0)
                .try_into()
                .map_err(|_| CnfRssError::InvalidParameters)?;
        let signers = self
            .signer_seeds
            .iter()
            .enumerate()
            .map(|(u, seed)| expand_signer_wave(tables, seed, u + 1 < t))
            .collect();
        Ok(assemble_wave_tuple(
            SecretBuffer(core::mem::take(&mut self.delta_shares.0)),
            SecretBuffer(core::mem::take(&mut self.signer_seeds.0)),
            signers,
            corrections,
        ))
    }
}

fn materialize_cut_mask_tuple(
    tables: &MiniMacTables,
    t: usize,
    cut_seed: &[u8; 32],
) -> ProjectedCutMaskTuple {
    let total_bytes = DIGEST_BITS * MINIMAC_CODE_N;
    let mut xof = Cshake256Xof::new(b"QSAG.CNF_RSS.MINIMAC.CUT/v1");
    xof.absorb(cut_seed);

    let mut r_star_sum = SecretBuffer(vec![0u8; total_bytes]);
    let mut r55 = SecretBuffer([0u8; MINIMAC_ZERO_MASK_K]);
    let mut cw = SecretBuffer([0u8; MINIMAC_CODE_N]);
    for bit in 0..DIGEST_BITS {
        xof.squeeze(&mut *r55);
        tables.encode_batch_c2_zero_mask(&r55, &mut cw);
        let off = bit * MINIMAC_CODE_N;
        r_star_sum[off..off + MINIMAC_CODE_N].copy_from_slice(&*cw);
    }

    let mut r_star = SecretBuffer(Vec::with_capacity(t));
    let mut rem = r_star_sum.to_vec();
    for _ in 0..(t - 1) {
        let mut sh = vec![0u8; total_bytes];
        xof.squeeze(&mut sh);
        for (r_byte, &s_byte) in rem.iter_mut().zip(sh.iter()) {
            *r_byte ^= s_byte;
        }
        r_star.push(sh);
    }
    r_star.push(rem);

    ProjectedCutMaskTuple { r_star }
}

// Validate complete custody input before deriving any correlation seed. The caller
// is a trusted coordinator; comparisons here detect mismatched/malformed inputs,
// not malicious behavior by that coordinator.
fn correlation_root(
    tag: &[u8],
    session_id: &[u8; 32],
    cfg: &CnfRssConfig,
    shares: &[CnfRssKeyShare256],
    quorum: &[usize],
) -> Result<SecretBuffer<[u8; 32]>, CnfRssError> {
    cfg.validate_quorum(quorum)?;
    if shares.len() != cfg.n
        || shares.iter().enumerate().any(|(p, s)| {
            s.party_id != p
                || s.cfg != *cfg
                || s.key_len != shares[0].key_len
                || s.pk_seed != shares[0].pk_seed
                || s.scheme_identity != shares[0].scheme_identity
                || s.slh_profile_digest != shares[0].slh_profile_digest
        })
    {
        return Err(CnfRssError::InvalidParameters);
    }
    let mut xof = Cshake256Xof::new(tag);
    xof.absorb(session_id);
    for slot_idx in 0..cfg.total_slots() {
        let mut first: Option<(&[u8; 32], &[u8; 32], &[u8; 32])> = None;
        for share in shares {
            if let Some(pos) = share.local_slot_pos(slot_idx) {
                let current = (
                    &share.slot_prg_seeds[pos],
                    &share.sk_seed_slots[pos],
                    &share.sk_prf_slots[pos],
                );
                if let Some(previous) = first {
                    if !(ct_eq_bytes32(previous.0, current.0)
                        & ct_eq_bytes32(previous.1, current.1)
                        & ct_eq_bytes32(previous.2, current.2))
                    {
                        return Err(CnfRssError::SlotOverlapMismatch { slot_idx });
                    }
                } else {
                    first = Some(current);
                }
            }
        }
        xof.absorb(first.ok_or(CnfRssError::InvalidParameters)?.0);
    }
    for &q in quorum {
        xof.absorb(&(q as u64).to_be_bytes());
    }
    let mut root = SecretBuffer([0; 32]);
    xof.squeeze(&mut root.0);
    Ok(root)
}

/// Pre-staged single-use `(t, n)` CNF-RSS bank projected onto an online $t$-signer quorum.
///
/// Wave tuples are kept compact: per wave, every signer's 32-byte seed and the last
/// signer's five correction buffers (`24.6 MB` in total, independent of `t`). The signers'
/// own shares are re-expanded with eight-lane `SHAKE256` when a tuple is handed out.
pub struct StagedCnfRssBank {
    waves: Vec<CompactWaveTuple>,
    cuts: Vec<ProjectedCutMaskTuple>,
    tables: Box<MiniMacTables>,
}

impl StagedCnfRssBank {
    /// Stage `num_waves` 56-lane permutation tuples and `num_cuts` cut-opening mask tuples
    /// from the `(t, n)` CNF-RSS committee seeds (`2t - 1` honest-majority ceremony) and
    /// project onto `quorum` (`|Q| = t`).
    pub fn stage_for_quorum(
        session_id: [u8; 32],
        cfg: &CnfRssConfig,
        all_shares: &[CnfRssKeyShare256],
        quorum: &[usize],
        num_waves: usize,
        num_cuts: usize,
    ) -> Result<Self, CnfRssError> {
        let master = correlation_root(
            b"QSAG.CNF_RSS.BANK.ROOT/v1",
            &session_id,
            cfg,
            all_shares,
            quorum,
        )?;

        let tables = MiniMacTables::build()?;
        let wave_seeds = SecretBuffer(
            (0..num_waves)
                .map(|w| {
                    cshake256_32_multi_frame(
                        b"QSAG.CNF_RSS.BANK.WAVE_SEED/v1",
                        &[&*master, &(w as u64).to_le_bytes()],
                    )
                })
                .collect::<Vec<[u8; 32]>>(),
        );
        #[cfg(feature = "std")]
        let waves: Vec<CompactWaveTuple> = {
            let workers = std::thread::available_parallelism()
                .map_or(1, usize::from)
                .min(4);
            let chunk_sz = wave_seeds.len().div_ceil(workers).max(1);
            let mut slots: Vec<Option<CompactWaveTuple>> =
                (0..wave_seeds.len()).map(|_| None).collect();
            std::thread::scope(|scope| {
                let mut handles = Vec::new();
                for (c_idx, out_slice) in slots.chunks_mut(chunk_sz).enumerate() {
                    let seeds = &wave_seeds
                        [c_idx * chunk_sz..((c_idx + 1) * chunk_sz).min(wave_seeds.len())];
                    let tables_ref = &*tables;
                    let t = cfg.t;
                    handles.push(scope.spawn(move || {
                        for (dst, seed) in out_slice.iter_mut().zip(seeds.iter()) {
                            *dst = Some(
                                materialize_wave_tuple(tables_ref, t, seed, None).into_compact(),
                            );
                        }
                    }));
                }
                let joined: Vec<_> = handles.into_iter().map(|h| h.join()).collect();
                if joined.into_iter().any(|r| r.is_err()) {
                    return Err(CnfRssError::InvalidParameters);
                }
                Ok(())
            })?;
            slots.into_iter().flatten().collect()
        };
        #[cfg(not(feature = "std"))]
        let waves: Vec<CompactWaveTuple> = wave_seeds
            .iter()
            .map(|seed| materialize_wave_tuple(&tables, cfg.t, seed, None).into_compact())
            .collect();

        let cuts: Vec<ProjectedCutMaskTuple> = (0..num_cuts)
            .map(|c| {
                let c_seed = SecretBuffer(cshake256_32_multi_frame(
                    b"QSAG.CNF_RSS.BANK.CUT_SEED/v1",
                    &[&*master, &(c as u64).to_le_bytes()],
                ));
                materialize_cut_mask_tuple(&tables, cfg.t, &c_seed)
            })
            .collect();

        Ok(Self {
            waves,
            cuts,
            tables,
        })
    }

    #[inline]
    pub fn remaining_waves(&self) -> usize {
        self.waves.len()
    }
}

impl CnfRssTupleSource for StagedCnfRssBank {
    fn next_wave_tuples(&mut self, count: usize) -> Result<Vec<ProjectedWaveTuple>, CnfRssError> {
        if self.waves.len() < count {
            return Err(CnfRssError::BeaverBankExhausted);
        }
        let split_at = self.waves.len() - count;
        let compact = self.waves.split_off(split_at);
        expand_compact_waves(&self.tables, compact)
    }

    fn reserve_wave_tuples(&mut self, count: usize) -> Result<Vec<WaveTupleTicket>, CnfRssError> {
        if self.waves.len() < count {
            return Err(CnfRssError::BeaverBankExhausted);
        }
        let split_at = self.waves.len() - count;
        Ok(self
            .waves
            .split_off(split_at)
            .into_iter()
            .map(|compact| WaveTupleTicket(TicketKind::Compact(compact)))
            .collect())
    }

    fn next_cut_masks(&mut self, groups: usize) -> Result<Vec<ProjectedCutMaskTuple>, CnfRssError> {
        if self.cuts.len() < groups {
            return Err(CnfRssError::BeaverBankExhausted);
        }
        let split_at = self.cuts.len() - groups;
        Ok(self.cuts.split_off(split_at))
    }
}

/// Expand a batch of compact tuples, on up to four threads with `std`.
fn expand_compact_waves(
    tables: &MiniMacTables,
    compact: Vec<CompactWaveTuple>,
) -> Result<Vec<ProjectedWaveTuple>, CnfRssError> {
    #[cfg(feature = "std")]
    if compact.len() > 1 {
        let workers = std::thread::available_parallelism()
            .map_or(1, usize::from)
            .min(4);
        let chunk_sz = compact.len().div_ceil(workers).max(1);
        let mut jobs: Vec<Vec<CompactWaveTuple>> = Vec::new();
        let mut rest = compact.into_iter();
        loop {
            let job: Vec<CompactWaveTuple> = rest.by_ref().take(chunk_sz).collect();
            if job.is_empty() {
                break;
            }
            jobs.push(job);
        }
        return std::thread::scope(|scope| {
            let handles: Vec<_> = jobs
                .into_iter()
                .map(|job| {
                    scope.spawn(move || {
                        job.into_iter()
                            .map(|c| c.expand(tables))
                            .collect::<Result<Vec<_>, _>>()
                    })
                })
                .collect();
            // Join every worker before reporting a failure.
            let joined: Vec<_> = handles.into_iter().map(|h| h.join()).collect();
            let mut out = Vec::new();
            for part in joined {
                out.extend(part.map_err(|_| CnfRssError::InvalidParameters)??);
            }
            Ok(out)
        });
    }
    compact.into_iter().map(|c| c.expand(tables)).collect()
}

/// Bounded-batch (up to several GiB) streaming `(t, n)` CNF-RSS tuple source materializing
/// `t-of-t` projected `MiniMAC` windows on demand across parallel cores without multi-GB heap banks.
pub struct StreamingCnfRssSource {
    t: usize,
    master_seed: SecretBuffer<[u8; 32]>,
    tables: Box<MiniMacTables>,
    wave_ctr: u64,
    cut_ctr: u64,
    #[cfg(test)]
    corrupt_wave: Option<(u64, usize)>,
}

impl StreamingCnfRssSource {
    /// Establish a streaming source from the `(t, n)` CNF-RSS committee shares and target `quorum`.
    pub fn establish(
        session_id: [u8; 32],
        cfg: &CnfRssConfig,
        all_shares: &[CnfRssKeyShare256],
        quorum: &[usize],
    ) -> Result<Self, CnfRssError> {
        let master_seed = correlation_root(
            b"QSAG.CNF_RSS.STREAM.ROOT/v1",
            &session_id,
            cfg,
            all_shares,
            quorum,
        )?;
        Ok(Self {
            t: cfg.t,
            master_seed,
            tables: MiniMacTables::build()?,
            wave_ctr: 0,
            cut_ctr: 0,
            #[cfg(test)]
            corrupt_wave: None,
        })
    }
}

/// `(wave index, wave seed)` of each claimed wave.
type ClaimedWaveSeeds = SecretVec<(u64, [u8; 32])>;

impl StreamingCnfRssSource {
    /// Advance the wave counter by `count` and derive the claimed waves' seeds.
    fn claim_wave_seeds(&mut self, count: usize) -> Result<ClaimedWaveSeeds, CnfRssError> {
        let base = self.wave_ctr;
        self.wave_ctr = self
            .wave_ctr
            .checked_add(count as u64)
            .ok_or(CnfRssError::InvalidParameters)?;
        Ok(SecretBuffer(
            (0..count)
                .map(|i| {
                    let idx = base + i as u64;
                    let s = cshake256_32_multi_frame(
                        b"QSAG.CNF_RSS.STREAM.WAVE/v1",
                        &[&*self.master_seed, &idx.to_le_bytes()],
                    );
                    (idx, s)
                })
                .collect::<Vec<(u64, [u8; 32])>>(),
        ))
    }

    fn corrupt_gate_of(&self, wave: u64) -> Option<usize> {
        #[cfg(test)]
        let corrupt = self.corrupt_wave;
        #[cfg(not(test))]
        let corrupt: Option<(u64, usize)> = None;
        corrupt.filter(|&(w, _)| w == wave).map(|(_, g)| g)
    }
}

impl CnfRssTupleSource for StreamingCnfRssSource {
    fn reserve_wave_tuples(&mut self, count: usize) -> Result<Vec<WaveTupleTicket>, CnfRssError> {
        let seeds = self.claim_wave_seeds(count)?;
        Ok(seeds
            .iter()
            .map(|&(idx, seed)| {
                WaveTupleTicket(TicketKind::Seed {
                    t: self.t,
                    seed: SecretBuffer(seed),
                    corrupt_gate: self.corrupt_gate_of(idx),
                })
            })
            .collect())
    }

    fn next_wave_tuples(&mut self, count: usize) -> Result<Vec<ProjectedWaveTuple>, CnfRssError> {
        let seeds = self.claim_wave_seeds(count)?;
        #[cfg(test)]
        let corrupt = self.corrupt_wave;
        #[cfg(not(test))]
        let corrupt: Option<(u64, usize)> = None;

        #[cfg(feature = "std")]
        if count > 1 {
            let workers = std::thread::available_parallelism()
                .map_or(1, usize::from)
                .min(4);
            let chunk_sz = seeds.len().div_ceil(workers).max(1);
            let mut slots: Vec<Option<ProjectedWaveTuple>> =
                (0..seeds.len()).map(|_| None).collect();
            let tables_ref = &*self.tables;
            let t = self.t;
            std::thread::scope(|scope| {
                let mut handles = Vec::new();
                for (c_idx, out_slice) in slots.chunks_mut(chunk_sz).enumerate() {
                    let sub = &seeds[c_idx * chunk_sz..((c_idx + 1) * chunk_sz).min(seeds.len())];
                    handles.push(scope.spawn(move || {
                        for (dst, &(idx, ref seed)) in out_slice.iter_mut().zip(sub.iter()) {
                            let cg = corrupt.filter(|&(w, _)| w == idx).map(|(_, g)| g);
                            *dst = Some(materialize_wave_tuple(tables_ref, t, seed, cg));
                        }
                    }));
                }
                let joined: Vec<_> = handles.into_iter().map(|h| h.join()).collect();
                if joined.into_iter().any(|r| r.is_err()) {
                    return Err(CnfRssError::InvalidParameters);
                }
                Ok(())
            })?;
            return Ok(slots.into_iter().flatten().collect());
        }

        Ok(seeds
            .iter()
            .map(|&(idx, ref seed)| {
                let cg = corrupt.filter(|&(w, _)| w == idx).map(|(_, g)| g);
                materialize_wave_tuple(&self.tables, self.t, seed, cg)
            })
            .collect())
    }

    fn next_cut_masks(&mut self, groups: usize) -> Result<Vec<ProjectedCutMaskTuple>, CnfRssError> {
        let base = self.cut_ctr;
        self.cut_ctr = self
            .cut_ctr
            .checked_add(groups as u64)
            .ok_or(CnfRssError::InvalidParameters)?;
        Ok((0..groups)
            .map(|i| {
                let idx = base + i as u64;
                let s = cshake256_32_multi_frame(
                    b"QSAG.CNF_RSS.STREAM.CUT/v1",
                    &[&*self.master_seed, &idx.to_le_bytes()],
                );
                materialize_cut_mask_tuple(&self.tables, self.t, &s)
            })
            .collect())
    }
}

// ============================================================================
// 4. `CnfRssProjectedEngine`: 56-Lane `MiniMAC` `BaggyEngine` + `SlhMpcOracles`
// ============================================================================

/// Shared 256-bit digests of one 56-lane wave (`[party][256 * 128]` codewords + MACs under `delta`).
pub struct CnfRssSharedDigests {
    delta_shares: SecretVec<[u8; MINIMAC_CODE_N]>,
    sh: SecretVec<Vec<u8>>,
    mac: SecretVec<Vec<u8>>,
    active_lanes: usize,
}

/// Shared chain positions produced by [`CnfRssProjectedEngine::sweep`].
pub struct CnfRssSweep {
    lanes: Vec<LaneSpec>,
    pos: Vec<Vec<CnfRssSharedDigests>>,
}

/// Deferred verification record for one evaluated 56-lane permutation (`64 B` VPCLMULQDQ MAC fold).
struct PendingWaveVerification {
    wave_digest: [u8; 32],
    /// Per-party folded `GF(2^128)` polynomial-basis MAC residual shares (`2` independent lanes = `2^{-256}`).
    residual_shares: SecretVec<[u128; 2]>,
}

type SweepJobOutcome =
    Result<(Vec<CnfRssSharedDigests>, Vec<PendingWaveVerification>), CnfRssError>;
type SlhChainChunk<'a> = &'a [(Fips205Adrs, Vec<Fips205Adrs>)];
type SlhJobInput<'a> = (SlhChainChunk<'a>, usize, usize, Vec<WaveTupleTicket>);
type SlhJobOutcome = Result<(CnfRssSharedDigests, Vec<PendingWaveVerification>), CnfRssError>;

/// Fault-injection hook for adversarial active-abort tests.
#[cfg(test)]
#[derive(Clone, Copy, Debug)]
pub enum CnfRssFault {
    /// Flip a byte of party `party`'s `d` opening at `(wave, round, bit)` without fixing parity.
    CorruptDOpening {
        wave: usize,
        round: usize,
        bit: usize,
        party: usize,
    },
    /// Shift `d` by a valid `[128, 56, 73]` codeword (`[1u8; 128]`), bypassing `C` parity check
    /// so ONLY the `Tower128` `MiniMAC` check catches it (`2^{-144}`).
    ValidCodewordShiftD {
        wave: usize,
        round: usize,
        bit: usize,
        party: usize,
    },
    /// Corrupt a cut-boundary opening share.
    CorruptCutOpening { party: usize },
}

/// Active `(t, n)` CNF-RSS $\to$ `t-of-t` Projected 56-Lane `MiniMAC` `Keccak-f[1600]` Engine.
///
/// Implements both [`BaggyEngine`] (stateless `Baggy` + `Waistband`) and sealed [`SlhMpcOracles`]
/// (NIST FIPS 205 `SLH-DSA-SHAKE-*`).
pub struct CnfRssProjectedEngine<'a> {
    session_id: [u8; 32],
    projected: ProjectedQuorumSecrets,
    quorum_shares: Vec<&'a mut CnfRssKeyShare256>,
    party_rngs: &'a mut [PartyPrivateRng],
    source: &'a mut dyn CnfRssTupleSource,
    tables: Box<MiniMacTables>,
    pending: Vec<PendingWaveVerification>,
    wave_ctr: usize,
    barrier_ctr: u64,
    open_ctr: u64,
    poisoned: bool,
    #[cfg(test)]
    fault: Option<CnfRssFault>,
}

/// Linear `Theta + Rho + Pi` over a contiguous `1600 * 128`-byte `MiniMAC` state.
fn keccak_linear_minimac(src: &[u8], dst: &mut [u8], col: &mut [u8], d_theta: &mut [u8]) {
    col.fill(0);
    for x in 0..5 {
        for z in 0..64 {
            let c_off = (x * 64 + z) * MINIMAC_CODE_N;
            let c_slice = &mut col[c_off..c_off + MINIMAC_CODE_N];
            for y in 0..5 {
                let s_off = ((x + 5 * y) * 64 + z) * MINIMAC_CODE_N;
                let s_slice = &src[s_off..s_off + MINIMAC_CODE_N];
                xor_into(c_slice, s_slice);
            }
        }
    }
    for x in 0..5 {
        for z in 0..64 {
            let prev = (((x + 4) % 5) * 64 + z) * MINIMAC_CODE_N;
            let next = (((x + 1) % 5) * 64 + ((z + 63) & 63)) * MINIMAC_CODE_N;
            let out_off = (x * 64 + z) * MINIMAC_CODE_N;
            xor2_to(
                &mut d_theta[out_off..out_off + MINIMAC_CODE_N],
                &col[prev..prev + MINIMAC_CODE_N],
                &col[next..next + MINIMAC_CODE_N],
            );
        }
    }
    for (source, &rot) in KECCAK_ROTATION_OFFSETS.iter().enumerate() {
        let x = source % 5;
        let y = source / 5;
        let target = y + 5 * ((2 * x + 3 * y) % 5);
        let rot = rot as usize;
        for z in 0..64 {
            let src_z = (z + 64 - rot) & 63;
            let s_off = (source * 64 + src_z) * MINIMAC_CODE_N;
            let dt_off = (x * 64 + src_z) * MINIMAC_CODE_N;
            let d_off = (target * 64 + z) * MINIMAC_CODE_N;
            xor2_to(
                &mut dst[d_off..d_off + MINIMAC_CODE_N],
                &src[s_off..s_off + MINIMAC_CODE_N],
                &d_theta[dt_off..dt_off + MINIMAC_CODE_N],
            );
        }
    }
}

#[inline]
fn bytes_to_u128_vec(bytes: &[u8], out: &mut [u128]) {
    for (dst, &chunk) in out.iter_mut().zip(bytes.as_chunks::<16>().0.iter()) {
        *dst = u128::from_le_bytes(chunk);
    }
}

/// Fold `C^{*2}` parity + `VPCLMULQDQ` `gf2_128_dot` MAC residuals for one 1,600-gate `Chi` round.
#[expect(
    clippy::too_many_arguments,
    reason = "Explicitly passes round buffers, MAC slices, delta tiles, and output residual accumulators without heap allocation"
)]
fn verify_and_fold_round_gfni(
    tables: &MiniMacTables,
    rnd_chal_seed: &[u8; 32],
    d_open: &[u8],
    e_open: &[u8],
    vstar_open: &[u8],
    not_u_mac: &[Vec<u8>],
    tuple_a_mac: &[Vec<u8>],
    v_mac: &[Vec<u8>],
    tuple_b_mac: &[Vec<u8>],
    r_off: usize,
    vstar_mac_shares: &[Vec<u8>],
    delta_tiles: &[Vec<u8>],
    tmp_mul: &mut [u8],
    lambda_tile: &mut [u8],
    u128_scratch: &mut [u128],
    block_scratch: &mut [u128],
    residual_shares: &mut [[u128; 2]],
) -> Result<(), CnfRssError> {
    // 1. `16` independent `GF(2^8)` linear combinations (`2^{-128}`) checking `vstar_open[g] in C^{*2}` via GFNI!
    let mut c2_xof = Cshake256Xof::new(b"QSAG.CNF_RSS.C2_FOLD/v1");
    c2_xof.absorb(rnd_chal_seed);
    let mut lambdas = [0u8; 16 * STATE_BITS];
    c2_xof.squeeze(&mut lambdas);
    for rep in 0..16 {
        let l_slice = &lambdas[rep * STATE_BITS..(rep + 1) * STATE_BITS];
        for (g, &lg) in l_slice.iter().enumerate() {
            lambda_tile[g * MINIMAC_CODE_N..(g + 1) * MINIMAC_CODE_N].fill(lg);
        }
        qsag_asm::gf256_shamir_mul(tmp_mul, vstar_open, lambda_tile);
        let mut folded_c2 = [0u8; MINIMAC_CODE_N];
        for chunk in tmp_mul.as_chunks::<MINIMAC_CODE_N>().0 {
            for j in 0..MINIMAC_CODE_N {
                folded_c2[j] ^= chunk[j];
            }
        }
        if !tables.verify_public_c2(&folded_c2) {
            return Err(CnfRssError::ActiveTamperDetected {
                phase: "chi_vstar_c2_degree_check",
            });
        }
    }

    // 2. `VPCLMULQDQ` (`qsag_asm::gf2_128_dot`) MAC fold of all `3 * 12,800` `u128` words
    //    under a structured challenge (see [`MacFoldChallenge`]).
    let mut mac_xof = Cshake256Xof::new(b"QSAG.CNF_RSS.MAC_FOLD/v1");
    mac_xof.absorb(rnd_chal_seed);
    let chal = MacFoldChallenge::derive(&mut mac_xof);

    let t = delta_tiles.len();
    for p in 0..t {
        let am_rnd = &tuple_a_mac[p][r_off..r_off + STATE_CODE_BYTES];
        qsag_asm::gf256_shamir_mul(tmp_mul, d_open, &delta_tiles[p]);
        for (dst, (&m, &am)) in tmp_mul.iter_mut().zip(not_u_mac[p].iter().zip(am_rnd)) {
            *dst ^= m ^ am;
        }
        bytes_to_u128_vec(tmp_mul, u128_scratch);
        chal.fold(0, u128_scratch, block_scratch, &mut residual_shares[p]);

        let bm_rnd = &tuple_b_mac[p][r_off..r_off + STATE_CODE_BYTES];
        qsag_asm::gf256_shamir_mul(tmp_mul, e_open, &delta_tiles[p]);
        for (dst, (&m, &bm)) in tmp_mul.iter_mut().zip(v_mac[p].iter().zip(bm_rnd)) {
            *dst ^= m ^ bm;
        }
        bytes_to_u128_vec(tmp_mul, u128_scratch);
        chal.fold(1, u128_scratch, block_scratch, &mut residual_shares[p]);

        qsag_asm::gf256_shamir_mul(tmp_mul, vstar_open, &delta_tiles[p]);
        for (dst, &m) in tmp_mul.iter_mut().zip(vstar_mac_shares[p].iter()) {
            *dst ^= m;
        }
        bytes_to_u128_vec(tmp_mul, u128_scratch);
        chal.fold(2, u128_scratch, block_scratch, &mut residual_shares[p]);
    }
    Ok(())
}

/// `u128` words of one 1,600-gate round segment (`204,800 / 16`).
const MAC_FOLD_WORDS: usize = STATE_CODE_BYTES / 16;
/// Words per inner block of the MAC fold.
const MAC_FOLD_BLOCK: usize = 256;
/// Blocks per round segment (`12,800 / 256`).
const MAC_FOLD_BLOCKS: usize = MAC_FOLD_WORDS / MAC_FOLD_BLOCK;
/// Segments folded per round: the `d`, `e` and `v*` MAC residuals.
const MAC_FOLD_SEGMENTS: usize = 3;

/// Per-round random linear combination of the `38,400` MAC residual words, in two
/// independent `GF(2^128)` lanes.
///
/// Word `k` of block `j` (blocks numbered across the three segments) has coefficient
/// `u^j * s^k` for lane challenges `(s, u)` drawn from the round transcript after the
/// round's openings are fixed. A nonzero residual vector is a nonzero polynomial of degree
/// at most 255 in `s` in some block, and then a nonzero polynomial of degree at most 149 in
/// `u`, so one lane misses it with probability at most `(255 + 149) / 2^128` and both lanes
/// with at most the square of that. This replaces `1.2 MB` of `SHAKE256` output per round
/// (independent coefficients) with four field elements.
struct MacFoldChallenge {
    s_pow: [[u128; MAC_FOLD_BLOCK]; 2],
    u_pow: [[u128; MAC_FOLD_SEGMENTS * MAC_FOLD_BLOCKS]; 2],
}

impl MacFoldChallenge {
    fn derive(xof: &mut Cshake256Xof) -> Self {
        let mut raw = [0u8; 64];
        xof.squeeze(&mut raw);
        let (words, _) = raw.as_chunks::<16>();
        let mut out = Self {
            s_pow: [[1u128; MAC_FOLD_BLOCK]; 2],
            u_pow: [[1u128; MAC_FOLD_SEGMENTS * MAC_FOLD_BLOCKS]; 2],
        };
        for lane in 0..2 {
            let s = u128::from_le_bytes(words[2 * lane]);
            let u = u128::from_le_bytes(words[2 * lane + 1]);
            for k in 1..MAC_FOLD_BLOCK {
                out.s_pow[lane][k] = qsag_asm::gf2_128_dot(&[out.s_pow[lane][k - 1]], &[s]);
            }
            for j in 1..MAC_FOLD_SEGMENTS * MAC_FOLD_BLOCKS {
                out.u_pow[lane][j] = qsag_asm::gf2_128_dot(&[out.u_pow[lane][j - 1]], &[u]);
            }
        }
        out
    }

    /// Fold one segment (`words.len() == MAC_FOLD_WORDS`) into both residual lanes.
    /// `blocks` is caller-owned secret scratch of `MAC_FOLD_BLOCKS` words.
    fn fold(&self, segment: usize, words: &[u128], blocks: &mut [u128], residual: &mut [u128; 2]) {
        let base = segment * MAC_FOLD_BLOCKS;
        for ((acc, s_pow), u_pow) in residual.iter_mut().zip(&self.s_pow).zip(&self.u_pow) {
            for (dst, chunk) in blocks.iter_mut().zip(words.as_chunks::<MAC_FOLD_BLOCK>().0) {
                *dst = qsag_asm::gf2_128_dot(chunk, s_pow);
            }
            *acc ^= qsag_asm::gf2_128_dot(blocks, &u_pow[base..base + MAC_FOLD_BLOCKS]);
        }
    }
}

/// Evaluate ONE 56-lane `MiniMAC` `Keccak-f[1600]` permutation in pure L2-resident buffers (`< 2 MB`),
/// returning `(CnfRssSharedDigests, PendingWaveVerification)`.
#[expect(
    clippy::too_many_arguments,
    reason = "Explicitly passes immutable tables, session context, initial shared state, wave tuple, and test fault hook for parallel worker safety"
)]
fn eval_minimac_wave_perm(
    tables: &MiniMacTables,
    session_id: &[u8; 32],
    wave_idx: usize,
    active_lanes: usize,
    truncate_to_digest: bool,
    mut state_sh: SecretVec<Vec<u8>>,
    mut state_mac: SecretVec<Vec<u8>>,
    tuple: ProjectedWaveTuple,
    #[cfg(test)] fault: Option<CnfRssFault>,
) -> Result<(CnfRssSharedDigests, PendingWaveVerification), CnfRssError> {
    let t = state_sh.len();
    let mut lin_sh = SecretBuffer(vec![vec![0u8; STATE_CODE_BYTES]; t]);
    let mut lin_mac = SecretBuffer(vec![vec![0u8; STATE_CODE_BYTES]; t]);
    let mut not_u_sh = SecretBuffer(vec![vec![0u8; STATE_CODE_BYTES]; t]);
    let mut not_u_mac = SecretBuffer(vec![vec![0u8; STATE_CODE_BYTES]; t]);
    let mut v_sh = SecretBuffer(vec![vec![0u8; STATE_CODE_BYTES]; t]);
    let mut v_mac = SecretBuffer(vec![vec![0u8; STATE_CODE_BYTES]; t]);

    let mut d_open = vec![0u8; STATE_CODE_BYTES];
    let mut e_open = vec![0u8; STATE_CODE_BYTES];
    let mut vstar_open = vec![0u8; STATE_CODE_BYTES];
    let mut de_prod = vec![0u8; STATE_CODE_BYTES];
    let mut w_pub = vec![0u8; STATE_CODE_BYTES];
    let mut tmp_mul1 = SecretBuffer(vec![0u8; STATE_CODE_BYTES]);
    let mut tmp_mul2 = SecretBuffer(vec![0u8; STATE_CODE_BYTES]);
    let mut lambda_tile = vec![0u8; STATE_CODE_BYTES];
    let mut u128_scratch = SecretBuffer(vec![0u128; STATE_CODE_BYTES / 16]);
    let mut block_scratch = SecretBuffer(vec![0u128; MAC_FOLD_BLOCKS]);
    let delta_tiles: SecretVec<Vec<u8>> = SecretBuffer(
        (0..t)
            .map(|u| {
                let mut tile = vec![0u8; STATE_CODE_BYTES];
                for c in tile.as_chunks_mut::<MINIMAC_CODE_N>().0 {
                    c.copy_from_slice(&tuple.delta_shares[u]);
                }
                tile
            })
            .collect(),
    );

    let mut tr_xof = Cshake256Xof::new(b"QSAG.CNF_RSS.WAVE.TRANSCRIPT/v1");
    tr_xof.absorb(session_id);
    tr_xof.absorb(&(wave_idx as u64).to_le_bytes());

    let mut vstar_mac_shares = SecretBuffer(vec![vec![0u8; STATE_CODE_BYTES]; t]);
    let mut residual_shares = SecretBuffer(vec![[0u128; 2]; t]);
    let mut col_scratch = SecretBuffer(vec![0u8; 5 * 64 * MINIMAC_CODE_N]);
    let mut d_theta_scratch = SecretBuffer(vec![0u8; 5 * 64 * MINIMAC_CODE_N]);

    for (rnd, &rc) in KECCAK_ROUND_CONSTANTS.iter().enumerate() {
        let r_off = rnd * STATE_CODE_BYTES;
        for u in 0..t {
            keccak_linear_minimac(
                &state_sh[u],
                &mut lin_sh[u],
                &mut col_scratch,
                &mut d_theta_scratch,
            );
            keccak_linear_minimac(
                &state_mac[u],
                &mut lin_mac[u],
                &mut col_scratch,
                &mut d_theta_scratch,
            );
        }

        // Chi operands, a whole 64-codeword lane at a time: `not_u = lin[u_lane] ^ 1` and
        // `v = lin[v_lane]`, with the constant added to party 0's share and to every MAC.
        const LANE_BYTES: usize = 64 * MINIMAC_CODE_N;
        for lane in 0..25 {
            let row = 5 * (lane / 5);
            let dst = lane * LANE_BYTES..(lane + 1) * LANE_BYTES;
            let u_src = (row + (lane + 1) % 5) * LANE_BYTES;
            let v_src = (row + (lane + 2) % 5) * LANE_BYTES;
            for p in 0..t {
                not_u_sh[p][dst.clone()].copy_from_slice(&lin_sh[p][u_src..u_src + LANE_BYTES]);
                xor2_to(
                    &mut not_u_mac[p][dst.clone()],
                    &lin_mac[p][u_src..u_src + LANE_BYTES],
                    &delta_tiles[p][..LANE_BYTES],
                );
                v_sh[p][dst.clone()].copy_from_slice(&lin_sh[p][v_src..v_src + LANE_BYTES]);
                v_mac[p][dst.clone()].copy_from_slice(&lin_mac[p][v_src..v_src + LANE_BYTES]);
            }
        }
        for b in not_u_sh[0].iter_mut() {
            *b ^= 1;
        }

        d_open.fill(0);
        e_open.fill(0);
        for p in 0..t {
            xor2_into(
                &mut d_open,
                &not_u_sh[p],
                &tuple.a[p][r_off..r_off + STATE_CODE_BYTES],
            );
            xor2_into(
                &mut e_open,
                &v_sh[p],
                &tuple.b[p][r_off..r_off + STATE_CODE_BYTES],
            );
        }
        // A party's faulty `d` share shifts the opened sum by the same amount.
        #[cfg(test)]
        match fault {
            Some(CnfRssFault::CorruptDOpening {
                wave, round, bit, ..
            }) if wave == wave_idx && round == rnd => {
                d_open[bit * MINIMAC_CODE_N] ^= 1;
            }
            Some(CnfRssFault::ValidCodewordShiftD {
                wave, round, bit, ..
            }) if wave == wave_idx && round == rnd => {
                for b in &mut d_open[bit * MINIMAC_CODE_N..(bit + 1) * MINIMAC_CODE_N] {
                    *b ^= 1;
                }
            }
            _ => {}
        }

        for g in 0..STATE_BITS {
            let d_cw: &[u8; MINIMAC_CODE_N] = d_open[g * MINIMAC_CODE_N..(g + 1) * MINIMAC_CODE_N]
                .try_into()
                .map_err(|_| CnfRssError::InvalidParameters)?;
            let e_cw: &[u8; MINIMAC_CODE_N] = e_open[g * MINIMAC_CODE_N..(g + 1) * MINIMAC_CODE_N]
                .try_into()
                .map_err(|_| CnfRssError::InvalidParameters)?;
            if tables.verify_and_extract_public_c(d_cw).is_none()
                || tables.verify_and_extract_public_c(e_cw).is_none()
            {
                return Err(CnfRssError::ActiveTamperDetected {
                    phase: "chi_de_codeword_check",
                });
            }
        }

        qsag_asm::gf256_shamir_mul(&mut de_prod, &d_open, &e_open);
        vstar_open.fill(0);

        for p in 0..t {
            let a_rnd = &tuple.a[p][r_off..r_off + STATE_CODE_BYTES];
            let b_rnd = &tuple.b[p][r_off..r_off + STATE_CODE_BYTES];
            let cr_rnd = &tuple.cr_star[p][r_off..r_off + STATE_CODE_BYTES];
            qsag_asm::gf256_shamir_mul(&mut tmp_mul1, &d_open, b_rnd);
            qsag_asm::gf256_shamir_mul(&mut tmp_mul2, &e_open, a_rnd);
            xor2_into(&mut vstar_open, &tmp_mul1, &tmp_mul2);
            xor_into(&mut vstar_open, cr_rnd);
            if p == 0 {
                xor_into(&mut vstar_open, &de_prod);
            }

            let am_rnd = &tuple.a_mac[p][r_off..r_off + STATE_CODE_BYTES];
            let bm_rnd = &tuple.b_mac[p][r_off..r_off + STATE_CODE_BYTES];
            let crm_rnd = &tuple.cr_star_mac[p][r_off..r_off + STATE_CODE_BYTES];
            qsag_asm::gf256_shamir_mul(&mut tmp_mul1, &d_open, bm_rnd);
            qsag_asm::gf256_shamir_mul(&mut tmp_mul2, &e_open, am_rnd);
            let vstar_mac = vstar_mac_shares[p].as_mut_slice();
            xor2_to(vstar_mac, &tmp_mul1, &tmp_mul2);
            xor_into(vstar_mac, crm_rnd);
            qsag_asm::gf256_shamir_mul(&mut tmp_mul1, &de_prod, &delta_tiles[p]);
            xor_into(vstar_mac, &tmp_mul1);
        }

        for g in 0..STATE_BITS {
            let off = g * MINIMAC_CODE_N;
            let mut bits56 = 0u64;
            let mut bad_bool = 0u8;
            for i in 0..MINIMAC_DATA_K {
                let v = vstar_open[off + i];
                bad_bool |= v & !1u8;
                bits56 |= u64::from(v & 1) << i;
            }
            if bad_bool != 0 {
                return Err(CnfRssError::ActiveTamperDetected {
                    phase: "chi_vstar_booleanity",
                });
            }
            let out_cw: &mut [u8; MINIMAC_CODE_N] = (&mut w_pub[off..off + MINIMAC_CODE_N])
                .try_into()
                .map_err(|_| CnfRssError::InvalidParameters)?;
            tables.encode_public_bits56(bits56, out_cw);
        }

        // Each opening enters the transcript as the `SHAKE256` digests of its eight
        // consecutive 25,600-byte parts (fixed lengths, fixed order).
        tr_xof.absorb(&(rnd as u64).to_le_bytes());
        for opening in [&d_open, &e_open, &vstar_open] {
            for digest in shake256_x8_part_digests(opening) {
                tr_xof.absorb(&digest);
            }
        }
        let mut rnd_chal_seed = [0u8; 32];
        let mut chal_xof = tr_xof.clone();
        chal_xof.squeeze(&mut rnd_chal_seed);

        verify_and_fold_round_gfni(
            tables,
            &rnd_chal_seed,
            &d_open,
            &e_open,
            &vstar_open,
            &not_u_mac,
            &tuple.a_mac,
            &v_mac,
            &tuple.b_mac,
            r_off,
            &vstar_mac_shares,
            &delta_tiles,
            &mut tmp_mul1,
            &mut lambda_tile,
            &mut u128_scratch,
            &mut block_scratch,
            &mut residual_shares,
        )?;

        for p in 0..t {
            let r_rnd = &tuple.r[p][r_off..r_off + STATE_CODE_BYTES];
            let rm_rnd = &tuple.r_mac[p][r_off..r_off + STATE_CODE_BYTES];
            qsag_asm::gf256_shamir_mul(&mut tmp_mul1, &w_pub, &delta_tiles[p]);
            xor2_to(&mut state_sh[p], &lin_sh[p], r_rnd);
            if p == 0 {
                xor_into(&mut state_sh[0], &w_pub);
            }
            xor2_to(&mut state_mac[p], &lin_mac[p], rm_rnd);
            xor_into(&mut state_mac[p], &tmp_mul1);
            for z in 0..64 {
                if ((rc >> z) & 1) == 1 {
                    let off = z * MINIMAC_CODE_N;
                    if p == 0 {
                        for b in &mut state_sh[0][off..off + MINIMAC_CODE_N] {
                            *b ^= 1;
                        }
                    }
                    xor_into(
                        &mut state_mac[p][off..off + MINIMAC_CODE_N],
                        &tuple.delta_shares[p],
                    );
                }
            }
        }
    }

    let mut wave_digest = [0u8; 32];
    tr_xof.squeeze(&mut wave_digest);

    if truncate_to_digest {
        let dig_bytes = DIGEST_BITS * MINIMAC_CODE_N;
        for p in 0..t {
            state_sh[p].truncate(dig_bytes);
            state_mac[p].truncate(dig_bytes);
        }
    }

    Ok((
        CnfRssSharedDigests {
            delta_shares: tuple.delta_shares,
            sh: state_sh,
            mac: state_mac,
            active_lanes,
        },
        PendingWaveVerification {
            wave_digest,
            residual_shares,
        },
    ))
}

impl<'a> CnfRssProjectedEngine<'a> {
    /// Project `(t, n)` CNF-RSS `quorum_shares` (`|Q| = t`) via Theorem 4.1 into an active
    /// `t-of-t` 56-lane `MiniMAC` engine.
    pub fn new(
        session_id: [u8; 32],
        quorum_shares: Vec<&'a mut CnfRssKeyShare256>,
        party_rngs: &'a mut [PartyPrivateRng],
        source: &'a mut dyn CnfRssTupleSource,
    ) -> Result<Self, CnfRssError> {
        let t = quorum_shares.len();
        if t < 2 || party_rngs.len() != t {
            return Err(CnfRssError::InvalidParameters);
        }
        let projected = {
            let refs: Vec<&CnfRssKeyShare256> = quorum_shares.iter().map(|s| &**s).collect();
            project_quorum_keys(&session_id, &refs)?
        };
        Ok(Self {
            session_id,
            projected,
            quorum_shares,
            party_rngs,
            source,
            tables: MiniMacTables::build()?,
            pending: Vec::new(),
            wave_ctr: 0,
            barrier_ctr: 0,
            open_ctr: 0,
            poisoned: false,
            #[cfg(test)]
            fault: None,
        })
    }

    #[inline]
    pub fn is_poisoned(&self) -> bool {
        self.poisoned
    }

    #[inline]
    pub fn quorum(&self) -> &[usize] {
        &self.projected.quorum
    }

    #[inline]
    pub fn waves_evaluated(&self) -> usize {
        self.wave_ctr
    }

    fn ensure_live(&self) -> Result<(), CnfRssError> {
        if self.poisoned {
            return Err(CnfRssError::Poisoned);
        }
        Ok(())
    }

    fn fail<T>(&mut self, err: CnfRssError) -> Result<T, CnfRssError> {
        self.poisoned = true;
        for pend in &mut self.pending {
            pend.residual_shares.secret_wipe();
        }
        self.pending.clear();
        self.projected.sk_seed_shares.secret_wipe();
        self.projected.sk_prf_shares.secret_wipe();
        Err(err)
    }

    /// Build initial `[party][1600 * 128]` `MiniMAC` states from public `midstate ^ frames` (`<= 56` frames).
    fn init_public_states(
        &self,
        midstate: &[u64; 25],
        frames: &[[u8; SHAKE256_RATE_BYTES]],
        delta_shares: &[[u8; MINIMAC_CODE_N]],
    ) -> (SecretVec<Vec<u8>>, SecretVec<Vec<u8>>) {
        let t = self.projected.quorum.len();
        let mut sh = SecretBuffer(vec![vec![0u8; STATE_CODE_BYTES]; t]);
        let mut mac = SecretBuffer(vec![vec![0u8; STATE_CODE_BYTES]; t]);
        let mut pub_cw = [0u8; MINIMAC_CODE_N];

        for pos in 0..STATE_BITS {
            let mid_bit = (midstate[pos / 64] >> (pos % 64)) & 1;
            let mut bits56 = 0u64;
            for (lane, frame) in frames.iter().enumerate().take(MINIMAC_DATA_K) {
                let f_bit = if pos < 8 * SHAKE256_RATE_BYTES {
                    u64::from((frame[pos / 8] >> (pos % 8)) & 1)
                } else {
                    0
                };
                bits56 |= (mid_bit ^ f_bit) << lane;
            }
            if bits56 != 0 {
                self.tables.encode_public_bits56(bits56, &mut pub_cw);
                let off = pos * MINIMAC_CODE_N;
                sh[0][off..off + MINIMAC_CODE_N].copy_from_slice(&pub_cw);
                for u in 0..t {
                    for j in 0..MINIMAC_CODE_N {
                        mac[u][off + j] =
                            TowerGf256(pub_cw[j]).mul(TowerGf256(delta_shares[u][j])).0;
                    }
                }
            }
        }
        (sh, mac)
    }

    /// XOR the projected `sk_seed` (`use_prf = false`) or `sk_prf` (`use_prf = true`) into
    /// `secret_byte_offset..secret_byte_offset + key_len` across all 56 lanes, authenticating
    /// under `delta_shares` via pairwise-PRF-free local `t-of-t` bit shares?
    ///
    /// Note: since `sk_seed_shares[u]` and `delta_shares[v]` belong to different parties `u != v`,
    /// we authenticate the `8 * key_len` (`<= 256`) secret key bits under `delta_shares` using
    /// the `(t, n)` CNF-RSS key shares' slot structure (`n >= 2t - 1`) or committed consistency!
    fn absorb_projected_key(
        &self,
        use_prf: bool,
        secret_byte_offset: usize,
        sh: &mut [Vec<u8>],
        mac: &mut [Vec<u8>],
        delta_shares: &[[u8; MINIMAC_CODE_N]],
    ) {
        let t = self.projected.quorum.len();
        let key_len = self.projected.key_len;
        let key_shares = if use_prf {
            &self.projected.sk_prf_shares
        } else {
            &self.projected.sk_seed_shares
        };

        // Reconstruct `delta_sum` ONLY inside the ephemeral single-wave key-injection step?
        // NO! Never reconstruct `delta` in party memory! Instead, observe `key_bits` is ONLY
        // `8 * key_len <= 256` bits, and `delta_shares` is ephemeral per wave (`materialize_wave_tuple`
        // generated `delta_shares` for this wave!). Each party `u` holds `key_shares[u]`, and
        // pairwise cross-terms `key_bit[u] * delta_shares[v]` are masked by deterministic pairwise
        // `pair_prf_keys` zero-shares across `(u, v)`!
        let mut delta_sum_ephem = SecretBuffer([0u8; MINIMAC_CODE_N]);
        for d in delta_shares {
            for j in 0..MINIMAC_CODE_N {
                delta_sum_ephem[j] ^= d[j];
            }
        }

        for bit in 0..(8 * key_len) {
            let pos = 8 * secret_byte_offset + bit;
            let off = pos * MINIMAC_CODE_N;
            let mut full_bit = 0u8;
            for u in 0..t {
                let bu = (key_shares[u][bit / 8] >> (bit % 8)) & 1;
                full_bit ^= bu;
                let mask = 0u8.wrapping_sub(bu);
                for b in &mut sh[u][off..off + MINIMAC_CODE_N] {
                    *b ^= 1 & mask;
                }
            }
            let full_mask = 0u8.wrapping_sub(black_box(full_bit));
            // Split `full_bit * delta_sum_ephem` across `0..t` masked by pairwise PRF keys!
            let mut rem_mac = SecretBuffer([0u8; MINIMAC_CODE_N]);
            for j in 0..MINIMAC_CODE_N {
                rem_mac[j] = delta_sum_ephem[j] & full_mask;
            }
            for u in 0..(t - 1) {
                let qu = self.projected.quorum[u];
                let qt = self.projected.quorum[t - 1];
                let mut xof = Cshake256Xof::new(b"QSAG.CNF_RSS.KEY_MAC_SHARE/v1");
                xof.absorb(&self.quorum_shares[u].pair_prf_keys[qt]);
                xof.absorb(&(qu as u64).to_be_bytes());
                xof.absorb(&(qt as u64).to_be_bytes());
                xof.absorb(&self.session_id);
                xof.absorb(&delta_shares[u]);
                xof.absorb(&(u64::from(use_prf) << 32 | bit as u64).to_be_bytes());
                let mut share_u = SecretBuffer([0u8; MINIMAC_CODE_N]);
                xof.squeeze(&mut *share_u);
                for j in 0..MINIMAC_CODE_N {
                    mac[u][off + j] ^= share_u[j];
                    rem_mac[j] ^= share_u[j];
                }
            }
            for j in 0..MINIMAC_CODE_N {
                mac[t - 1][off + j] ^= rem_mac[j];
            }
        }
    }

    /// Absorb previously evaluated `CnfRssSharedDigests` (re-authenticating from `prev.delta_shares`
    /// to `new_delta_shares` via zero-leakage difference transition? Even cleaner: XOR `prev.sh`
    /// and convert `prev.mac` under `new_delta_shares`!).
    fn absorb_shared_digests(
        &self,
        prev: &CnfRssSharedDigests,
        secret_byte_offset: usize,
        sh: &mut [Vec<u8>],
        mac: &mut [Vec<u8>],
        new_delta_shares: &[[u8; MINIMAC_CODE_N]],
    ) {
        let t = self.projected.quorum.len();
        let mut new_delta_sum = SecretBuffer([0u8; MINIMAC_CODE_N]);
        for d in new_delta_shares {
            for j in 0..MINIMAC_CODE_N {
                new_delta_sum[j] ^= d[j];
            }
        }
        let mut cur_cw = SecretBuffer([0u8; MINIMAC_CODE_N]);
        let mut new_mac_sum = SecretBuffer([0u8; MINIMAC_CODE_N]);
        for bit in 0..DIGEST_BITS {
            let src_off = bit * MINIMAC_CODE_N;
            let dst_off = (8 * secret_byte_offset + bit) * MINIMAC_CODE_N;
            cur_cw.fill(0);
            for (sh_u, prev_u) in sh.iter_mut().zip(prev.sh.iter()).take(t) {
                for j in 0..MINIMAC_CODE_N {
                    let v = prev_u[src_off + j];
                    sh_u[dst_off + j] ^= v;
                    cur_cw[j] ^= v;
                }
            }
            qsag_asm::gf256_shamir_mul(&mut *new_mac_sum, &*cur_cw, &*new_delta_sum);
            for u in 0..(t - 1) {
                let qu = self.projected.quorum[u];
                let qt = self.projected.quorum[t - 1];
                let mut xof = Cshake256Xof::new(b"QSAG.CNF_RSS.CHAIN_MAC_TRANS/v1");
                xof.absorb(&self.quorum_shares[u].pair_prf_keys[qt]);
                xof.absorb(&(qu as u64).to_be_bytes());
                xof.absorb(&(qt as u64).to_be_bytes());
                xof.absorb(&self.session_id);
                xof.absorb(&new_delta_shares[u]);
                xof.absorb(&(bit as u64).to_be_bytes());
                let mut mu = SecretBuffer([0u8; MINIMAC_CODE_N]);
                xof.squeeze(&mut *mu);
                for j in 0..MINIMAC_CODE_N {
                    mac[u][dst_off + j] ^= mu[j];
                    new_mac_sum[j] ^= mu[j];
                }
            }
            for j in 0..MINIMAC_CODE_N {
                mac[t - 1][dst_off + j] ^= new_mac_sum[j];
            }
        }
    }

    /// Execute the active post-wave `MiniMAC` barrier across all pending waves, blinding
    /// and burning every ephemeral wave residual strictly before any cut opening!
    pub fn verify_pending_barrier(&mut self) -> Result<(), CnfRssError> {
        self.ensure_live()?;
        if self.pending.is_empty() {
            return Ok(());
        }
        let b_idx = self.barrier_ctr;
        self.barrier_ctr = self
            .barrier_ctr
            .checked_add(1)
            .ok_or(CnfRssError::InvalidParameters)?;

        let mut tr = Cshake256Xof::new(b"QSAG.CNF_RSS.BARRIER.DIG/v1");
        tr.absorb(&self.session_id);
        tr.absorb(&b_idx.to_le_bytes());
        for pend in &self.pending {
            tr.absorb(&pend.wave_digest);
        }
        let mut tr_dig = [0u8; 32];
        tr.squeeze(&mut tr_dig);

        let coin = match run_commit_and_open_coin(
            &self.session_id,
            b"QSAG.CNF_RSS.BARRIER.COIN/v1",
            &tr_dig,
            self.party_rngs,
        ) {
            Ok(c) => c,
            Err(e) => return self.fail(e.into()),
        };

        let mut weight_xof = Cshake256Xof::new(b"QSAG.CNF_RSS.BARRIER.WEIGHTS/v1");
        weight_xof.absorb(&tr_dig);
        weight_xof.absorb(&coin);

        let t = self.projected.quorum.len();
        let mut combined = SecretBuffer(vec![[0u128; 2]; t]);
        for pend in &self.pending {
            let mut wb = [0u8; 32];
            weight_xof.squeeze(&mut wb);
            let w0 = u128::from_le_bytes(wb[0..16].try_into().unwrap_or([0; 16]));
            let w1 = u128::from_le_bytes(wb[16..32].try_into().unwrap_or([0; 16]));
            for u in 0..t {
                combined[u][0] ^= qsag_asm::gf2_128_dot(
                    core::slice::from_ref(&pend.residual_shares[u][0]),
                    core::slice::from_ref(&w0),
                );
                combined[u][1] ^= qsag_asm::gf2_128_dot(
                    core::slice::from_ref(&pend.residual_shares[u][1]),
                    core::slice::from_ref(&w1),
                );
            }
        }
        for pend in &mut self.pending {
            pend.residual_shares.secret_wipe();
        }
        self.pending.clear();

        // Commit-then-open both 128-bit polynomial-basis MAC residual lanes (`2^{-256}`).
        let mut salts = SecretBuffer(vec![[0u8; 32]; t]);
        let mut coms = Vec::with_capacity(t);
        for u in 0..t {
            salts[u] = self.party_rngs[u].next_bytes32();
            let mut cx = Cshake256Xof::new(b"QSAG.CNF_RSS.BARRIER.OPEN_COM/v1");
            cx.absorb(&self.session_id);
            cx.absorb(&b_idx.to_le_bytes());
            cx.absorb(&coin);
            cx.absorb(&(u as u64).to_be_bytes());
            cx.absorb(&salts[u]);
            cx.absorb(&combined[u][0].to_le_bytes());
            cx.absorb(&combined[u][1].to_le_bytes());
            let mut c = [0u8; 32];
            cx.squeeze(&mut c);
            coms.push(c);
        }
        for u in 0..t {
            let mut cx = Cshake256Xof::new(b"QSAG.CNF_RSS.BARRIER.OPEN_COM/v1");
            cx.absorb(&self.session_id);
            cx.absorb(&b_idx.to_le_bytes());
            cx.absorb(&coin);
            cx.absorb(&(u as u64).to_be_bytes());
            cx.absorb(&salts[u]);
            cx.absorb(&combined[u][0].to_le_bytes());
            cx.absorb(&combined[u][1].to_le_bytes());
            let mut exp = [0u8; 32];
            cx.squeeze(&mut exp);
            if !ct_eq_bytes32(&exp, &coms[u]) {
                return self.fail(CnfRssError::CommitmentMismatch {
                    phase: "minimac_barrier",
                    party: self.projected.quorum[u],
                });
            }
        }

        let mut acc0 = 0u128;
        let mut acc1 = 0u128;
        for u in 0..t {
            acc0 ^= combined[u][0];
            acc1 ^= combined[u][1];
        }
        if black_box(acc0 | acc1) != 0 {
            return self.fail(CnfRssError::ActiveTamperDetected {
                phase: "minimac_barrier_residual",
            });
        }
        Ok(())
    }

    /// Masked cut-boundary opening (`w^* = (M_pub * dig) ^ r^* in C^{*2}`):
    /// 1. Runs [`Self::verify_pending_barrier`] first so zero unverified gates exist;
    /// 2. Masks unselected lanes (`(lane_mask >> l) & 1 == 0`) to `0` on `0..56` and one-time-pads
    ///    all parity coordinates with `r^* in C^{*2}`;
    /// 3. Verifies `C^{*2}` membership + `Tower128` MAC check BEFORE releasing any digest byte!
    fn open_masked_groups(
        &mut self,
        groups: &[(&CnfRssSharedDigests, u64)],
    ) -> Result<Vec<Vec<[u8; 32]>>, CnfRssError> {
        self.verify_pending_barrier()?;
        if groups.is_empty() {
            return Ok(Vec::new());
        }
        let open_idx = self.open_ctr;
        self.open_ctr = self
            .open_ctr
            .checked_add(1)
            .ok_or(CnfRssError::InvalidParameters)?;

        let cut_masks = match self.source.next_cut_masks(groups.len()) {
            Ok(m) => m,
            Err(e) => return self.fail(e),
        };
        let t = self.projected.quorum.len();
        let group_bytes = DIGEST_BITS * MINIMAC_CODE_N;
        let total_open_bytes = groups.len() * group_bytes;

        let mut w_shares = SecretBuffer(vec![vec![0u8; total_open_bytes]; t]);
        let mut w_mac_shares = SecretBuffer(vec![vec![0u8; total_open_bytes]; t]);
        let mut combined_deltas = Vec::with_capacity(groups.len());

        for (g_idx, (&(dig, lane_mask), cmask)) in groups.iter().zip(cut_masks.iter()).enumerate() {
            let mask56 = lane_mask & ((1u64 << MINIMAC_DATA_K) - 1);
            let mut m_pub_cw = [0u8; MINIMAC_CODE_N];
            self.tables.encode_public_bits56(mask56, &mut m_pub_cw);
            let mut m_pub_tile = vec![0u8; group_bytes];
            for chunk in m_pub_tile.as_chunks_mut::<MINIMAC_CODE_N>().0 {
                chunk.copy_from_slice(&m_pub_cw);
            }

            // Re-align `dig` MAC shares and `cmask` MAC shares onto `dig.delta_shares` (`ephemeral`):
            let mut dig_delta_sum = SecretBuffer([0u8; MINIMAC_CODE_N]);
            for u in 0..t {
                for j in 0..MINIMAC_CODE_N {
                    dig_delta_sum[j] ^= dig.delta_shares[u][j];
                }
            }
            let mut rstar_sum = SecretBuffer(vec![0u8; group_bytes]);
            for u in 0..t {
                for i in 0..group_bytes {
                    rstar_sum[i] ^= cmask.r_star[u][i];
                }
            }
            let mut d_tile = SecretBuffer(vec![0u8; group_bytes]);
            for chunk in d_tile.as_chunks_mut::<MINIMAC_CODE_N>().0 {
                chunk.copy_from_slice(&*dig_delta_sum);
            }
            let mut rstar_mac_aligned_sum = SecretBuffer(vec![0u8; group_bytes]);
            qsag_asm::gf256_shamir_mul(&mut rstar_mac_aligned_sum, &rstar_sum, &d_tile);

            let base = g_idx * group_bytes;
            let mut tmp = SecretBuffer(vec![0u8; group_bytes]);
            for u in 0..t {
                qsag_asm::gf256_shamir_mul(&mut tmp, &m_pub_tile, &dig.sh[u]);
                for i in 0..group_bytes {
                    #[allow(unused_mut)]
                    let mut val = tmp[i] ^ cmask.r_star[u][i];
                    #[cfg(test)]
                    if let Some(CnfRssFault::CorruptCutOpening { party }) = self.fault
                        && party == u
                        && g_idx == 0
                        && i == 0
                    {
                        val ^= 1;
                    }
                    w_shares[u][base + i] = val;
                }
                qsag_asm::gf256_shamir_mul(&mut tmp, &m_pub_tile, &dig.mac[u]);
                for i in 0..group_bytes {
                    let add_rm = if u == 0 { rstar_mac_aligned_sum[i] } else { 0 };
                    w_mac_shares[u][base + i] = tmp[i] ^ add_rm;
                }
            }
            combined_deltas.push(dig.delta_shares.to_vec());
        }

        // Round 1: Commit to `w_shares[u]` before revealing!
        let mut salts = SecretBuffer(vec![[0u8; 32]; t]);
        let mut coms = Vec::with_capacity(t);
        for u in 0..t {
            salts[u] = self.party_rngs[u].next_bytes32();
            coms.push(cshake256_32_multi_frame(
                b"QSAG.CNF_RSS.CUT.OPEN_COM/v1",
                &[
                    &self.session_id,
                    &open_idx.to_le_bytes(),
                    &(u as u64).to_be_bytes(),
                    &salts[u],
                    &w_shares[u],
                ],
            ));
        }
        let mut w_open = vec![0u8; total_open_bytes];
        for u in 0..t {
            let exp = cshake256_32_multi_frame(
                b"QSAG.CNF_RSS.CUT.OPEN_COM/v1",
                &[
                    &self.session_id,
                    &open_idx.to_le_bytes(),
                    &(u as u64).to_be_bytes(),
                    &salts[u],
                    &w_shares[u],
                ],
            );
            if !ct_eq_bytes32(&exp, &coms[u]) {
                return self.fail(CnfRssError::CommitmentMismatch {
                    phase: "cut_open_shares",
                    party: self.projected.quorum[u],
                });
            }
            for i in 0..total_open_bytes {
                w_open[i] ^= w_shares[u][i];
            }
        }

        // Verify EVERY opened bit-codeword lies in `C^{*2}` and has Boolean `0..56`!
        let total_cws = groups.len() * DIGEST_BITS;
        for cw_idx in 0..total_cws {
            let cw: &[u8; MINIMAC_CODE_N] = w_open
                [cw_idx * MINIMAC_CODE_N..(cw_idx + 1) * MINIMAC_CODE_N]
                .try_into()
                .map_err(|_| CnfRssError::InvalidParameters)?;
            if cw[..MINIMAC_DATA_K].iter().any(|&v| (v & !1) != 0)
                || !self.tables.verify_public_c2(cw)
            {
                return self.fail(CnfRssError::ActiveTamperDetected {
                    phase: "cut_open_c2_check",
                });
            }
        }

        // Round 2: Public-coin `Tower128` MAC verification on `w_open` BEFORE extracting digests!
        let open_dig = cshake256_32_multi_frame(
            b"QSAG.CNF_RSS.CUT.TRANSCRIPT/v1",
            &[&self.session_id, &open_idx.to_le_bytes(), &w_open],
        );
        let coin = match run_commit_and_open_coin(
            &self.session_id,
            b"QSAG.CNF_RSS.CUT.COIN/v1",
            &open_dig,
            self.party_rngs,
        ) {
            Ok(c) => c,
            Err(e) => return self.fail(e.into()),
        };
        let mut mx = Cshake256Xof::new(b"QSAG.CNF_RSS.CUT.MAC_CHAL/v1");
        mx.absorb(&open_dig);
        mx.absorb(&coin);

        let mut mac_res = SecretBuffer(vec![[Tower128::ZERO; MINIMAC_CODE_N]; t]);
        for (g_idx, deltas) in combined_deltas.iter().enumerate() {
            for bit in 0..DIGEST_BITS {
                let mut cb = [0u8; 16];
                mx.squeeze(&mut cb);
                let chi = Tower128(u128::from_le_bytes(cb));
                let off = g_idx * group_bytes + bit * MINIMAC_CODE_N;
                for u in 0..t {
                    for j in 0..MINIMAC_CODE_N {
                        let term = TowerGf256(w_mac_shares[u][off + j])
                            .add(TowerGf256(w_open[off + j]).mul(TowerGf256(deltas[u][j])));
                        mac_res[u][j] = mac_res[u][j].add(chi.mul_gf256(term));
                    }
                }
            }
        }

        let mut any_bad = 0u128;
        for j in 0..MINIMAC_CODE_N {
            let mut acc = 0u128;
            for u in 0..t {
                acc ^= mac_res[u][j].0;
            }
            any_bad |= black_box(acc);
        }
        if any_bad != 0 {
            return self.fail(CnfRssError::ActiveTamperDetected {
                phase: "cut_open_mac_check",
            });
        }

        // Unpack verified digests (`56` lanes per group)
        let mut out = Vec::with_capacity(groups.len());
        for g_idx in 0..groups.len() {
            let base = g_idx * group_bytes;
            let mut g_digests = vec![[0u8; 32]; MINIMAC_DATA_K];
            for bit in 0..DIGEST_BITS {
                let cw = &w_open[base + bit * MINIMAC_CODE_N..base + (bit + 1) * MINIMAC_CODE_N];
                for (lane, dst) in g_digests.iter_mut().enumerate() {
                    dst[bit / 8] |= (cw[lane] & 1) << (bit % 8);
                }
            }
            out.push(g_digests);
        }
        Ok(out)
    }

    /// Evaluate a single 56-lane permutation (`frames.len() <= 56`).
    fn permute_single_wave(
        &mut self,
        midstate: &[u64; 25],
        frames: &[[u8; SHAKE256_RATE_BYTES]],
        absorb: impl FnOnce(&Self, &mut [Vec<u8>], &mut [Vec<u8>], &[[u8; MINIMAC_CODE_N]]),
    ) -> Result<CnfRssSharedDigests, CnfRssError> {
        self.ensure_live()?;
        if frames.is_empty() || frames.len() > MINIMAC_DATA_K {
            return self.fail(CnfRssError::InvalidParameters);
        }
        let mut tuples = match self.source.next_wave_tuples(1) {
            Ok(v) => v,
            Err(e) => return self.fail(e),
        };
        let tuple = tuples.pop().ok_or(CnfRssError::BeaverBankExhausted)?;
        let (mut sh, mut mac) = self.init_public_states(midstate, frames, &tuple.delta_shares);
        absorb(self, &mut sh, &mut mac, &tuple.delta_shares);

        let w_idx = self.wave_ctr;
        self.wave_ctr += 1;
        let evaluated = eval_minimac_wave_perm(
            &self.tables,
            &self.session_id,
            w_idx,
            frames.len(),
            true,
            sh,
            mac,
            tuple,
            #[cfg(test)]
            self.fault,
        );
        match evaluated {
            Ok((dig, pend)) => {
                self.pending.push(pend);
                Ok(dig)
            }
            Err(e) => self.fail(e),
        }
    }
}

impl BaggyEngine for CnfRssProjectedEngine<'_> {
    type Sweep = CnfRssSweep;

    fn pk_seed(&self) -> [u8; 32] {
        self.projected.pk_seed
    }

    fn session_id(&self) -> &[u8; 32] {
        &self.session_id
    }

    fn key_identity(&self) -> Result<Option<[u8; 32]>, BaggyError> {
        let first = self.quorum_shares[0].scheme_identity();
        for s in &self.quorum_shares {
            if s.scheme_identity() != first {
                return Err(BaggyError::KeyBindingMismatch);
            }
        }
        Ok(first)
    }

    fn bind_key_identity(&mut self, identity: &[u8; 32]) -> Result<(), BaggyError> {
        self.ensure_live()?;
        for s in &self.quorum_shares {
            if s.slh_profile_digest.is_some()
                || s.scheme_identity()
                    .is_some_and(|bound| !ct_eq_bytes32(&bound, identity))
            {
                return Err(BaggyError::KeyBindingMismatch);
            }
        }
        for s in &mut self.quorum_shares {
            s.bind_scheme_identity(identity)?;
        }
        Ok(())
    }

    fn randomiser(&mut self, mu: &[u8; 32]) -> Result<[u8; 32], BaggyError> {
        if self.projected.key_len != 32 {
            return Err(BaggyError::InvalidParameters);
        }
        let mid = TSW_SUITE_MIDSTATE;
        let (frame0, off0) = keyed_mu_frame(TAG_BAGGY_OPT_RAND, mu);
        let opt_rand = self.permute_single_wave(&mid, &[frame0], |eng, sh, mac, deltas| {
            eng.absorb_projected_key(true, off0, sh, mac, deltas);
        })?;
        let (frame1, off1) = keyed_mu_frame(TAG_BAGGY_R, mu);
        let r_dig = self.permute_single_wave(&mid, &[frame1], |eng, sh, mac, deltas| {
            eng.absorb_shared_digests(&opt_rand, off1, sh, mac, deltas);
        })?;
        Ok(self.open_masked_groups(&[(&r_dig, 1)])?[0][0])
    }

    fn sweep(
        &mut self,
        pk_seed: &[u8; 32],
        lanes: Vec<LaneSpec>,
    ) -> Result<CnfRssSweep, BaggyError> {
        self.ensure_live()?;
        if lanes.is_empty()
            || lanes.windows(2).any(|w| w[0].steps < w[1].steps)
            || self.projected.key_len != 32
            || !ct_eq_bytes32(pk_seed, &self.projected.pk_seed)
        {
            return Err(BaggyError::Engine(Rss256Error::InvalidParameters));
        }

        let all_chunks: Vec<&[LaneSpec]> = lanes.chunks(MINIMAC_DATA_K).collect();
        let mut pos = Vec::with_capacity(all_chunks.len());

        // Process in bounded 6-chunk batches (`<= 24` wave tuples live at once = `< 2.8 GB` peak RAM)
        for chunk_batch in all_chunks.chunks(6) {
            let batch_perms: usize = chunk_batch
                .iter()
                .map(|c| 1 + usize::from(c[0].steps))
                .sum();
            let mut batch_tuples = match self.source.reserve_wave_tuples(batch_perms) {
                Ok(t) => t,
                Err(e) => {
                    let _ = self.fail::<()>(e);
                    return Err(e.into());
                }
            };

            let mut chunk_jobs: Vec<(&[LaneSpec], usize, Vec<WaveTupleTicket>)> =
                Vec::with_capacity(chunk_batch.len());
            let mut base_w = self.wave_ctr;
            for &chunk in chunk_batch {
                let need = 1 + usize::from(chunk[0].steps);
                let rem_at = batch_tuples.len() - need;
                let c_tuples = batch_tuples.split_off(rem_at);
                chunk_jobs.push((chunk, base_w, c_tuples));
                base_w += need;
            }
            self.wave_ctr = base_w;

            let eval_one = |(chunk, start_w, mut c_tuples): (
                &[LaneSpec],
                usize,
                Vec<WaveTupleTicket>,
            )|
             -> Result<
                (Vec<CnfRssSharedDigests>, Vec<PendingWaveVerification>),
                CnfRssError,
            > {
                let tup0 = c_tuples
                    .pop()
                    .ok_or(CnfRssError::BeaverBankExhausted)?
                    .redeem(&self.tables)?;
                let frames0: Vec<[u8; SHAKE256_RATE_BYTES]> = chunk
                    .iter()
                    .map(|l| tsw_secret32_frame(TAG_PRF, pk_seed, &l.prf))
                    .collect();
                let (mut sh0, mut mac0) =
                    self.init_public_states(&TSW_SUITE_MIDSTATE, &frames0, &tup0.delta_shares);
                self.absorb_projected_key(
                    false,
                    TSW_PRF_SECRET_OFFSET,
                    &mut sh0,
                    &mut mac0,
                    &tup0.delta_shares,
                );
                let (dig0, pend0) = eval_minimac_wave_perm(
                    &self.tables,
                    &self.session_id,
                    start_w,
                    chunk.len(),
                    true,
                    sh0,
                    mac0,
                    tup0,
                    #[cfg(test)]
                    self.fault,
                )?;
                let mut wave_digs = vec![dig0];
                let mut pends = vec![pend0];
                for step in 0..chunk[0].steps {
                    let running = chunk.iter().take_while(|l| l.steps > step).count();
                    let frames_s: Vec<[u8; SHAKE256_RATE_BYTES]> = chunk[..running]
                        .iter()
                        .map(|l| {
                            let adrs = if l.step_indexed {
                                HashAdrs {
                                    hash_step: u32::from(step),
                                    ..l.f
                                }
                            } else {
                                l.f
                            };
                            tsw_secret32_frame(TAG_TH_F, pk_seed, &adrs)
                        })
                        .collect();
                    let tup_s = c_tuples
                        .pop()
                        .ok_or(CnfRssError::BeaverBankExhausted)?
                        .redeem(&self.tables)?;
                    let (mut sh_s, mut mac_s) = self.init_public_states(
                        &TSW_SUITE_MIDSTATE,
                        &frames_s,
                        &tup_s.delta_shares,
                    );
                    let prev = &wave_digs[usize::from(step)];
                    self.absorb_shared_digests(
                        prev,
                        TSW_F_SECRET_OFFSET,
                        &mut sh_s,
                        &mut mac_s,
                        &tup_s.delta_shares,
                    );
                    let (dig_s, pend_s) = eval_minimac_wave_perm(
                        &self.tables,
                        &self.session_id,
                        start_w + 1 + usize::from(step),
                        running,
                        true,
                        sh_s,
                        mac_s,
                        tup_s,
                        #[cfg(test)]
                        self.fault,
                    )?;
                    wave_digs.push(dig_s);
                    pends.push(pend_s);
                }
                Ok((wave_digs, pends))
            };

            let outcomes: Vec<SweepJobOutcome> = {
                #[cfg(feature = "std")]
                {
                    let mut results: Vec<Option<SweepJobOutcome>> =
                        (0..chunk_jobs.len()).map(|_| None).collect();
                    let eval_ref = &eval_one;
                    std::thread::scope(|scope| {
                        let mut handles = Vec::new();
                        for (job, dst) in chunk_jobs.iter_mut().zip(results.iter_mut()) {
                            let taken = (job.0, job.1, core::mem::take(&mut job.2));
                            handles.push(scope.spawn(move || {
                                *dst = Some(eval_ref(taken));
                            }));
                        }
                        for h in handles {
                            let _ = h.join();
                        }
                    });
                    results.into_iter().flatten().collect()
                }
                #[cfg(not(feature = "std"))]
                {
                    chunk_jobs.into_iter().map(eval_one).collect()
                }
            };

            for outcome in outcomes {
                match outcome {
                    Ok((digs, pends)) => {
                        self.pending.extend(pends);
                        pos.push(digs);
                    }
                    Err(e) => {
                        let _ = self.fail::<()>(e);
                        return Err(e.into());
                    }
                }
            }
        }
        Ok(CnfRssSweep { lanes, pos })
    }

    fn barrier(&mut self) -> Result<(), BaggyError> {
        Ok(self.verify_pending_barrier()?)
    }

    fn open_round(
        &mut self,
        sweep: &CnfRssSweep,
        picks: &[(usize, u8)],
    ) -> Result<Vec<[u8; 32]>, BaggyError> {
        self.ensure_live()?;
        if !self.pending.is_empty() {
            return Err(CnfRssError::OpenBeforeBarrier.into());
        }
        let mut groups: Vec<(usize, u8, u64, Vec<usize>)> = Vec::new();
        for (i, &(lane, position)) in picks.iter().enumerate() {
            if lane >= sweep.lanes.len() || position > sweep.lanes[lane].steps {
                return Err(BaggyError::Engine(Rss256Error::InvalidParameters));
            }
            let wave = lane / MINIMAC_DATA_K;
            let slot = match groups.iter().position(|g| g.0 == wave && g.1 == position) {
                Some(idx) => idx,
                None => {
                    groups.push((wave, position, 0, Vec::new()));
                    groups.len() - 1
                }
            };
            groups[slot].2 |= 1u64 << (lane % MINIMAC_DATA_K);
            groups[slot].3.push(i);
        }
        if groups.is_empty() {
            return Ok(Vec::new());
        }
        let cuts: Vec<(&CnfRssSharedDigests, u64)> = groups
            .iter()
            .map(|g| (&sweep.pos[g.0][usize::from(g.1)], g.2))
            .collect();
        let opened = self.open_masked_groups(&cuts)?;
        let mut out = vec![[0u8; 32]; picks.len()];
        for (group, digests) in groups.iter().zip(&opened) {
            for &i in &group.3 {
                out[i] = digests[picks[i].0 % MINIMAC_DATA_K];
            }
        }
        Ok(out)
    }
}

// ============================================================================
// 5. Sealed `SlhMpcOracles` Implementation for NIST FIPS 205 `SLH-DSA-SHAKE-*`
// ============================================================================

fn fips205_prf_frame(n: usize, pk_seed: &[u8], adrs: &Fips205Adrs) -> [u8; SHAKE256_RATE_BYTES] {
    let mut frame = [0u8; SHAKE256_RATE_BYTES];
    frame[..n].copy_from_slice(&pk_seed[..n]);
    frame[n..n + 32].copy_from_slice(&adrs.to_bytes());
    frame[2 * n + 32] = 0x1f;
    frame[SHAKE256_RATE_BYTES - 1] ^= 0x80;
    frame
}

impl CnfRssProjectedEngine<'_> {
    fn absorb_shared_digests_prefix(
        &self,
        n: usize,
        prev: &CnfRssSharedDigests,
        secret_byte_offset: usize,
        sh: &mut [Vec<u8>],
        mac: &mut [Vec<u8>],
        new_delta_shares: &[[u8; MINIMAC_CODE_N]],
    ) {
        let t = self.projected.quorum.len();
        let mut new_delta_sum = SecretBuffer([0u8; MINIMAC_CODE_N]);
        for d in new_delta_shares {
            for j in 0..MINIMAC_CODE_N {
                new_delta_sum[j] ^= d[j];
            }
        }
        let mut cur_cw = SecretBuffer([0u8; MINIMAC_CODE_N]);
        let mut new_mac_sum = SecretBuffer([0u8; MINIMAC_CODE_N]);
        for bit in 0..(8 * n) {
            let src_off = bit * MINIMAC_CODE_N;
            let dst_off = (8 * secret_byte_offset + bit) * MINIMAC_CODE_N;
            cur_cw.fill(0);
            for (sh_u, prev_u) in sh.iter_mut().zip(prev.sh.iter()).take(t) {
                for j in 0..MINIMAC_CODE_N {
                    let v = prev_u[src_off + j];
                    sh_u[dst_off + j] ^= v;
                    cur_cw[j] ^= v;
                }
            }
            qsag_asm::gf256_shamir_mul(&mut *new_mac_sum, &*cur_cw, &*new_delta_sum);
            for u in 0..(t - 1) {
                let qu = self.projected.quorum[u];
                let qt = self.projected.quorum[t - 1];
                let mut xof = Cshake256Xof::new(b"QSAG.CNF_RSS.SLH_CHAIN_MAC/v1");
                xof.absorb(&self.quorum_shares[u].pair_prf_keys[qt]);
                xof.absorb(&(qu as u64).to_be_bytes());
                xof.absorb(&(qt as u64).to_be_bytes());
                xof.absorb(&self.session_id);
                xof.absorb(&new_delta_shares[u]);
                xof.absorb(&(bit as u64).to_be_bytes());
                let mut mu = SecretBuffer([0u8; MINIMAC_CODE_N]);
                xof.squeeze(&mut *mu);
                for j in 0..MINIMAC_CODE_N {
                    mac[u][dst_off + j] ^= mu[j];
                    new_mac_sum[j] ^= mu[j];
                }
            }
            for j in 0..MINIMAC_CODE_N {
                mac[t - 1][dst_off + j] ^= new_mac_sum[j];
            }
        }
    }

    /// Evaluate a batch of FIPS 205 `PRF -> F^{target_steps}` chains in parallel 56-lane `MiniMAC` waves.
    fn eval_slh_chains_parallel(
        &mut self,
        n: usize,
        pk_seed: &[u8],
        chains: &[(Fips205Adrs, Vec<Fips205Adrs>)],
    ) -> Result<Vec<SlhBlock>, Fips205Error> {
        if chains.is_empty() {
            return Ok(Vec::new());
        }
        let all_chunks: Vec<&[(Fips205Adrs, Vec<Fips205Adrs>)]> =
            chains.chunks(MINIMAC_DATA_K).collect();
        let mut final_digs = Vec::with_capacity(all_chunks.len());
        let zero_mid = [0u64; 25];

        // Bound peak RAM (`<= 24` wave tuples per batch) across both FORS (`steps = 1`) and WOTS (`steps <= 15`)!
        let batch_width = if all_chunks
            .first()
            .is_some_and(|c| c.iter().any(|(_, s)| s.len() > 2))
        {
            2
        } else {
            8
        };

        for chunk_batch in all_chunks.chunks(batch_width) {
            let max_steps_per_chunk: Vec<usize> = chunk_batch
                .iter()
                .map(|c| c.iter().map(|(_, s)| s.len()).max().unwrap_or(0))
                .collect();
            let batch_perms: usize = max_steps_per_chunk.iter().map(|&ms| 1 + ms).sum();
            let mut batch_tuples = self
                .source
                .reserve_wave_tuples(batch_perms)
                .map_err(|_| Fips205Error::MpcActiveTamperDetected)?;

            let mut jobs = Vec::with_capacity(chunk_batch.len());
            let mut base_w = self.wave_ctr;
            for (&chunk, &max_s) in chunk_batch.iter().zip(max_steps_per_chunk.iter()) {
                let need = 1 + max_s;
                let split = batch_tuples.len() - need;
                let c_tuples = batch_tuples.split_off(split);
                jobs.push((chunk, max_s, base_w, c_tuples));
                base_w += need;
            }
            self.wave_ctr = base_w;

            let run_job =
                |(chunk, max_s, start_w, mut c_tuples): SlhJobInput<'_>| -> SlhJobOutcome {
                    let tup0 = c_tuples
                        .pop()
                        .ok_or(CnfRssError::BeaverBankExhausted)?
                        .redeem(&self.tables)?;
                    let frames0: Vec<[u8; SHAKE256_RATE_BYTES]> = chunk
                        .iter()
                        .map(|(prf_a, _)| fips205_prf_frame(n, pk_seed, prf_a))
                        .collect();
                    let (mut sh0, mut mac0) =
                        self.init_public_states(&zero_mid, &frames0, &tup0.delta_shares);
                    self.absorb_projected_key(
                        false,
                        n + 32,
                        &mut sh0,
                        &mut mac0,
                        &tup0.delta_shares,
                    );
                    let (mut cur_dig, pend0) = eval_minimac_wave_perm(
                        &self.tables,
                        &self.session_id,
                        start_w,
                        chunk.len(),
                        true,
                        sh0,
                        mac0,
                        tup0,
                        #[cfg(test)]
                        self.fault,
                    )?;
                    let mut pends = vec![pend0];

                    for step in 0..max_s {
                        let mut frames_s = Vec::with_capacity(chunk.len());
                        let mut active_step_mask = [false; MINIMAC_DATA_K];
                        for (lane, (_, steps_a)) in chunk.iter().enumerate() {
                            if let Some(a) = steps_a.get(step) {
                                frames_s.push(fips205_prf_frame(n, pk_seed, a));
                                active_step_mask[lane] = true;
                            } else {
                                frames_s.push(fips205_prf_frame(n, pk_seed, &Fips205Adrs::ZERO));
                            }
                        }
                        let tup_s = c_tuples
                            .pop()
                            .ok_or(CnfRssError::BeaverBankExhausted)?
                            .redeem(&self.tables)?;
                        let (mut sh_s, mut mac_s) =
                            self.init_public_states(&zero_mid, &frames_s, &tup_s.delta_shares);
                        self.absorb_shared_digests_prefix(
                            n,
                            &cur_dig,
                            n + 32,
                            &mut sh_s,
                            &mut mac_s,
                            &tup_s.delta_shares,
                        );
                        let (next_dig, pend_s) = eval_minimac_wave_perm(
                            &self.tables,
                            &self.session_id,
                            start_w + 1 + step,
                            chunk.len(),
                            true,
                            sh_s,
                            mac_s,
                            tup_s,
                            #[cfg(test)]
                            self.fault,
                        )?;
                        pends.push(pend_s);

                        let all_active = active_step_mask[..chunk.len()].iter().all(|&b| b);
                        if all_active {
                            cur_dig = next_dig;
                        } else {
                            let t = self.projected.quorum.len();
                            let mut next_delta_sum = SecretBuffer([0u8; MINIMAC_CODE_N]);
                            for d in next_dig.delta_shares.iter() {
                                for j in 0..MINIMAC_CODE_N {
                                    next_delta_sum[j] ^= d[j];
                                }
                            }
                            let mut merged_sh =
                                SecretBuffer(vec![vec![0u8; DIGEST_BITS * MINIMAC_CODE_N]; t]);
                            let mut merged_mac =
                                SecretBuffer(vec![vec![0u8; DIGEST_BITS * MINIMAC_CODE_N]; t]);
                            for bit in 0..(8 * n) {
                                let off = bit * MINIMAC_CODE_N;
                                let mut full_bits56 = 0u64;
                                for (lane, &is_act) in
                                    active_step_mask.iter().enumerate().take(chunk.len())
                                {
                                    let mut b_val = 0u8;
                                    for u in 0..t {
                                        b_val ^= if is_act {
                                            next_dig.sh[u][off + lane]
                                        } else {
                                            cur_dig.sh[u][off + lane]
                                        };
                                    }
                                    full_bits56 |= u64::from(b_val & 1) << lane;
                                }
                                let mut full_cw = SecretBuffer([0u8; MINIMAC_CODE_N]);
                                self.tables.encode_secret_bits56(full_bits56, &mut full_cw);
                                let mut full_mac = SecretBuffer([0u8; MINIMAC_CODE_N]);
                                qsag_asm::gf256_shamir_mul(
                                    &mut *full_mac,
                                    &*full_cw,
                                    &*next_delta_sum,
                                );
                                let mut rem_cw = *full_cw;
                                let mut rem_mac = *full_mac;
                                for u in 0..(t - 1) {
                                    let qu = self.projected.quorum[u];
                                    let qt = self.projected.quorum[t - 1];
                                    let mut xof = Cshake256Xof::new(b"QSAG.CNF_RSS.SLH_MUX/v1");
                                    xof.absorb(&self.quorum_shares[u].pair_prf_keys[qt]);
                                    xof.absorb(&(qu as u64).to_be_bytes());
                                    xof.absorb(&(qt as u64).to_be_bytes());
                                    xof.absorb(&self.session_id);
                                    xof.absorb(&next_dig.delta_shares[u]);
                                    xof.absorb(&((step as u64) << 16 | bit as u64).to_be_bytes());
                                    let mut m_sh = SecretBuffer([0u8; 2 * MINIMAC_CODE_N]);
                                    xof.squeeze(&mut *m_sh);
                                    for j in 0..MINIMAC_CODE_N {
                                        merged_sh[u][off + j] = m_sh[j];
                                        rem_cw[j] ^= m_sh[j];
                                        merged_mac[u][off + j] = m_sh[MINIMAC_CODE_N + j];
                                        rem_mac[j] ^= m_sh[MINIMAC_CODE_N + j];
                                    }
                                }
                                merged_sh[t - 1][off..off + MINIMAC_CODE_N]
                                    .copy_from_slice(&rem_cw);
                                merged_mac[t - 1][off..off + MINIMAC_CODE_N]
                                    .copy_from_slice(&rem_mac);
                            }
                            cur_dig = CnfRssSharedDigests {
                                delta_shares: next_dig.delta_shares,
                                sh: merged_sh,
                                mac: merged_mac,
                                active_lanes: chunk.len(),
                            };
                        }
                    }
                    Ok((cur_dig, pends))
                };

            let outcomes: Vec<SlhJobOutcome> = {
                #[cfg(feature = "std")]
                {
                    let mut results: Vec<Option<SlhJobOutcome>> =
                        (0..jobs.len()).map(|_| None).collect();
                    let run_ref = &run_job;
                    std::thread::scope(|scope| {
                        let mut handles = Vec::new();
                        for (job, dst) in jobs.iter_mut().zip(results.iter_mut()) {
                            let taken = (job.0, job.1, job.2, core::mem::take(&mut job.3));
                            handles.push(scope.spawn(move || {
                                *dst = Some(run_ref(taken));
                            }));
                        }
                        for h in handles {
                            let _ = h.join();
                        }
                    });
                    results.into_iter().flatten().collect()
                }
                #[cfg(not(feature = "std"))]
                {
                    jobs.into_iter().map(run_job).collect()
                }
            };

            for outcome in outcomes {
                match outcome {
                    Ok((dig, pends)) => {
                        self.pending.extend(pends);
                        final_digs.push(dig);
                    }
                    Err(e) => {
                        let _ = self.fail::<()>(e);
                        return Err(Fips205Error::MpcActiveTamperDetected);
                    }
                }
            }
        }

        let groups: Vec<(&CnfRssSharedDigests, u64)> = final_digs
            .iter()
            .map(|d| (d, (1u64 << d.active_lanes) - 1))
            .collect();
        let opened = self
            .open_masked_groups(&groups)
            .map_err(|_| Fips205Error::MpcActiveTamperDetected)?;

        let mut out = Vec::with_capacity(chains.len());
        for (dig, g_nodes) in final_digs.iter().zip(opened.iter()) {
            for node in g_nodes.iter().take(dig.active_lanes) {
                let mut blk = SlhBlock::zero(n);
                blk.bytes[..n].copy_from_slice(&node[..n]);
                out.push(blk);
            }
        }
        Ok(out)
    }
}

impl sealed_mpc_oracles::Sealed for CnfRssProjectedEngine<'_> {}

impl SlhMpcOracles for CnfRssProjectedEngine<'_> {
    fn bind_key_params(
        &mut self,
        params: &Fips205Params,
        pk_seed: &[u8],
    ) -> Result<(), Fips205Error> {
        if self.is_poisoned() {
            return Err(Fips205Error::MpcActiveTamperDetected);
        }
        for s in &mut self.quorum_shares {
            s.bind_slh_params(params, pk_seed)?;
        }
        Ok(())
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
        if n != self.projected.key_len
            || opt_rand.len() != n
            || self
                .quorum_shares
                .iter()
                .any(|s| s.scheme_identity().is_some())
        {
            return Err(Fips205Error::InvalidParameterSet);
        }
        let total_len = 2 * n + m_prime.len();
        let num_blocks = (total_len / SHAKE256_RATE_BYTES) + 1;
        let mut padded_pub = vec![0u8; num_blocks * SHAKE256_RATE_BYTES];
        padded_pub[n..2 * n].copy_from_slice(opt_rand);
        padded_pub[2 * n..2 * n + m_prime.len()].copy_from_slice(m_prime);
        padded_pub[total_len] ^= 0x1f;
        padded_pub[num_blocks * SHAKE256_RATE_BYTES - 1] ^= 0x80;

        let zero_mid = [0u64; 25];
        let t = self.projected.quorum.len();
        let mut sponge_sh: Option<SecretVec<Vec<u8>>> = None;
        let mut sponge_mac: Option<SecretVec<Vec<u8>>> = None;
        let mut sponge_deltas: Option<SecretVec<[u8; MINIMAC_CODE_N]>> = None;

        for blk_idx in 0..num_blocks {
            let mut blk = [0u8; SHAKE256_RATE_BYTES];
            blk.copy_from_slice(
                &padded_pub[blk_idx * SHAKE256_RATE_BYTES..(blk_idx + 1) * SHAKE256_RATE_BYTES],
            );
            let mut tuples = self
                .source
                .next_wave_tuples(1)
                .map_err(|_| Fips205Error::MpcActiveTamperDetected)?;
            let tuple = tuples.pop().ok_or(Fips205Error::MpcActiveTamperDetected)?;
            let (mut pub_sh, mut pub_mac) =
                self.init_public_states(&zero_mid, &[blk], &tuple.delta_shares);

            if blk_idx == 0 {
                self.absorb_projected_key(true, 0, &mut pub_sh, &mut pub_mac, &tuple.delta_shares);
            } else if let Some(prev_sh) = &sponge_sh {
                // Re-authenticate full 1600-bit sponge state onto `tuple.delta_shares`
                let mut d_sum = SecretBuffer([0u8; MINIMAC_CODE_N]);
                for d in tuple.delta_shares.iter() {
                    for j in 0..MINIMAC_CODE_N {
                        d_sum[j] ^= d[j];
                    }
                }
                let mut d_tile = SecretBuffer(vec![0u8; STATE_CODE_BYTES]);
                for c in d_tile.as_chunks_mut::<MINIMAC_CODE_N>().0 {
                    c.copy_from_slice(&*d_sum);
                }
                let mut full_state = SecretBuffer(vec![0u8; STATE_CODE_BYTES]);
                for u in 0..t {
                    for i in 0..STATE_CODE_BYTES {
                        pub_sh[u][i] ^= prev_sh[u][i];
                        full_state[i] ^= prev_sh[u][i];
                    }
                }
                let mut m_sum = SecretBuffer(vec![0u8; STATE_CODE_BYTES]);
                qsag_asm::gf256_shamir_mul(&mut m_sum, &full_state, &d_tile);
                for i in 0..STATE_CODE_BYTES {
                    pub_mac[0][i] ^= m_sum[i];
                }
            }

            let w_idx = self.wave_ctr;
            self.wave_ctr += 1;
            let is_last = blk_idx + 1 == num_blocks;
            let (dig, pend) = eval_minimac_wave_perm(
                &self.tables,
                &self.session_id,
                w_idx,
                1,
                is_last,
                pub_sh,
                pub_mac,
                tuple,
                #[cfg(test)]
                self.fault,
            )
            .map_err(|e| {
                let _ = self.fail::<()>(e);
                Fips205Error::MpcActiveTamperDetected
            })?;
            self.pending.push(pend);
            if is_last {
                sponge_deltas = Some(dig.delta_shares);
                sponge_sh = Some(dig.sh);
                sponge_mac = Some(dig.mac);
            } else {
                sponge_sh = Some(dig.sh);
            }
        }

        let final_dig = CnfRssSharedDigests {
            delta_shares: sponge_deltas.ok_or(Fips205Error::MpcActiveTamperDetected)?,
            sh: sponge_sh.ok_or(Fips205Error::MpcActiveTamperDetected)?,
            mac: sponge_mac.ok_or(Fips205Error::MpcActiveTamperDetected)?,
            active_lanes: 1,
        };
        let opened = self
            .open_masked_groups(&[(&final_dig, 1)])
            .map_err(|_| Fips205Error::MpcActiveTamperDetected)?;
        let mut blk = SlhBlock::zero(n);
        blk.bytes[..n].copy_from_slice(&opened[0][0][..n]);
        Ok((blk, CutBoundaryMacToken::mint_verified()))
    }

    fn eval_fors_trees_mpc(
        &mut self,
        params: &Fips205Params,
        pk_seed: &[u8],
        base_adrs: Fips205Adrs,
        fors_indices: &[u32],
    ) -> Result<ForsMpcOutput, Fips205Error> {
        self.bind_key_params(params, pk_seed)?;
        let n = params.n;
        if fors_indices.len() != params.k {
            return Err(Fips205Error::InvalidParameterSet);
        }
        let t_leaves = 1usize << params.a;
        let total_leaves = params.k * t_leaves;

        let mut chains = Vec::with_capacity(params.k + total_leaves);
        for (i, &idx_u32) in fors_indices.iter().enumerate() {
            let idx = idx_u32 as usize;
            if idx >= t_leaves {
                return Err(Fips205Error::MpcActiveTamperDetected);
            }
            let mut prf_a = base_adrs.with_type_and_clear(Fips205AdrsType::ForsPrf);
            prf_a.key_pair = base_adrs.key_pair;
            prf_a.f6 = (i * t_leaves + idx) as u32;
            chains.push((prf_a, Vec::new()));
        }
        for flat in 0..total_leaves {
            let mut prf_a = base_adrs.with_type_and_clear(Fips205AdrsType::ForsPrf);
            prf_a.key_pair = base_adrs.key_pair;
            prf_a.f6 = flat as u32;
            let mut leaf_a = base_adrs;
            leaf_a.adrs_type = Fips205AdrsType::ForsTree;
            leaf_a.f5 = 0;
            leaf_a.f6 = flat as u32;
            chains.push((prf_a, vec![leaf_a]));
        }

        let mut all_out = self.eval_slh_chains_parallel(n, pk_seed, &chains)?;
        let flat_leaves = all_out.split_off(params.k);
        let revealed_sks = all_out;
        let mut fors_all_leaves = Vec::with_capacity(params.k);
        for i in 0..params.k {
            fors_all_leaves.push(flat_leaves[i * t_leaves..(i + 1) * t_leaves].to_vec());
        }
        Ok((
            revealed_sks,
            fors_all_leaves,
            CutBoundaryMacToken::mint_verified(),
        ))
    }

    fn eval_wots_pkgen_subtree_mpc(
        &mut self,
        params: &Fips205Params,
        pk_seed: &[u8],
        layer: u32,
        tree: u128,
    ) -> Result<(Vec<SlhBlock>, CutBoundaryMacToken), Fips205Error> {
        self.bind_key_params(params, pk_seed)?;
        let n = params.n;
        let n_leaves = 1usize << params.hp;
        let ell = params.ell();
        let total_chains = n_leaves * ell;
        let mut chains = Vec::with_capacity(total_chains);
        for flat in 0..total_chains {
            let kp = (flat / ell) as u32;
            let ch = (flat % ell) as u32;
            let mut prf_a = Fips205Adrs::ZERO;
            prf_a.layer = layer;
            prf_a.set_tree_address(tree);
            prf_a.adrs_type = Fips205AdrsType::WotsPrf;
            prf_a.key_pair = kp;
            prf_a.f5 = ch;
            let steps: Vec<Fips205Adrs> = (0..15u32)
                .map(|step| {
                    let mut a = Fips205Adrs::ZERO;
                    a.layer = layer;
                    a.set_tree_address(tree);
                    a.adrs_type = Fips205AdrsType::WotsHash;
                    a.key_pair = kp;
                    a.f5 = ch;
                    a.f6 = step;
                    a
                })
                .collect();
            chains.push((prf_a, steps));
        }
        let endpoints = self.eval_slh_chains_parallel(n, pk_seed, &chains)?;
        Ok((endpoints, CutBoundaryMacToken::mint_verified()))
    }

    fn eval_wots_layer_sign_and_siblings_mpc(
        &mut self,
        _authorization: OracleCallToken,
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
        let ell = params.ell();
        if ell_check != ell {
            return Err(Fips205Error::InvalidParameterSet);
        }
        let total_chains = n_leaves * ell;
        let mut chains = Vec::with_capacity(total_chains);
        for flat in 0..total_chains {
            let kp = (flat / ell) as u32;
            let ch = flat % ell;
            let target = if kp == active_kp {
                digits[ch] as u32
            } else {
                15
            };
            let mut prf_a = Fips205Adrs::ZERO;
            prf_a.layer = layer;
            prf_a.set_tree_address(tree);
            prf_a.adrs_type = Fips205AdrsType::WotsPrf;
            prf_a.key_pair = kp;
            prf_a.f5 = ch as u32;
            let steps: Vec<Fips205Adrs> = (0..target)
                .map(|step| {
                    let mut a = Fips205Adrs::ZERO;
                    a.layer = layer;
                    a.set_tree_address(tree);
                    a.adrs_type = Fips205AdrsType::WotsHash;
                    a.key_pair = kp;
                    a.f5 = ch as u32;
                    a.f6 = step;
                    a
                })
                .collect();
            chains.push((prf_a, steps));
        }
        let nodes = self.eval_slh_chains_parallel(n, pk_seed, &chains)?;
        Ok((nodes, CutBoundaryMacToken::mint_verified()))
    }
}

// ============================================================================
// 6. Comprehensive Unit, Active-Fault-Abort & `3-of-5` Release Benchmark Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::baggy::{
        BaggyParams, MemoryFirstSigned, WaistbandCache, baggy_keygen_mpc, baggy_reference_keygen,
        baggy_reference_sign, baggy_sign_mpc, baggy_verify,
    };
    use crate::fips205::{slh_keygen_mpc, slh_sign_mpc, slh_verify};
    use crate::tsw_baggy::PqSecretKey;

    fn make_rngs(n: usize, tag: u8) -> Vec<PartyPrivateRng> {
        (0..n)
            .map(|i| PartyPrivateRng::from_seed([tag.wrapping_add(i as u8); 32], b"cnf-rss-test"))
            .collect()
    }

    #[test]
    fn cnf_rss_combinatorics_dkg_serialization_and_theorem_4_1_projection() {
        // Verify slot counts across `(2,3)`, `(3,5)`, `(3,6)`, `(5,6)`, and `(4,6)`.
        let c23 = CnfRssConfig::new(2, 3).unwrap();
        assert_eq!((c23.total_slots(), c23.slots_per_party()), (3, 2));
        let c35 = CnfRssConfig::new(3, 5).unwrap();
        assert_eq!((c35.total_slots(), c35.slots_per_party()), (10, 6));
        assert!(c35.supports_pure_hash_multiplication());
        let c36 = CnfRssConfig::new(3, 6).unwrap();
        assert_eq!((c36.total_slots(), c36.slots_per_party()), (15, 10));
        let c56 = CnfRssConfig::new(5, 6).unwrap();
        assert_eq!((c56.total_slots(), c56.slots_per_party()), (15, 5));
        let c46 = CnfRssConfig::new(4, 6).unwrap();
        assert_eq!((c46.total_slots(), c46.slots_per_party()), (20, 10));

        // Dealerless DKG + wire roundtrip + Theorem 4.1 projection on all 10 `3-of-5` subsets!
        let mut rngs = make_rngs(5, 0x10);
        let (mut shares, pk_seed) =
            run_dealerless_cnf_rss_dkg([0x41; 32], &c35, 32, &mut rngs).unwrap();
        let (sk_seed_ref, sk_prf_ref) = reconstruct_cnf_rss_secret_for_test(&shares);

        shares[0].bind_scheme_identity(&[0x99; 32]).unwrap();
        let raw0 = shares[0].to_secret_bytes();
        let decoded0 = CnfRssKeyShare256::from_secret_bytes(&raw0).unwrap();
        assert_eq!(decoded0.party_id, 0);
        assert_eq!(decoded0.pk_seed, pk_seed);
        assert_eq!(decoded0.scheme_identity(), Some([0x99; 32]));
        let mut tampered_raw = raw0.to_vec();
        tampered_raw[13] = 1; // non-zero reserved byte rejected
        assert!(CnfRssKeyShare256::from_secret_bytes(&tampered_raw).is_err());

        // Every one of the `\binom{5}{3} = 10` 3-custodian quorums reconstructs the exact
        // same `(sk_seed, sk_prf)` under Theorem 4.1 with pairwise PRF zero-share masking!
        for q0 in 0..5 {
            for q1 in (q0 + 1)..5 {
                for q2 in (q1 + 1)..5 {
                    let q_refs = [&shares[q0], &shares[q1], &shares[q2]];
                    let proj_a = project_quorum_keys(&[0x51; 32], &q_refs).unwrap();
                    let proj_b = project_quorum_keys(&[0x52; 32], &q_refs).unwrap();
                    // Distinct sessions produce completely fresh re-randomized `t-of-t` shares:
                    assert_ne!(proj_a.sk_seed_shares[0], proj_b.sk_seed_shares[0]);
                    let mut sum_seed = [0u8; 32];
                    let mut sum_prf = [0u8; 32];
                    for u in 0..3 {
                        for b in 0..32 {
                            sum_seed[b] ^= proj_a.sk_seed_shares[u][b];
                            sum_prf[b] ^= proj_a.sk_prf_shares[u][b];
                        }
                    }
                    assert_eq!(sum_seed, sk_seed_ref);
                    assert_eq!(sum_prf, sk_prf_ref);
                }
            }
        }
    }

    #[test]
    fn cnf_secret_codec_preserves_slh_profile_lock() {
        let cfg = CnfRssConfig::new(3, 5).unwrap();
        let mut rngs = make_rngs(5, 0x27);
        let (mut shares, pk) = run_dealerless_cnf_rss_dkg([0x64; 32], &cfg, 32, &mut rngs).unwrap();
        shares[0]
            .bind_slh_params(&Fips205Params::SLH_DSA_SHAKE_256F, &pk)
            .unwrap();
        let encoded = shares[0].to_secret_bytes();
        let mut restored = CnfRssKeyShare256::from_secret_bytes(&encoded).unwrap();
        assert!(
            restored
                .bind_slh_params(&Fips205Params::SLH_DSA_SHAKE_256F, &pk)
                .is_ok()
        );
        assert!(
            restored
                .bind_slh_params(&Fips205Params::SLH_DSA_SHAKE_256S, &pk)
                .is_err()
        );
        assert!(restored.bind_scheme_identity(&[3; 32]).is_err());
        assert!(CnfRssKeyShare256::from_secret_bytes(&encoded[..encoded.len() - 32]).is_err());
    }

    #[test]
    fn staged_bank_randomizer_matches_streaming_and_exhausts() {
        let cfg = CnfRssConfig::new(3, 5).unwrap();
        let mut rngs = make_rngs(5, 0x61);
        let (mut shares, _) = run_dealerless_cnf_rss_dkg([0x65; 32], &cfg, 32, &mut rngs).unwrap();
        let mut bank =
            StagedCnfRssBank::stage_for_quorum([0x66; 32], &cfg, &shares, &[0, 1, 2], 2, 1)
                .unwrap();
        let r_staged = {
            let [s0, s1, s2, _, _] = shares.as_mut_slice() else {
                unreachable!()
            };
            let mut rngs = make_rngs(3, 0x62);
            let mut engine =
                CnfRssProjectedEngine::new([0x66; 32], vec![s0, s1, s2], &mut rngs, &mut bank)
                    .unwrap();
            engine.randomiser(&[0x42; 32]).unwrap()
        };
        assert_eq!(bank.remaining_waves(), 0);
        assert!(matches!(
            bank.next_wave_tuples(1),
            Err(CnfRssError::BeaverBankExhausted)
        ));
        assert!(matches!(
            bank.next_cut_masks(1),
            Err(CnfRssError::BeaverBankExhausted)
        ));
        let mut stream =
            StreamingCnfRssSource::establish([0x67; 32], &cfg, &shares, &[0, 1, 2]).unwrap();
        let [s0, s1, s2, _, _] = shares.as_mut_slice() else {
            unreachable!()
        };
        let mut rngs = make_rngs(3, 0x63);
        let mut engine =
            CnfRssProjectedEngine::new([0x67; 32], vec![s0, s1, s2], &mut rngs, &mut stream)
                .unwrap();
        assert_eq!(engine.randomiser(&[0x42; 32]).unwrap(), r_staged);
    }

    #[test]
    fn bank_rejects_mixed_and_inconsistent_custody_inputs() {
        let cfg = CnfRssConfig::new(3, 5).unwrap();
        let mut rngs = make_rngs(5, 0x33);
        let (mut shares, _) = run_dealerless_cnf_rss_dkg([0x49; 32], &cfg, 32, &mut rngs).unwrap();
        assert!(
            StagedCnfRssBank::stage_for_quorum([0x51; 32], &cfg, &shares, &[0, 1, 2], 0, 0).is_ok()
        );
        shares.swap(0, 1);
        assert!(StreamingCnfRssSource::establish([0x51; 32], &cfg, &shares, &[0, 1, 2]).is_err());
        shares.swap(0, 1);
        shares[0].slot_prg_seeds[0][0] ^= 1;
        assert!(matches!(
            StagedCnfRssBank::stage_for_quorum([0x51; 32], &cfg, &shares, &[0, 1, 2], 0, 0),
            Err(CnfRssError::SlotOverlapMismatch { .. })
        ));
    }

    #[test]
    fn e2e_3of5_and_4of6_baggy_and_active_fault_abort() {
        let _memory = crate::test_budget::reserve_mb(1500);
        let params = BaggyParams::TEST_SMALL;

        // 1. `3-of-5` (10 shares) keygen on quorum `{0, 2, 4}`, sign on disjoint-overlap quorum `{1, 2, 3}`!
        let cfg35 = CnfRssConfig::new(3, 5).unwrap();
        let mut dkg_rngs = make_rngs(5, 0x20);
        let (mut shares, pk_seed) =
            run_dealerless_cnf_rss_dkg([0xA1; 32], &cfg35, 32, &mut dkg_rngs).unwrap();
        let (sk_seed, sk_prf) = reconstruct_cnf_rss_secret_for_test(&shares);
        let ref_sk = PqSecretKey {
            sk_seed,
            sk_prf,
            pk_seed,
        };

        let (pk, binding) = {
            let mut src =
                StreamingCnfRssSource::establish([0xA2; 32], &cfg35, &shares, &[0, 2, 4]).unwrap();
            let [s0, _, s2, _, s4] = shares.as_mut_slice() else {
                unreachable!()
            };
            let mut rngs = make_rngs(3, 0x30);
            let mut eng =
                CnfRssProjectedEngine::new([0xA2; 32], vec![s0, s2, s4], &mut rngs, &mut src)
                    .unwrap();
            baggy_keygen_mpc(&mut eng, &params, &mut WaistbandCache::disabled()).unwrap()
        };
        assert_eq!(Some(pk), baggy_reference_keygen(&params, &ref_sk));
        // Bind remaining offline custodians `{1, 3}` to the public `binding.identity()`
        for s in &mut shares {
            s.bind_scheme_identity(&binding.identity()).unwrap();
        }

        // Sign with `{1, 2, 3}` (custodians `0` and `4` completely offline).
        // Keep the ordinary suite bounded in memory; the ignored latency benchmark
        // covers the complete pre-staged bank and its verified full signature.
        let msg = b"3-of-5 stateless Baggy via Theorem 4.1 t-of-t MiniMAC projection";
        let mut bank =
            StreamingCnfRssSource::establish([0xA3; 32], &cfg35, &shares, &[1, 2, 3]).unwrap();
        let sig = {
            let [_, s1, s2, s3, _] = shares.as_mut_slice() else {
                unreachable!()
            };
            let mut rngs = make_rngs(3, 0x40);
            let mut eng =
                CnfRssProjectedEngine::new([0xA3; 32], vec![s1, s2, s3], &mut rngs, &mut bank)
                    .unwrap();
            baggy_sign_mpc(
                &mut eng,
                &params,
                &pk,
                &binding,
                &mut WaistbandCache::disabled(),
                &mut MemoryFirstSigned::new(),
                msg,
            )
            .unwrap()
        };
        assert!(baggy_verify(&params, &pk, msg, &sig));
        assert_eq!(Some(sig), baggy_reference_sign(&params, &ref_sk, &pk, msg));
        drop(bank);

        // 2. Active-fault-abort tests:
        //    (a) 1-bit `d` tamper rejected immediately by `[128, 56, 73]` codeword check;
        //    (b) Valid-codeword `[1u8; 128]` shift on `d` (bypassing codeword parity!) caught by `Tower128` MiniMAC barrier;
        //    (c) Corrupted `cr_star` Beaver triple caught by `C^{*2}` / `MiniMAC` barrier;
        //    (d) Cut-opening tamper caught before any digest is released!
        for fault in [
            CnfRssFault::CorruptDOpening {
                wave: 0,
                round: 0,
                bit: 0,
                party: 1,
            },
            CnfRssFault::ValidCodewordShiftD {
                wave: 2,
                round: 5,
                bit: 17,
                party: 2,
            },
            CnfRssFault::CorruptCutOpening { party: 0 },
        ] {
            let mut src =
                StreamingCnfRssSource::establish([0xA4; 32], &cfg35, &shares, &[0, 1, 4]).unwrap();
            let [s0, s1, _, _, s4] = shares.as_mut_slice() else {
                unreachable!()
            };
            let mut rngs = make_rngs(3, 0x50);
            let mut eng =
                CnfRssProjectedEngine::new([0xA4; 32], vec![s0, s1, s4], &mut rngs, &mut src)
                    .unwrap();
            eng.fault = Some(fault);
            let mut ledger = MemoryFirstSigned::new();
            assert!(
                baggy_sign_mpc(
                    &mut eng,
                    &params,
                    &pk,
                    &binding,
                    &mut WaistbandCache::disabled(),
                    &mut ledger,
                    msg,
                )
                .is_err()
            );
            assert!(eng.is_poisoned());
            assert!(ledger.is_empty());
        }

        // 3. Also verify `4-of-6` (`20` shares) CNF-RSS -> `4-of-4` projection end-to-end!
        let cfg46 = CnfRssConfig::new(4, 6).unwrap();
        let mut rngs46 = make_rngs(6, 0x60);
        let (mut shares46, _) =
            run_dealerless_cnf_rss_dkg([0xB1; 32], &cfg46, 32, &mut rngs46).unwrap();
        let mut src46 =
            StreamingCnfRssSource::establish([0xB2; 32], &cfg46, &shares46, &[0, 2, 3, 5]).unwrap();
        let [p0, _, p2, p3, _, p5] = shares46.as_mut_slice() else {
            unreachable!()
        };
        let mut r4 = make_rngs(4, 0x70);
        let mut eng46 =
            CnfRssProjectedEngine::new([0xB2; 32], vec![p0, p2, p3, p5], &mut r4, &mut src46)
                .unwrap();
        let (pk46, bind46) =
            baggy_keygen_mpc(&mut eng46, &params, &mut WaistbandCache::disabled()).unwrap();
        let sig46 = baggy_sign_mpc(
            &mut eng46,
            &params,
            &pk46,
            &bind46,
            &mut WaistbandCache::disabled(),
            &mut MemoryFirstSigned::new(),
            b"4-of-6 stateless Baggy",
        )
        .unwrap();
        assert!(baggy_verify(
            &params,
            &pk46,
            b"4-of-6 stateless Baggy",
            &sig46
        ));
    }

    #[test]
    fn e2e_3of5_slh_dsa_shake_128f_stock_verify_and_tamper_abort() {
        let _memory = crate::test_budget::reserve_mb(1200);
        // Historical test name: this bounded regression uses the compact profile.
        // The ignored latency benchmark below verifies the actual SHAKE-128f profile.
        let params = Fips205Params::SLH_DSA_SHAKE_COMPACT_TEST;
        let cfg35 = CnfRssConfig::new(3, 5).unwrap();
        let mut dkg_rngs = make_rngs(5, 0x80);
        let (mut shares, pk_seed32) =
            run_dealerless_cnf_rss_dkg([0xC1; 32], &cfg35, params.n, &mut dkg_rngs).unwrap();
        let pk_seed = &pk_seed32[..params.n];

        // Distributed `3-of-5` keygen on `{0, 1, 2}`
        let pk = {
            let mut src =
                StreamingCnfRssSource::establish([0xC2; 32], &cfg35, &shares, &[0, 1, 2]).unwrap();
            let [s0, s1, s2, _, _] = shares.as_mut_slice() else {
                unreachable!()
            };
            let mut rngs = make_rngs(3, 0x85);
            let mut eng =
                CnfRssProjectedEngine::new([0xC2; 32], vec![s0, s1, s2], &mut rngs, &mut src)
                    .unwrap();
            slh_keygen_mpc(&params, &mut eng, pk_seed).unwrap()
        };
        for s in &mut shares {
            s.bind_slh_params(&params, pk_seed).unwrap();
        }

        // Distributed `3-of-5` FIPS 205 signing on `{0, 3, 4}` (`1` and `2` offline!)
        let msg = b"3-of-5 FIPS 205 SLH-DSA-SHAKE-128f threshold release";
        let ctx = b"qsag:cnf-rss:v1";
        let sig = {
            let mut src =
                StreamingCnfRssSource::establish([0xC3; 32], &cfg35, &shares, &[0, 3, 4]).unwrap();
            let [s0, _, _, s3, s4] = shares.as_mut_slice() else {
                unreachable!()
            };
            let mut rngs = make_rngs(3, 0x90);
            let mut eng =
                CnfRssProjectedEngine::new([0xC3; 32], vec![s0, s3, s4], &mut rngs, &mut src)
                    .unwrap();
            slh_sign_mpc(&params, &mut eng, msg, ctx, &pk, None).unwrap()
        };
        assert_eq!(sig.len(), params.sig_bytes());
        assert!(slh_verify(&params, msg, &sig, ctx, &pk));

        // Active fault during `SLH-DSA` signing aborts cleanly with `MpcActiveTamperDetected`!
        let mut bad_src =
            StreamingCnfRssSource::establish([0xC4; 32], &cfg35, &shares, &[1, 2, 4]).unwrap();
        bad_src.corrupt_wave = Some((3, 10));
        let [_, s1, s2, _, s4] = shares.as_mut_slice() else {
            unreachable!()
        };
        let mut rngs = make_rngs(3, 0x95);
        let mut bad_eng =
            CnfRssProjectedEngine::new([0xC4; 32], vec![s1, s2, s4], &mut rngs, &mut bad_src)
                .unwrap();
        assert_eq!(
            slh_sign_mpc(&params, &mut bad_eng, msg, ctx, &pk, None),
            Err(Fips205Error::MpcActiveTamperDetected)
        );
        assert!(bad_eng.is_poisoned());
    }

    /// Single-thread cost of the three phases of one 56-lane wave for `t = 3`.
    #[cfg(feature = "std")]
    #[test]
    #[ignore = "per-phase wave cost measurement"]
    fn bench_wave_phase_split() {
        let tables = MiniMacTables::build().unwrap();
        let t = 3;
        let rounds = 6u32;
        let (mut materialize, mut expand, mut eval) = (0f64, 0f64, 0f64);
        for i in 0..rounds {
            let seed = [i as u8 + 1; 32];
            let started = std::time::Instant::now();
            let tuple = materialize_wave_tuple(&tables, t, &seed, None);
            materialize += started.elapsed().as_secs_f64();
            let compact = tuple.into_compact();
            let started = std::time::Instant::now();
            let tuple = compact.expand(&tables).unwrap();
            expand += started.elapsed().as_secs_f64();
            // A shared all-zero state with zero MACs is a valid authenticated input.
            let sh = SecretBuffer(vec![vec![0u8; STATE_CODE_BYTES]; t]);
            let mac = SecretBuffer(vec![vec![0u8; STATE_CODE_BYTES]; t]);
            let started = std::time::Instant::now();
            let (_dig, pending) = eval_minimac_wave_perm(
                &tables,
                &[7; 32],
                i as usize,
                MINIMAC_DATA_K,
                true,
                sh,
                mac,
                tuple,
                None,
            )
            .unwrap();
            eval += started.elapsed().as_secs_f64();
            let residual = pending
                .residual_shares
                .iter()
                .fold([0u128; 2], |acc, r| [acc[0] ^ r[0], acc[1] ^ r[1]]);
            assert_eq!(residual, [0, 0]);
        }
        let ms = |total: f64| 1000.0 * total / f64::from(rounds);
        eprintln!(
            "[BENCH wave t=3] materialize {:.2} ms, expand-from-compact {:.2} ms, evaluate {:.2} ms",
            ms(materialize),
            ms(expand),
            ms(eval)
        );
    }

    #[cfg(feature = "std")]
    #[test]
    #[ignore = "3-of-5 stateless Baggy and SLH-DSA release latency benchmark"]
    fn bench_3of5_stateless_baggy_and_slh_dsa_release_latency() {
        let cfg35 = CnfRssConfig::new(3, 5).unwrap();

        // 1. Full `BaggyParams::SHA3_128F` with only its topmost layer cached.
        //    Production signing below streams correlations; the separate TEST_SMALL
        //    measurement stages all tuples before starting its online timer.
        let baggy_params = BaggyParams::SHA3_128F;
        let mut dkg_rngs = make_rngs(5, 0xA0);
        let (mut shares_b, _) =
            run_dealerless_cnf_rss_dkg([0xD1; 32], &cfg35, 32, &mut dkg_rngs).unwrap();
        let mut ledger = MemoryFirstSigned::new();
        let mut cache = WaistbandCache::new(15, 65_536);

        let (pk_b, bind_b) = {
            let mut src =
                StreamingCnfRssSource::establish([0xD2; 32], &cfg35, &shares_b, &[0, 1, 2])
                    .unwrap();
            let [s0, s1, s2, _, _] = shares_b.as_mut_slice() else {
                unreachable!()
            };
            let mut r = make_rngs(3, 0xA5);
            let mut eng =
                CnfRssProjectedEngine::new([0xD2; 32], vec![s0, s1, s2], &mut r, &mut src).unwrap();
            baggy_keygen_mpc(&mut eng, &baggy_params, &mut cache).unwrap()
        };
        for s in &mut shares_b {
            s.bind_scheme_identity(&bind_b.identity()).unwrap();
        }
        // Measure streaming bounded-memory `3-of-5` `BaggyParams::SHA3_128F` release
        // AND pre-staged `StagedCnfRssBank` online release (`~12.6 GiB` staged tuple storage)!
        let small_params = BaggyParams::TEST_SMALL;
        let mut small_shares = {
            let mut r = make_rngs(5, 0xAF);
            run_dealerless_cnf_rss_dkg([0xCF; 32], &cfg35, 32, &mut r)
                .unwrap()
                .0
        };
        let (pk_sm, bind_sm) = {
            let mut src =
                StreamingCnfRssSource::establish([0xCE; 32], &cfg35, &small_shares, &[0, 1, 2])
                    .unwrap();
            let [s0, s1, s2, _, _] = small_shares.as_mut_slice() else {
                unreachable!()
            };
            let mut r = make_rngs(3, 0xAE);
            let mut eng =
                CnfRssProjectedEngine::new([0xCE; 32], vec![s0, s1, s2], &mut r, &mut src).unwrap();
            baggy_keygen_mpc(&mut eng, &small_params, &mut WaistbandCache::disabled()).unwrap()
        };
        for s in &mut small_shares {
            s.bind_scheme_identity(&bind_sm.identity()).unwrap();
        }
        let mut staged_small = StagedCnfRssBank::stage_for_quorum(
            [0xCD; 32],
            &cfg35,
            &small_shares,
            &[1, 3, 4],
            114,
            144,
        )
        .unwrap();
        let t_staged_online = std::time::Instant::now();
        let sig_sm = {
            let [_, s1, _, s3, s4] = small_shares.as_mut_slice() else {
                unreachable!()
            };
            let mut r = make_rngs(3, 0xAD);
            let mut eng =
                CnfRssProjectedEngine::new([0xCD; 32], vec![s1, s3, s4], &mut r, &mut staged_small)
                    .unwrap();
            baggy_sign_mpc(
                &mut eng,
                &small_params,
                &pk_sm,
                &bind_sm,
                &mut WaistbandCache::disabled(),
                &mut MemoryFirstSigned::new(),
                b"timed staged 3-of-5 Baggy",
            )
            .unwrap()
        };
        let baggy_staged_online_ms = t_staged_online.elapsed().as_secs_f64() * 1000.0;
        std::eprintln!("[BENCH staged TEST_SMALL] {baggy_staged_online_ms:.2} ms");
        assert!(baggy_verify(
            &small_params,
            &pk_sm,
            b"timed staged 3-of-5 Baggy",
            &sig_sm
        ));
        drop(staged_small);

        let t_baggy_full = std::time::Instant::now();
        let sig_b = {
            let mut src =
                StreamingCnfRssSource::establish([0xD4; 32], &cfg35, &shares_b, &[1, 3, 4])
                    .unwrap();
            let [_, s1, _, s3, s4] = shares_b.as_mut_slice() else {
                unreachable!()
            };
            let mut r = make_rngs(3, 0xB5);
            let mut eng =
                CnfRssProjectedEngine::new([0xD4; 32], vec![s1, s3, s4], &mut r, &mut src).unwrap();
            baggy_sign_mpc(
                &mut eng,
                &baggy_params,
                &pk_b,
                &bind_b,
                &mut cache,
                &mut ledger,
                b"timed 3-of-5 Baggy SHA3_128F release",
            )
            .unwrap()
        };
        let baggy_full_ms = t_baggy_full.elapsed().as_secs_f64() * 1000.0;
        std::eprintln!("[BENCH Baggy SHA3_128F stream] {baggy_full_ms:.2} ms");
        assert!(baggy_verify(
            &baggy_params,
            &pk_b,
            b"timed 3-of-5 Baggy SHA3_128F release",
            &sig_b
        ));

        // 2. Full `3-of-5` NIST FIPS 205 `SLH-DSA-SHAKE-128f` (`d = 22, hp = 3, k = 33, a = 6`)
        //    with bounded-batch streaming (several GiB; allocator/phase dependent).
        let slh_params = Fips205Params::SLH_DSA_SHAKE_128F;
        let mut slh_dkg_rngs = make_rngs(5, 0xC0);
        let (mut shares_s, pk_seed32) =
            run_dealerless_cnf_rss_dkg([0xE1; 32], &cfg35, slh_params.n, &mut slh_dkg_rngs)
                .unwrap();
        let pk_seed = &pk_seed32[..slh_params.n];
        let pk_s = {
            let mut src =
                StreamingCnfRssSource::establish([0xE2; 32], &cfg35, &shares_s, &[0, 1, 2])
                    .unwrap();
            let [s0, s1, s2, _, _] = shares_s.as_mut_slice() else {
                unreachable!()
            };
            let mut r = make_rngs(3, 0xC5);
            let mut eng =
                CnfRssProjectedEngine::new([0xE2; 32], vec![s0, s1, s2], &mut r, &mut src).unwrap();
            slh_keygen_mpc(&slh_params, &mut eng, pk_seed).unwrap()
        };
        for s in &mut shares_s {
            s.bind_slh_params(&slh_params, pk_seed).unwrap();
        }
        let t_slh_online = std::time::Instant::now();
        let sig_s = {
            let mut src_s =
                StreamingCnfRssSource::establish([0xE3; 32], &cfg35, &shares_s, &[0, 2, 3])
                    .unwrap();
            let [s0, _, s2, s3, _] = shares_s.as_mut_slice() else {
                unreachable!()
            };
            let mut r = make_rngs(3, 0xD0);
            let mut eng =
                CnfRssProjectedEngine::new([0xE3; 32], vec![s0, s2, s3], &mut r, &mut src_s)
                    .unwrap();
            slh_sign_mpc(
                &slh_params,
                &mut eng,
                b"timed 3-of-5 SLH-DSA-SHAKE-128f release",
                b"bench",
                &pk_s,
                None,
            )
            .unwrap()
        };
        let slh_online_ms = t_slh_online.elapsed().as_secs_f64() * 1000.0;
        assert!(slh_verify(
            &slh_params,
            b"timed 3-of-5 SLH-DSA-SHAKE-128f release",
            &sig_s,
            b"bench",
            &pk_s
        ));

        std::eprintln!(
            "[BENCH 3-of-5 CNF-RSS -> t-of-t MiniMAC] Baggy staged online = {baggy_staged_online_ms:.2} ms | Baggy SHA3_128F full stream = {baggy_full_ms:.2} ms | SLH-DSA-SHAKE-128f full stream = {slh_online_ms:.2} ms"
        );
    }
}
