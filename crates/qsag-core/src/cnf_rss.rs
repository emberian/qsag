//! Generalized `(t, n)` CNF Replicated Secret Sharing (`CNF-RSS`) with Theorem 4.1
//! Deterministic + Authenticated `t-of-t` Online Projection onto a 56-Lane `GFNI`-Accelerated
//! `[128, 56, 73]` Systematic Reed–Solomon `MiniMAC` `Keccak-f[1600]` Engine (`< 2^{-128}` Active Security).
//!
//! ### Overview
//! 1. **Dealerless `(t, n)` CNF-RSS Custody (`2 <= t <= n <= 10`, $\binom{n}{t-1}$ Share Slots):**
//!    - Splits 256-bit `sk_seed` and `sk_prf` into $M = \binom{n}{t-1}$ replicated share slots
//!      (`3` for `2-of-3`, `10` for `3-of-5`, `15` for `3-of-6`/`5-of-6`, `20` for `4-of-6`,
//!      `35` for `4-of-7`), where custodian $i \in [n]$ holds slot $S_m \iff i \notin S_m$.
//!    - Any $t - 1$ colluding custodians $C$ miss slot $S^\star = C$, whose complement
//!      $H_{S^\star} = [n] \setminus C$ consists exclusively of honest custodians.
//! 2. **Theorem 4.1 Zero-Communication Authenticated `t-of-t` Online Projection:**
//!    - Any online $t$-custodian quorum $Q = \{q_0 < \dots < q_{t-1}\} \subset [n]$ partitions
//!      all $M = \binom{n}{t-1}$ slots via $\mathsf{owner}(Q, S) = \min(Q \setminus S) \in Q$
//!      (cross-checking all overlapping slots $|Q \setminus S| \ge 2$ via committed digests) and
//!      re-randomizes into fresh uniform `t-of-t` additive shares via pairwise `cSHAKE256` zero-masks.
//! 3. **56-Lane `AVX-512 GFNI` `[128, 56, 73]` `MiniMAC` `Keccak-f[1600]` Sweep (`BaggyEngine` + `SlhMpcOracles`):**
//!    - Packs `56` parallel Boolean `Keccak-f[1600]` lanes into `[u8; 128]` codewords of the
//!      systematic `[128, 56, 73]` Reed–Solomon code $C$ over [`TowerGf256`], whose Schur square
//!      $C^{\ast 2} = [128, 111, 18]$ has minimum distance $d_{\min}(C^{\ast 2}) = 18$ bytes
//!      ($2^{-144} < 2^{-128}$ unconditional active forgery soundness against up to $t - 1$
//!      malicious online signers).
//!    - Evaluates all `1,600` `Chi` gates of each round in a single contiguous `204,800`-byte
//!      [`qsag_asm::gf256_shamir_mul`] (`AVX-512 GFNI` / `AVX2` / portable constant-time) call,
//!      masks unselected cut-boundary lanes via $(\mathbf{M}_{\text{pub}} \ast \mathbf{dig}) \oplus \mathbf{r}^\ast \in C^{\ast 2}$
//!      (zero leakage of unrevealed WOTS/PORS/FORS nodes), and blinds/burns ephemeral per-window
//!      MAC keys $\boldsymbol{\Delta}^{(w)}$ at every barrier.

use alloc::boxed::Box;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;
use core::hint::black_box;

use crate::baggy::{
    BaggyEngine, BaggyError, TAG_BAGGY_OPT_RAND, TAG_BAGGY_R, keyed_mu_frame,
};
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
    cshake256_32_multi_frame,
};
use crate::tsw_baggy::{HashAdrs, TAG_PRF, TAG_TH_F};
use crate::wipe::{
    SecretBuffer, SecretVec, SecretWipe, ct_eq_bytes, ct_eq_bytes32, wipe_bytes, wipe_bytes32,
};
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
            CnfRssError::CommitmentMismatch { party, .. } => {
                Self::RssCommitMismatch { accused_party: party }
            }
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
            CnfRssError::ActiveTamperDetected { .. }
            | CnfRssError::SlotOverlapMismatch { .. } => {
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
                write!(f, "CNF-RSS replicated slot {slot_idx} mismatch across quorum")
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
    slh_params: Option<Fips205Params>,
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

    #[inline]
    pub fn scheme_identity(&self) -> Option<[u8; 32]> {
        self.scheme_identity
    }

    /// Bind this share once to a `BaggyKeyBinding::identity()` digest (idempotent on same digest).
    pub fn bind_scheme_identity(&mut self, identity: &[u8; 32]) -> Result<(), CnfRssError> {
        if self.slh_params.is_some() {
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
        match &self.slh_params {
            None => {
                self.slh_params = Some(*params);
                Ok(())
            }
            Some(bound) if bound == params => Ok(()),
            Some(_) => Err(Fips205Error::InvalidParameterSet),
        }
    }

    fn local_slot_pos(&self, global_slot_idx: usize) -> Option<usize> {
        self.slot_indices.binary_search(&global_slot_idx).ok()
    }

    /// Canonical secret byte serialization (`QSCNFK01` header).
    pub fn to_secret_bytes(&self) -> SecretVec<u8> {
        let k = self.slot_indices.len();
        let n = self.cfg.n;
        let cap = 16 + 32 + 32 + 2 * k + 96 * k + 32 * n;
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
        out.push(0u8);
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
        let reserved = bytes[13];
        let k = u16::from_le_bytes([bytes[14], bytes[15]]) as usize;
        if !matches!(key_len, 16 | 24 | 32) || has_id > 1 || reserved != 0 {
            return Err(CnfRssError::InvalidParameters);
        }
        let cfg = CnfRssConfig::new(t, n)?;
        let expected_slots = cfg.party_slot_indices(party_id)?;
        if k != expected_slots.len() {
            return Err(CnfRssError::InvalidParameters);
        }
        let expected_len = 80 + 2 * k + 96 * k + 32 * n;
        if bytes.len() != expected_len {
            return Err(CnfRssError::InvalidParameters);
        }
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
            for _ in 0..count {
                let mut arr = [0u8; 32];
                arr.copy_from_slice(&bytes[*pos..*pos + 32]);
                v.push(arr);
                *pos += 32;
            }
            v
        };
        let sk_seed_slots = read_vec32(&mut pos, k);
        let sk_prf_slots = read_vec32(&mut pos, k);
        let slot_prg_seeds = read_vec32(&mut pos, k);
        let pair_prf_keys = read_vec32(&mut pos, n);
        if pair_prf_keys[party_id] != [0u8; 32] {
            return Err(CnfRssError::InvalidParameters);
        }
        for s in sk_seed_slots.iter().chain(sk_prf_slots.iter()) {
            if s[key_len..].iter().any(|&b| b != 0) {
                return Err(CnfRssError::InvalidParameters);
            }
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
            slh_params: None,
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
    let pk_coin = run_commit_and_open_coin(
        &session_id,
        b"QSAG.CNF_RSS.DKG.PK_SEED/v1",
        &[cfg.t as u8, cfg.n as u8, key_len as u8],
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
    let mut pair_keys: Vec<SecretVec<[u8; 32]>> = (0..n)
        .map(|_| SecretBuffer(vec![[0u8; 32]; n]))
        .collect();
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
            |(((((party_id, slot_indices), sk_seed_slots), sk_prf_slots), slot_prg_seeds), pair_prf_keys)| {
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
                    slh_params: None,
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
    /// Fast 8-bit LUT for encoding `bits56` (`7` bytes -> `72` parity bytes).
    pub_byte_lut: [[[u8; MINIMAC_PARITY_C]; 256]; 7],
    /// Parity rows for `C^{*2}`: `gen_c2_parity[k]` (`k in 0..111`) holds `L^{(111)}_k(\alpha_{111..128})` (`17` bytes).
    gen_c2_parity: [[u8; MINIMAC_PARITY_C2]; MINIMAC_C2_K],
    /// Fast 8-bit LUT for `encode_c2_zero_mask` (`55` coordinates x `256` byte values -> `17` parity bytes).
    c2_zero_lut: Box<[[[u8; MINIMAC_PARITY_C2]; 256]; MINIMAC_ZERO_MASK_K]>,
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
            for i in 0..MINIMAC_DATA_K {
                let diff_inv = xj
                    .add(TowerGf256(i as u8))
                    .inv()
                    .ok_or(CnfRssError::InvalidParameters)?;
                gen_c_parity[i][p_off] = full_num.mul(diff_inv).mul(bary_c[i]).0;
            }
        }

        let mut pub_byte_lut = [[[0u8; MINIMAC_PARITY_C]; 256]; 7];
        for (byte_idx, lut_group) in pub_byte_lut.iter_mut().enumerate() {
            for (val, entry) in lut_group.iter_mut().enumerate() {
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
            for k in 0..MINIMAC_C2_K {
                let diff_inv = xr
                    .add(TowerGf256(k as u8))
                    .inv()
                    .ok_or(CnfRssError::InvalidParameters)?;
                gen_c2_parity[k][r_off] = full_num.mul(diff_inv).mul(bary_c2[k]).0;
            }
        }

        let mut c2_zero_lut = Box::new([[[0u8; MINIMAC_PARITY_C2]; 256]; MINIMAC_ZERO_MASK_K]);
        for idx in 0..MINIMAC_ZERO_MASK_K {
            let row = &gen_c2_parity[MINIMAC_DATA_K + idx];
            for val in 0..256usize {
                let u = TowerGf256(val as u8);
                for r_off in 0..MINIMAC_PARITY_C2 {
                    c2_zero_lut[idx][val][r_off] = u.mul(TowerGf256(row[r_off])).0;
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
        for i in 0..MINIMAC_DATA_K {
            out[i] = ((public_bits56 >> i) & 1) as u8;
        }
        let le = public_bits56.to_le_bytes();
        for byte_idx in 0..7 {
            let lut = &self.pub_byte_lut[byte_idx][le[byte_idx] as usize];
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
        for byte_idx in 0..7 {
            let lut = &self.pub_byte_lut[byte_idx][le[byte_idx] as usize];
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
            let lut = &self.c2_zero_lut[idx][uk as usize];
            for r_off in 0..MINIMAC_PARITY_C2 {
                p17[r_off] ^= lut[r_off];
            }
        }
        out[MINIMAC_C2_K..].copy_from_slice(&p17);
    }

    /// Check that a PUBLIC folded `[u8; 128]` vector lies in $C^{\ast 2} = [128, 111, 18]$.
    fn verify_public_c2(&self, cw: &[u8; MINIMAC_CODE_N]) -> bool {
        let mut exp = [0u8; MINIMAC_PARITY_C2];
        for k in 0..MINIMAC_C2_K {
            let wk = TowerGf256(cw[k]);
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
    delta_shares: SecretVec<[u8; MINIMAC_CODE_N]>,
    r_star: SecretVec<Vec<u8>>,
    r_star_mac: SecretVec<Vec<u8>>,
}

/// Source of single-use `t-of-t` projected `[128, 56, 73]` `MiniMAC` tuples.
