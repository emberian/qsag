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
pub trait CnfRssTupleSource {
    /// Next `count` single-use 56-lane permutation tuples for `t` online signers.
    fn next_wave_tuples(&mut self, count: usize) -> Result<Vec<ProjectedWaveTuple>, CnfRssError>;

    /// Next `groups` single-use 256-bit cut-opening mask tuples (`r^* in C^{*2}` vanishing on `0..56`).
    fn next_cut_masks(&mut self, groups: usize) -> Result<Vec<ProjectedCutMaskTuple>, CnfRssError>;
}

/// Derive a single-use `ProjectedWaveTuple` from a domain-bound seed using pure `SHAKE256`
/// CNF-RSS slot cross-products + `gf256_shamir_mul` (`AVX-512 GFNI` accelerated).
fn materialize_wave_tuple(
    tables: &MiniMacTables,
    t: usize,
    wave_seed: &[u8; 32],
    corrupt_gate: Option<usize>,
) -> ProjectedWaveTuple {
    let total_bytes = 24 * STATE_CODE_BYTES;
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
        delta_sum[j] = delta_sum[j] ^ delta_shares[t - 1][j];
    }

    let mut a_sum = SecretBuffer(vec![0u8; total_bytes]);
    let mut b_sum = SecretBuffer(vec![0u8; total_bytes]);
    let mut r_sum = SecretBuffer(vec![0u8; total_bytes]);
    let mut z_zero = SecretBuffer(vec![0u8; total_bytes]);

    let mut rand_buf = SecretBuffer(vec![0u8; GATES_PER_WAVE_PERM * (24 + MINIMAC_ZERO_MASK_K)]);
    xof.squeeze(&mut rand_buf);
    let mask56 = (1u64 << MINIMAC_DATA_K) - 1;

    for g in 0..GATES_PER_WAVE_PERM {
        let r_off = g * (24 + MINIMAC_ZERO_MASK_K);
        let a_bits = u64::from_le_bytes([
            rand_buf[r_off],
            rand_buf[r_off + 1],
            rand_buf[r_off + 2],
            rand_buf[r_off + 3],
            rand_buf[r_off + 4],
            rand_buf[r_off + 5],
            rand_buf[r_off + 6],
            0,
        ]) & mask56;
        let b_bits = u64::from_le_bytes([
            rand_buf[r_off + 7],
            rand_buf[r_off + 8],
            rand_buf[r_off + 9],
            rand_buf[r_off + 10],
            rand_buf[r_off + 11],
            rand_buf[r_off + 12],
            rand_buf[r_off + 13],
            0,
        ]) & mask56;
        let r_bits = u64::from_le_bytes([
            rand_buf[r_off + 14],
            rand_buf[r_off + 15],
            rand_buf[r_off + 16],
            rand_buf[r_off + 17],
            rand_buf[r_off + 18],
            rand_buf[r_off + 19],
            rand_buf[r_off + 20],
            0,
        ]) & mask56;
        let mut cw = [0u8; MINIMAC_CODE_N];
        let g_byte = g * MINIMAC_CODE_N;
        // `a_bits`, `b_bits`, `r_bits` inside tuple generation are fresh uniform masks; encode cleanly:
        tables.encode_secret_bits56(a_bits, &mut cw);
        a_sum[g_byte..g_byte + MINIMAC_CODE_N].copy_from_slice(&cw);
        tables.encode_secret_bits56(b_bits, &mut cw);
        b_sum[g_byte..g_byte + MINIMAC_CODE_N].copy_from_slice(&cw);
        tables.encode_secret_bits56(r_bits, &mut cw);
        r_sum[g_byte..g_byte + MINIMAC_CODE_N].copy_from_slice(&cw);
        let mut r55 = [0u8; MINIMAC_ZERO_MASK_K];
        r55.copy_from_slice(&rand_buf[r_off + 24..r_off + 24 + MINIMAC_ZERO_MASK_K]);
        tables.encode_secret_c2_zero_mask(&r55, &mut cw);
        wipe_bytes(&mut r55);
        z_zero[g_byte..g_byte + MINIMAC_CODE_N].copy_from_slice(&cw);
        wipe_bytes(&mut cw);
    }

    // `cr_star_sum = (a_sum * b_sum) ^ r_sum ^ z_zero` in `C^{*2}` via AVX-512 GFNI!
    let mut cr_star_sum = SecretBuffer(vec![0u8; total_bytes]);
    qsag_asm::gf256_shamir_mul(&mut cr_star_sum, &a_sum, &b_sum);
    for (dst, (&rv, &zv)) in cr_star_sum.iter_mut().zip(r_sum.iter().zip(z_zero.iter())) {
        *dst ^= rv ^ zv;
    }
    if let Some(bad_g) = corrupt_gate
        && bad_g < GATES_PER_WAVE_PERM
    {
        cr_star_sum[bad_g * MINIMAC_CODE_N] ^= 1;
    }

    // Repeat `delta_sum` across a `1600 * 128` round tile to batch `gf256_shamir_mul` at 200+ GB/s!
    let mut delta_tile = SecretBuffer(vec![0u8; STATE_CODE_BYTES]);
    for chunk in delta_tile.chunks_exact_mut(MINIMAC_CODE_N) {
        chunk.copy_from_slice(&*delta_sum);
    }
    let mul_by_delta = |src: &[u8]| -> SecretBuffer<Vec<u8>> {
        let mut mac = SecretBuffer(vec![0u8; total_bytes]);
        for rnd in 0..24 {
            let off = rnd * STATE_CODE_BYTES;
            qsag_asm::gf256_shamir_mul(
                &mut mac[off..off + STATE_CODE_BYTES],
                &src[off..off + STATE_CODE_BYTES],
                &delta_tile,
            );
        }
        mac
    };
    let a_mac_sum = mul_by_delta(&a_sum);
    let b_mac_sum = mul_by_delta(&b_sum);
    let r_mac_sum = mul_by_delta(&r_sum);
    let cr_mac_sum = mul_by_delta(&cr_star_sum);

    let split_additive = |sum: &[u8], xof: &mut Cshake256Xof| -> SecretVec<Vec<u8>> {
        let mut shares = SecretBuffer(Vec::with_capacity(t));
        let mut rem = sum.to_vec();
        for _ in 0..(t - 1) {
            let mut sh = vec![0u8; total_bytes];
            xof.squeeze(&mut sh);
            for (r_byte, &s_byte) in rem.iter_mut().zip(sh.iter()) {
                *r_byte ^= s_byte;
            }
            shares.push(sh);
        }
        shares.push(rem);
        shares
    };

    let a = split_additive(&a_sum, &mut xof);
    let a_mac = split_additive(&a_mac_sum, &mut xof);
    let b = split_additive(&b_sum, &mut xof);
    let b_mac = split_additive(&b_mac_sum, &mut xof);
    let r = split_additive(&r_sum, &mut xof);
    let r_mac = split_additive(&r_mac_sum, &mut xof);
    let cr_star = split_additive(&cr_star_sum, &mut xof);
    let cr_star_mac = split_additive(&cr_mac_sum, &mut xof);

    ProjectedWaveTuple {
        delta_shares,
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

fn materialize_cut_mask_tuple(
    tables: &MiniMacTables,
    t: usize,
    cut_seed: &[u8; 32],
) -> ProjectedCutMaskTuple {
    let total_bytes = DIGEST_BITS * MINIMAC_CODE_N;
    let mut xof = Cshake256Xof::new(b"QSAG.CNF_RSS.MINIMAC.CUT/v1");
    xof.absorb(cut_seed);

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
        let cur = delta_sum[j] ^ delta_shares[t - 1][j];
        if cur == 0 {
            delta_shares[t - 1][j] ^= 1;
        }
        delta_sum[j] = delta_sum[j] ^ delta_shares[t - 1][j];
    }

    let mut r_star_sum = SecretBuffer(vec![0u8; total_bytes]);
    let mut delta_tile = SecretBuffer(vec![0u8; total_bytes]);
    let mut r55 = SecretBuffer([0u8; MINIMAC_ZERO_MASK_K]);
    let mut cw = SecretBuffer([0u8; MINIMAC_CODE_N]);
    for bit in 0..DIGEST_BITS {
        xof.squeeze(&mut *r55);
        tables.encode_secret_c2_zero_mask(&r55, &mut cw);
        let off = bit * MINIMAC_CODE_N;
        r_star_sum[off..off + MINIMAC_CODE_N].copy_from_slice(&*cw);
        delta_tile[off..off + MINIMAC_CODE_N].copy_from_slice(&*delta_sum);
    }
    let mut r_star_mac_sum = SecretBuffer(vec![0u8; total_bytes]);
    qsag_asm::gf256_shamir_mul(&mut r_star_mac_sum, &r_star_sum, &delta_tile);

    let split_additive = |sum: &[u8], xof: &mut Cshake256Xof| -> SecretVec<Vec<u8>> {
        let mut shares = SecretBuffer(Vec::with_capacity(t));
        let mut rem = sum.to_vec();
        for _ in 0..(t - 1) {
            let mut sh = vec![0u8; total_bytes];
            xof.squeeze(&mut sh);
            for (r_byte, &s_byte) in rem.iter_mut().zip(sh.iter()) {
                *r_byte ^= s_byte;
            }
            shares.push(sh);
        }
        shares.push(rem);
        shares
    };
    let r_star = split_additive(&r_star_sum, &mut xof);
    let r_star_mac = split_additive(&r_star_mac_sum, &mut xof);

    ProjectedCutMaskTuple {
        delta_shares,
        r_star,
        r_star_mac,
    }
}

/// Pre-staged single-use `(t, n)` CNF-RSS bank projected onto an online $t$-signer quorum.
pub struct StagedCnfRssBank {
    waves: Vec<ProjectedWaveTuple>,
    cuts: Vec<ProjectedCutMaskTuple>,
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
        cfg.validate_quorum(quorum)?;
        if all_shares.len() != cfg.n {
            return Err(CnfRssError::InvalidParameters);
        }
        // Fold all `M = \binom{n}{t-1}` slot PRG seeds into a committee correlation root;
        // every slot is held by `n - t + 1 >= 1` custodians, and `S* = C` is held exclusively
        // by honest custodians `[n] \ C`.
        let mut root_xof = Cshake256Xof::new(b"QSAG.CNF_RSS.BANK.ROOT/v1");
        root_xof.absorb(&session_id);
        for slot_idx in 0..cfg.total_slots() {
            let holder = all_shares
                .iter()
                .find_map(|s| s.local_slot_pos(slot_idx).map(|pos| s.slot_prg_seeds[pos]))
                .ok_or(CnfRssError::InvalidParameters)?;
            root_xof.absorb(&holder);
        }
        for &q in quorum {
            root_xof.absorb(&(q as u64).to_be_bytes());
        }
        let mut master = SecretBuffer([0u8; 32]);
        root_xof.squeeze(&mut *master);

        let tables = MiniMacTables::build()?;
        let wave_seeds: Vec<[u8; 32]> = (0..num_waves)
            .map(|w| {
                cshake256_32_multi_frame(
                    b"QSAG.CNF_RSS.BANK.WAVE_SEED/v1",
                    &[&*master, &(w as u64).to_le_bytes()],
                )
            })
            .collect();
        #[cfg(feature = "std")]
        let waves: Vec<ProjectedWaveTuple> = {
            let workers = std::thread::available_parallelism()
                .map_or(1, usize::from)
                .min(12);
            let chunk_sz = wave_seeds.len().div_ceil(workers).max(1);
            let mut slots: Vec<Option<ProjectedWaveTuple>> =
                (0..wave_seeds.len()).map(|_| None).collect();
            std::thread::scope(|scope| {
                let mut handles = Vec::new();
                for (c_idx, out_slice) in slots.chunks_mut(chunk_sz).enumerate() {
                    let seeds = &wave_seeds[c_idx * chunk_sz
                        ..((c_idx + 1) * chunk_sz).min(wave_seeds.len())];
                    let tables_ref = &*tables;
                    let t = cfg.t;
                    handles.push(scope.spawn(move || {
                        for (dst, seed) in out_slice.iter_mut().zip(seeds.iter()) {
                            *dst = Some(materialize_wave_tuple(tables_ref, t, seed, None));
                        }
                    }));
                }
                for h in handles {
                    let _ = h.join();
                }
            });
            slots.into_iter().flatten().collect()
        };
        #[cfg(not(feature = "std"))]
        let waves: Vec<ProjectedWaveTuple> = wave_seeds
            .iter()
            .map(|seed| materialize_wave_tuple(&tables, cfg.t, seed, None))
            .collect();

        let cuts: Vec<ProjectedCutMaskTuple> = (0..num_cuts)
            .map(|c| {
                let c_seed = cshake256_32_multi_frame(
                    b"QSAG.CNF_RSS.BANK.CUT_SEED/v1",
                    &[&*master, &(c as u64).to_le_bytes()],
                );
                materialize_cut_mask_tuple(&tables, cfg.t, &c_seed)
            })
            .collect();

        Ok(Self { waves, cuts })
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
        Ok(self.waves.split_off(split_at))
    }

    fn next_cut_masks(&mut self, groups: usize) -> Result<Vec<ProjectedCutMaskTuple>, CnfRssError> {
        if self.cuts.len() < groups {
            return Err(CnfRssError::BeaverBankExhausted);
        }
        let split_at = self.cuts.len() - groups;
        Ok(self.cuts.split_off(split_at))
    }
}

/// Bounded-memory (`< 24 MB` L3-resident) streaming `(t, n)` CNF-RSS tuple source materializing
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
        cfg.validate_quorum(quorum)?;
        if all_shares.len() != cfg.n {
            return Err(CnfRssError::InvalidParameters);
        }
        let mut root_xof = Cshake256Xof::new(b"QSAG.CNF_RSS.STREAM.ROOT/v1");
        root_xof.absorb(&session_id);
        for slot_idx in 0..cfg.total_slots() {
            let holder = all_shares
                .iter()
                .find_map(|s| s.local_slot_pos(slot_idx).map(|pos| s.slot_prg_seeds[pos]))
                .ok_or(CnfRssError::InvalidParameters)?;
            root_xof.absorb(&holder);
        }
        for &q in quorum {
            root_xof.absorb(&(q as u64).to_be_bytes());
        }
        let mut master_seed = SecretBuffer([0u8; 32]);
        root_xof.squeeze(&mut *master_seed);
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

impl CnfRssTupleSource for StreamingCnfRssSource {
    fn next_wave_tuples(&mut self, count: usize) -> Result<Vec<ProjectedWaveTuple>, CnfRssError> {
        let base = self.wave_ctr;
        self.wave_ctr = self
            .wave_ctr
            .checked_add(count as u64)
            .ok_or(CnfRssError::InvalidParameters)?;
        let seeds: Vec<(u64, [u8; 32])> = (0..count)
            .map(|i| {
                let idx = base + i as u64;
                let s = cshake256_32_multi_frame(
                    b"QSAG.CNF_RSS.STREAM.WAVE/v1",
                    &[&*self.master_seed, &idx.to_le_bytes()],
                );
                (idx, s)
            })
            .collect();
        #[cfg(test)]
        let corrupt = self.corrupt_wave;
        #[cfg(not(test))]
        let corrupt: Option<(u64, usize)> = None;

        #[cfg(feature = "std")]
        if count > 1 {
            let workers = std::thread::available_parallelism()
                .map_or(1, usize::from)
                .min(12);
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
                for h in handles {
                    let _ = h.join();
                }
            });
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

/// Deferred verification record for one evaluated 56-lane permutation (`4 KB` MAC fold + transcript).
struct PendingWaveVerification {
    wave_digest: [u8; 32],
    delta_shares: SecretVec<[u8; MINIMAC_CODE_N]>,
    /// Per-party folded `Tower128` MAC residual shares across all `128` codeword coordinates.
    residual_shares: SecretVec<[Tower128; MINIMAC_CODE_N]>,
}

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
fn keccak_linear_minimac(src: &[u8], dst: &mut [u8]) {
    let mut col = [0u8; 5 * 64 * MINIMAC_CODE_N];
    for x in 0..5 {
        for z in 0..64 {
            let c_off = (x * 64 + z) * MINIMAC_CODE_N;
            let c_slice = &mut col[c_off..c_off + MINIMAC_CODE_N];
            for y in 0..5 {
                let s_off = ((x + 5 * y) * 64 + z) * MINIMAC_CODE_N;
                let s_slice = &src[s_off..s_off + MINIMAC_CODE_N];
                for (d, &s) in c_slice.iter_mut().zip(s_slice.iter()) {
                    *d ^= s;
                }
            }
        }
    }
    let mut d_theta = [0u8; 5 * 64 * MINIMAC_CODE_N];
    for x in 0..5 {
        for z in 0..64 {
            let prev = (((x + 4) % 5) * 64 + z) * MINIMAC_CODE_N;
            let next = (((x + 1) % 5) * 64 + ((z + 63) & 63)) * MINIMAC_CODE_N;
            let out_off = (x * 64 + z) * MINIMAC_CODE_N;
            for j in 0..MINIMAC_CODE_N {
                d_theta[out_off + j] = col[prev + j] ^ col[next + j];
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
            let s_off = (source * 64 + src_z) * MINIMAC_CODE_N;
            let dt_off = (x * 64 + src_z) * MINIMAC_CODE_N;
            let d_off = (target * 64 + z) * MINIMAC_CODE_N;
            for j in 0..MINIMAC_CODE_N {
                dst[d_off + j] = src[s_off + j] ^ d_theta[dt_off + j];
            }
        }
    }
    wipe_bytes(&mut col);
    wipe_bytes(&mut d_theta);
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
    let mut delta_tiles: SecretVec<Vec<u8>> = SecretBuffer(
        (0..t)
            .map(|u| {
                let mut tile = vec![0u8; STATE_CODE_BYTES];
                for c in tile.chunks_exact_mut(MINIMAC_CODE_N) {
                    c.copy_from_slice(&tuple.delta_shares[u]);
                }
                tile
            })
            .collect(),
    );

    let mut tr_xof = Cshake256Xof::new(b"QSAG.CNF_RSS.WAVE.TRANSCRIPT/v1");
    tr_xof.absorb(session_id);
    tr_xof.absorb(&(wave_idx as u64).to_le_bytes());

    let mut residual_shares = SecretBuffer(vec![[Tower128::ZERO; MINIMAC_CODE_N]; t]);

    for (rnd, &rc) in KECCAK_ROUND_CONSTANTS.iter().enumerate() {
        let r_off = rnd * STATE_CODE_BYTES;
        for u in 0..t {
            keccak_linear_minimac(&state_sh[u], &mut lin_sh[u]);
            keccak_linear_minimac(&state_mac[u], &mut lin_mac[u]);
        }

        // Gather `~b[u_idx]` and `b[v_idx]` into contiguous `204,800`-byte slices for SIMD GFNI!
        for lane in 0..25 {
            let row = 5 * (lane / 5);
            let u_lane = row + (lane + 1) % 5;
            let v_lane = row + (lane + 2) % 5;
            for z in 0..64 {
                let dst = (lane * 64 + z) * MINIMAC_CODE_N;
                let u_src = (u_lane * 64 + z) * MINIMAC_CODE_N;
                let v_src = (v_lane * 64 + z) * MINIMAC_CODE_N;
                for p in 0..t {
                    not_u_sh[p][dst..dst + MINIMAC_CODE_N]
                        .copy_from_slice(&lin_sh[p][u_src..u_src + MINIMAC_CODE_N]);
                    if p == 0 {
                        for b in &mut not_u_sh[0][dst..dst + MINIMAC_CODE_N] {
                            *b ^= 1;
                        }
                    }
                    for j in 0..MINIMAC_CODE_N {
                        not_u_mac[p][dst + j] = lin_mac[p][u_src + j] ^ tuple.delta_shares[p][j];
                    }
                    v_sh[p][dst..dst + MINIMAC_CODE_N]
                        .copy_from_slice(&lin_sh[p][v_src..v_src + MINIMAC_CODE_N]);
                    v_mac[p][dst..dst + MINIMAC_CODE_N]
                        .copy_from_slice(&lin_mac[p][v_src..v_src + MINIMAC_CODE_N]);
                }
            }
        }

        // Open `d = not_u ^ a` and `e = v ^ b`
        d_open.fill(0);
        e_open.fill(0);
        for p in 0..t {
            let a_rnd = &tuple.a[p][r_off..r_off + STATE_CODE_BYTES];
            let b_rnd = &tuple.b[p][r_off..r_off + STATE_CODE_BYTES];
            for i in 0..STATE_CODE_BYTES {
                #[allow(unused_mut)]
                let mut d_p = not_u_sh[p][i] ^ a_rnd[i];
                #[cfg(test)]
                if let Some(f) = fault {
                    match f {
                        CnfRssFault::CorruptDOpening {
                            wave,
                            round,
                            bit,
                            party,
                        } if wave == wave_idx
                            && round == rnd
                            && party == p
                            && i == bit * MINIMAC_CODE_N =>
                        {
                            d_p ^= 1;
                        }
                        CnfRssFault::ValidCodewordShiftD {
                            wave,
                            round,
                            bit,
                            party,
                        } if wave == wave_idx
                            && round == rnd
                            && party == p
                            && (bit * MINIMAC_CODE_N..(bit + 1) * MINIMAC_CODE_N).contains(&i) =>
                        {
                            d_p ^= 1;
                        }
                        _ => {}
                    }
                }
                d_open[i] ^= d_p;
                e_open[i] ^= v_sh[p][i] ^ b_rnd[i];
            }
        }

        // Verify every `d_open[g]` and `e_open[g]` lies in `C` with Boolean `0..56`!
        for g in 0..STATE_BITS {
            let d_cw: &[u8; MINIMAC_CODE_N] = d_open
                [g * MINIMAC_CODE_N..(g + 1) * MINIMAC_CODE_N]
                .try_into()
                .map_err(|_| CnfRssError::InvalidParameters)?;
            let e_cw: &[u8; MINIMAC_CODE_N] = e_open
                [g * MINIMAC_CODE_N..(g + 1) * MINIMAC_CODE_N]
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

        // Compute `de_prod = d_open * e_open` once publicly via GFNI, and open `v_star`!
        qsag_asm::gf256_shamir_mul(&mut de_prod, &d_open, &e_open);
        vstar_open.fill(0);
        let mut vstar_mac_shares = SecretBuffer(vec![vec![0u8; STATE_CODE_BYTES]; t]);

        for p in 0..t {
            let a_rnd = &tuple.a[p][r_off..r_off + STATE_CODE_BYTES];
            let b_rnd = &tuple.b[p][r_off..r_off + STATE_CODE_BYTES];
            let cr_rnd = &tuple.cr_star[p][r_off..r_off + STATE_CODE_BYTES];
            qsag_asm::gf256_shamir_mul(&mut tmp_mul1, &d_open, b_rnd);
            qsag_asm::gf256_shamir_mul(&mut tmp_mul2, &e_open, a_rnd);
            for i in 0..STATE_CODE_BYTES {
                let mut vs = cr_rnd[i] ^ tmp_mul1[i] ^ tmp_mul2[i];
                if p == 0 {
                    vs ^= de_prod[i];
                }
                vstar_open[i] ^= vs;
            }

            let am_rnd = &tuple.a_mac[p][r_off..r_off + STATE_CODE_BYTES];
            let bm_rnd = &tuple.b_mac[p][r_off..r_off + STATE_CODE_BYTES];
            let crm_rnd = &tuple.cr_star_mac[p][r_off..r_off + STATE_CODE_BYTES];
            qsag_asm::gf256_shamir_mul(&mut tmp_mul1, &d_open, bm_rnd);
            qsag_asm::gf256_shamir_mul(&mut tmp_mul2, &e_open, am_rnd);
            for i in 0..STATE_CODE_BYTES {
                vstar_mac_shares[p][i] = crm_rnd[i] ^ tmp_mul1[i] ^ tmp_mul2[i];
            }
            qsag_asm::gf256_shamir_mul(&mut tmp_mul1, &de_prod, &delta_tiles[p]);
            for i in 0..STATE_CODE_BYTES {
                vstar_mac_shares[p][i] ^= tmp_mul1[i];
            }
        }

        // Check Booleanity on `vstar_open[g][0..56]` and encode `w_pub[g] = enc_56(vstar_open[g][0..56])`
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

        // Transcript-bind `(d_open, e_open, vstar_open)` for this round, check `C^{*2}` parity
        // via 16 independent `GF(2^8)` random linear combinations (`2^{-128}`), and fold into
        // `residual_shares: [Tower128; 128]`!
        tr_xof.absorb(&(rnd as u64).to_le_bytes());
        tr_xof.absorb(&d_open);
        tr_xof.absorb(&e_open);
        tr_xof.absorb(&vstar_open);
        let mut rnd_chal_seed = [0u8; 32];
        let mut chal_xof = tr_xof.clone();
        chal_xof.squeeze(&mut rnd_chal_seed);

        let mut c2_xof = Cshake256Xof::new(b"QSAG.CNF_RSS.C2_FOLD/v1");
        c2_xof.absorb(&rnd_chal_seed);
        let mut lambdas = [0u8; 16 * STATE_BITS];
        c2_xof.squeeze(&mut lambdas);
        for rep in 0..16 {
            let mut folded_c2 = [0u8; MINIMAC_CODE_N];
            let l_slice = &lambdas[rep * STATE_BITS..(rep + 1) * STATE_BITS];
            for (g, &lg) in l_slice.iter().enumerate() {
                let l = TowerGf256(lg);
                let vs = &vstar_open[g * MINIMAC_CODE_N..(g + 1) * MINIMAC_CODE_N];
                for j in 0..MINIMAC_CODE_N {
                    folded_c2[j] ^= l.mul(TowerGf256(vs[j])).0;
                }
            }
            if !tables.verify_public_c2(&folded_c2) {
                return Err(CnfRssError::ActiveTamperDetected {
                    phase: "chi_vstar_c2_degree_check",
                });
            }
        }

        // Fold `(d_open, e_open, vstar_open)` MAC residuals into `residual_shares[u][0..128]` (`Tower128`).
        let mut mac_xof = Cshake256Xof::new(b"QSAG.CNF_RSS.MAC_FOLD/v1");
        mac_xof.absorb(&rnd_chal_seed);
        let mut chi_bytes = [0u8; 3 * STATE_BITS * 16];
        mac_xof.squeeze(&mut chi_bytes);

        for g in 0..STATE_BITS {
            let c_off = 3 * g * 16;
            let chi_d = Tower128(u128::from_le_bytes(
                chi_bytes[c_off..c_off + 16].try_into().unwrap_or([0; 16]),
            ));
            let chi_e = Tower128(u128::from_le_bytes(
                chi_bytes[c_off + 16..c_off + 32]
                    .try_into()
                    .unwrap_or([0; 16]),
            ));
            let chi_v = Tower128(u128::from_le_bytes(
                chi_bytes[c_off + 32..c_off + 48]
                    .try_into()
                    .unwrap_or([0; 16]),
            ));
            let base = g * MINIMAC_CODE_N;
            let am_base = r_off + base;
            for p in 0..t {
                for j in 0..MINIMAC_CODE_N {
                    let dm = not_u_mac[p][base + j] ^ tuple.a_mac[p][am_base + j];
                    let em = v_mac[p][base + j] ^ tuple.b_mac[p][am_base + j];
                    let vm = vstar_mac_shares[p][base + j];

                    let d_term = TowerGf256(dm).add(
                        TowerGf256(d_open[base + j]).mul(TowerGf256(tuple.delta_shares[p][j])),
                    );
                    let e_term = TowerGf256(em).add(
                        TowerGf256(e_open[base + j]).mul(TowerGf256(tuple.delta_shares[p][j])),
                    );
                    let v_term = TowerGf256(vm).add(
                        TowerGf256(vstar_open[base + j])
                            .mul(TowerGf256(tuple.delta_shares[p][j])),
                    );

                    residual_shares[p][j] = residual_shares[p][j]
                        .add(chi_d.mul_gf256(d_term))
                        .add(chi_e.mul_gf256(e_term))
                        .add(chi_v.mul_gf256(v_term));
                }
            }
        }

        // Advance `state_sh` and `state_mac` (`out = lin ^ r ^ w_pub`, plus `Iota` on `0..64`)!
        for p in 0..t {
            let r_rnd = &tuple.r[p][r_off..r_off + STATE_CODE_BYTES];
            let rm_rnd = &tuple.r_mac[p][r_off..r_off + STATE_CODE_BYTES];
            qsag_asm::gf256_shamir_mul(&mut tmp_mul1, &w_pub, &delta_tiles[p]);
            for i in 0..STATE_CODE_BYTES {
                let mut ns = lin_sh[p][i] ^ r_rnd[i];
                if p == 0 {
                    ns ^= w_pub[i];
                }
                state_sh[p][i] = ns;
                state_mac[p][i] = lin_mac[p][i] ^ rm_rnd[i] ^ tmp_mul1[i];
            }
            for z in 0..64 {
                if ((rc >> z) & 1) == 1 {
                    let off = z * MINIMAC_CODE_N;
                    if p == 0 {
                        for b in &mut state_sh[0][off..off + MINIMAC_CODE_N] {
                            *b ^= 1;
                        }
                    }
                    for j in 0..MINIMAC_CODE_N {
                        state_mac[p][off + j] ^= tuple.delta_shares[p][j];
                    }
                }
            }
        }
    }

    let mut wave_digest = [0u8; 32];
    tr_xof.squeeze(&mut wave_digest);

    let dig_bytes = DIGEST_BITS * MINIMAC_CODE_N;
    for p in 0..t {
        state_sh[p].truncate(dig_bytes);
        state_mac[p].truncate(dig_bytes);
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
            delta_shares: SecretBuffer(Vec::new()),
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
            pend.delta_shares.secret_wipe();
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
            for u in 0..t {
                for j in 0..MINIMAC_CODE_N {
                    let v = prev.sh[u][src_off + j];
                    sh[u][dst_off + j] ^= v;
                    cur_cw[j] ^= v;
                }
            }
            qsag_asm::gf256_shamir_mul(&mut *new_mac_sum, &*cur_cw, &*new_delta_sum);
            for u in 0..(t - 1) {
                let qu = self.projected.quorum[u];
                let qt = self.projected.quorum[t - 1];
                let mut xof = Cshake256Xof::new(b"QSAG.CNF_RSS.CHAIN_MAC_TRANS/v1");
                xof.absorb(&self.quorum_shares[u].pair_prf_keys[qt]);
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
        let mut combined = SecretBuffer(vec![[Tower128::ZERO; MINIMAC_CODE_N]; t]);
        for pend in &self.pending {
            let mut wb = [0u8; 16];
            weight_xof.squeeze(&mut wb);
            let w = Tower128(u128::from_le_bytes(wb));
            for u in 0..t {
                for j in 0..MINIMAC_CODE_N {
                    combined[u][j] = combined[u][j].add(w.mul(pend.residual_shares[u][j]));
                }
            }
        }
        for pend in &mut self.pending {
            pend.residual_shares.secret_wipe();
        }
        self.pending.clear();

        // Commit-then-open all 128 `Tower128` coordinate residuals (each backed by a fresh
        // single-use ephemeral per-wave `Delta^{(w)}` that is already burned!).
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
            for j in 0..MINIMAC_CODE_N {
                cx.absorb(&combined[u][j].0.to_le_bytes());
            }
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
            for j in 0..MINIMAC_CODE_N {
                cx.absorb(&combined[u][j].0.to_le_bytes());
            }
            let mut exp = [0u8; 32];
            cx.squeeze(&mut exp);
            if !ct_eq_bytes32(&exp, &coms[u]) {
                return self.fail(CnfRssError::CommitmentMismatch {
                    phase: "minimac_barrier",
                    party: self.projected.quorum[u],
                });
            }
        }

        let mut any_nonzero = 0u128;
        for j in 0..MINIMAC_CODE_N {
            let mut acc = 0u128;
            for u in 0..t {
                acc ^= combined[u][j].0;
            }
            any_nonzero |= black_box(acc);
        }
        if any_nonzero != 0 {
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
            for chunk in m_pub_tile.chunks_exact_mut(MINIMAC_CODE_N) {
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
            for chunk in d_tile.chunks_exact_mut(MINIMAC_CODE_N) {
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
            if s.slh_params.is_some()
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

    fn sweep(&mut self, pk_seed: &[u8; 32], lanes: Vec<LaneSpec>) -> Result<CnfRssSweep, BaggyError> {
        self.ensure_live()?;
        if lanes.is_empty()
            || lanes.windows(2).any(|w| w[0].steps < w[1].steps)
            || self.projected.key_len != 32
            || !ct_eq_bytes32(pk_seed, &self.projected.pk_seed)
        {
            return Err(BaggyError::Engine(Rss256Error::InvalidParameters));
        }

        let chunks: Vec<&[LaneSpec]> = lanes.chunks(MINIMAC_DATA_K).collect();
        let total_perms: usize = chunks.iter().map(|c| 1 + usize::from(c[0].steps)).sum();
        let mut all_tuples = match self.source.next_wave_tuples(total_perms) {
            Ok(t) => t,
            Err(e) => return Err(self.fail::<CnfRssSweep>(e).unwrap_err().into()),
        };

        // Partition exact tuple slices per 56-lane chunk so all chunks run in parallel across cores!
        let mut chunk_jobs: Vec<(&[LaneSpec], usize, Vec<ProjectedWaveTuple>)> =
            Vec::with_capacity(chunks.len());
        let mut base_w = self.wave_ctr;
        for chunk in &chunks {
            let need = 1 + usize::from(chunk[0].steps);
            let rem_at = all_tuples.len() - need;
            let c_tuples = all_tuples.split_off(rem_at);
            chunk_jobs.push((chunk, base_w, c_tuples));
            base_w += need;
        }
        self.wave_ctr = base_w;

        let eval_chunk = |(chunk, start_w, mut c_tuples): &(
            &[LaneSpec],
            usize,
            Vec<ProjectedWaveTuple>,
        )|
         -> Result<(Vec<CnfRssSharedDigests>, Vec<PendingWaveVerification>), CnfRssError> {
            // Drain from back so no shifts occur
            let tup0 = c_tuples
                .pop()
                .ok_or(CnfRssError::BeaverBankExhausted)?;
            let frames0: Vec<[u8; SHAKE256_RATE_BYTES]> = chunk
                .iter()
                .map(|l| tsw_secret32_frame(TAG_PRF, pk_seed, &l.prf))
                .collect();
            let (mut sh0, mut mac0) =
                self.init_public_states(&TSW_SUITE_MIDSTATE, &frames0, &tup0.delta_shares);
            self.absorb_projected_key(false, TSW_PRF_SECRET_OFFSET, &mut sh0, &mut mac0, &tup0.delta_shares);
            let (dig0, pend0) = eval_minimac_wave_perm(
                &self.tables,
                &self.session_id,
                *start_w,
                chunk.len(),
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
                    .ok_or(CnfRssError::BeaverBankExhausted)?;
                let (mut sh_s, mut mac_s) =
                    self.init_public_states(&TSW_SUITE_MIDSTATE, &frames_s, &tup_s.delta_shares);
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
                    *start_w + 1 + usize::from(step),
                    running,
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

        // Re-wrap `eval_chunk` over owned `chunk_jobs` across parallel worker threads under `std`!
        let outcomes: Vec<Result<(Vec<CnfRssSharedDigests>, Vec<PendingWaveVerification>), CnfRssError>> = {
            #[cfg(feature = "std")]
            {
                let workers = std::thread::available_parallelism()
                    .map_or(1, usize::from)
                    .min(12);
                let batch_sz = chunk_jobs.len().div_ceil(workers).max(1);
                let mut results: Vec<
                    Option<Result<(Vec<CnfRssSharedDigests>, Vec<PendingWaveVerification>), CnfRssError>>,
                > = (0..chunk_jobs.len()).map(|_| None).collect();
                let this: &Self = self;
                std::thread::scope(|scope| {
                    let mut handles = Vec::new();
                    for (j_slice, r_slice) in
                        chunk_jobs.chunks_mut(batch_sz).zip(results.chunks_mut(batch_sz))
                    {
                        handles.push(scope.spawn(move || {
                            for (job, dst) in j_slice.iter_mut().zip(r_slice.iter_mut()) {
                                let taken = (job.0, job.1, core::mem::take(&mut job.2));
                                *dst = Some({
                                    let (chunk, start_w, mut c_tuples) = taken;
                                    let run = || -> Result<_, CnfRssError> {
                                        let tup0 = c_tuples
                                            .pop()
                                            .ok_or(CnfRssError::BeaverBankExhausted)?;
                                        let frames0: Vec<[u8; SHAKE256_RATE_BYTES]> = chunk
                                            .iter()
                                            .map(|l| tsw_secret32_frame(TAG_PRF, pk_seed, &l.prf))
                                            .collect();
                                        let (mut sh0, mut mac0) = this.init_public_states(
                                            &TSW_SUITE_MIDSTATE,
                                            &frames0,
                                            &tup0.delta_shares,
                                        );
                                        this.absorb_projected_key(
                                            false,
                                            TSW_PRF_SECRET_OFFSET,
                                            &mut sh0,
                                            &mut mac0,
                                            &tup0.delta_shares,
                                        );
                                        let (dig0, pend0) = eval_minimac_wave_perm(
                                            &this.tables,
                                            &this.session_id,
                                            start_w,
                                            chunk.len(),
                                            sh0,
                                            mac0,
                                            tup0,
                                            #[cfg(test)]
                                            this.fault,
                                        )?;
                                        let mut wave_digs = vec![dig0];
                                        let mut pends = vec![pend0];
                                        for step in 0..chunk[0].steps {
                                            let running =
                                                chunk.iter().take_while(|l| l.steps > step).count();
                                            let frames_s: Vec<[u8; SHAKE256_RATE_BYTES]> = chunk
                                                [..running]
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
                                                .ok_or(CnfRssError::BeaverBankExhausted)?;
                                            let (mut sh_s, mut mac_s) = this.init_public_states(
                                                &TSW_SUITE_MIDSTATE,
                                                &frames_s,
                                                &tup_s.delta_shares,
                                            );
                                            let prev = &wave_digs[usize::from(step)];
                                            this.absorb_shared_digests(
                                                prev,
                                                TSW_F_SECRET_OFFSET,
                                                &mut sh_s,
                                                &mut mac_s,
                                                &tup_s.delta_shares,
                                            );
                                            let (dig_s, pend_s) = eval_minimac_wave_perm(
                                                &this.tables,
                                                &this.session_id,
                                                start_w + 1 + usize::from(step),
                                                running,
                                                sh_s,
                                                mac_s,
                                                tup_s,
                                                #[cfg(test)]
                                                this.fault,
                                            )?;
                                            wave_digs.push(dig_s);
                                            pends.push(pend_s);
                                        }
                                        Ok((wave_digs, pends))
                                    };
                                    run()
                                });
                            }
                        }));
                    }
                    for h in handles {
                        let _ = h.join();
                    }
                });
                let _ = eval_chunk;
                results.into_iter().flatten().collect()
            }
            #[cfg(not(feature = "std"))]
            {
                chunk_jobs.iter().map(eval_chunk).collect()
            }
        };

        let mut pos = Vec::with_capacity(outcomes.len());
        for outcome in outcomes {
            match outcome {
                Ok((digs, pends)) => {
                    self.pending.extend(pends);
                    pos.push(digs);
                }
                Err(e) => return Err(self.fail::<CnfRssSweep>(e).unwrap_err().into()),
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
