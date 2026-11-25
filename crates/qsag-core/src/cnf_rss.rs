//! Generalized `(t, n)` CNF replicated secret sharing custody (`CnfRssConfig`,
//! `CnfRssKeyShare256`, `run_dealerless_cnf_rss_dkg`) and the sealed [`IsolatedSlhBackend`]
//! / [`IsolatedCnfSlhOracles`] bridge for zero-coordinator isolated-party `SLH-DSA` signing
//! (`qsag_quorum::cnf_party::IsolatedCnfParty`).
//!
//! Custody uses one slot for each `(t - 1)`-party subset `S`; party `i` holds that
//! slot exactly when `i` is not in `S`. Any `(t - 1)`-party coalition misses its own
//! slot. Honest-majority configurations (`2 * (t - 1) < n`, such as `2-of-3` and `3-of-5`)
//! execute full `Baggy` and `SLH-DSA` signing ceremonies directly over isolated custodian
//! parties (`qsag_quorum::cnf_party::IsolatedCnfParty`) with zero trusted coordinator.

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;
use core::hint::black_box;

use crate::baggy::{BaggyError, keyed_mu_frame};
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
use crate::sponge::keccak::{Cshake256Xof, SHAKE256_RATE_BYTES, cshake256_32_multi_frame};
use crate::tsw_baggy::HashAdrs;
use crate::wipe::{SecretBuffer, SecretVec, ct_eq_bytes, ct_eq_bytes32};

/// Maximum custodian count supported by `CnfRssConfig`.
pub const MAX_CNF_RSS_PARTIES: usize = 10;
/// Canonical wire header for `CnfRssKeyShare256`.
const CNF_KEY_SHARE_MAGIC: &[u8; 8] = b"QSCNFK01";

/// Errors surfaced by `(t, n)` CNF-RSS custody.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CnfRssError {
    /// Invalid `(t, n)`, `key_len`, or quorum subset.
    InvalidParameters,
    /// Underlying commit-and-open or RNG protocol failure.
    Preprocess(PreprocessError),
    /// Round-2 commitment mismatch attributed to `party`.
    CommitmentMismatch { phase: &'static str, party: usize },
    /// Key shares are unbound or bound to a different public key / parameter set.
    KeyBindingMismatch,
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
        }
    }
}

impl From<CnfRssError> for BaggyError {
    fn from(e: CnfRssError) -> Self {
        match e {
            CnfRssError::InvalidParameters => Self::Engine(Rss256Error::InvalidParameters),
            CnfRssError::KeyBindingMismatch => Self::KeyBindingMismatch,
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
            Self::KeyBindingMismatch => f.write_str("CNF-RSS key binding mismatch"),
        }
    }
}

impl core::error::Error for CnfRssError {}

// ============================================================================
// 1. `(t, n)` CNF-RSS Combinatorics and Dealerless DKG
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

    /// Subset $S_{\text{slot}} \in \binom{\[n\]}{t-1}$ of custodians EXCLUDED from holding `slot_idx`.
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

    #[inline]
    pub fn slh_profile_digest(&self) -> Option<[u64; 4]> {
        self.slh_profile_digest
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

    /// Enroll one endpoint's private DKG output in the canonical custody format.
    /// All secret vectors are move-only and erased on an invalid shape or encoding.
    #[allow(clippy::too_many_arguments)]
    pub fn from_dkg_slots(
        cfg: CnfRssConfig,
        party_id: usize,
        key_len: usize,
        pk_seed: [u8; 32],
        sk_seed_slots: SecretVec<[u8; 32]>,
        sk_prf_slots: SecretVec<[u8; 32]>,
        slot_prg_seeds: SecretVec<[u8; 32]>,
        pair_prf_keys: SecretVec<[u8; 32]>,
    ) -> Result<Self, CnfRssError> {
        let slot_indices = cfg.party_slot_indices(party_id)?;
        let k = slot_indices.len();
        if !matches!(key_len, 16 | 24 | 32)
            || pk_seed[key_len..].iter().any(|&v| v != 0)
            || sk_seed_slots.len() != k
            || sk_prf_slots.len() != k
            || slot_prg_seeds.len() != k
            || pair_prf_keys.len() != cfg.n
        {
            return Err(CnfRssError::InvalidParameters);
        }
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
            slot_indices,
            sk_seed_slots,
            sk_prf_slots,
            slot_prg_seeds,
            pair_prf_keys,
            scheme_identity: None,
            slh_profile_digest: None,
        })
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
        let mut share = Self::from_dkg_slots(
            cfg,
            party_id,
            key_len,
            pk_seed,
            sk_seed_slots,
            sk_prf_slots,
            slot_prg_seeds,
            pair_prf_keys,
        )?;
        share.scheme_identity = scheme_identity;
        share.slh_profile_digest = slh_profile_digest;
        Ok(share)
    }
}

/// Dealerless pure-hash `(t, n)` CNF-RSS distributed key generation (`0` trusted dealer, `0` RLWE/OT).
///
/// Executes:
/// 1. 2-round committed coin toss deriving `pk_seed` (`key_len` bytes in `16 | 24 | 32`);
/// 2. Per-complement $H_m = \[n\] \setminus S_m$ 2-round committed group seed ceremony deriving
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

/// Compute the 256-bit `SLH-DSA` parameter-profile digest locked by [`CnfRssKeyShare256::bind_slh_params`].
#[inline]
pub fn compute_slh_profile_digest(params: &Fips205Params) -> [u64; 4] {
    crate::keccak_mpc::slh_profile_digest_u64x4(params)
}

#[doc(hidden)]
pub const BAGGY_SUITE_MIDSTATE: [u64; 25] = TSW_SUITE_MIDSTATE;
#[doc(hidden)]
pub const BAGGY_PRF_SECRET_OFFSET: usize = TSW_PRF_SECRET_OFFSET;
#[doc(hidden)]
pub const BAGGY_F_SECRET_OFFSET: usize = TSW_F_SECRET_OFFSET;

#[doc(hidden)]
#[inline]
pub fn baggy_mu_frame(tag: &[u8], mu: &[u8; 32]) -> ([u8; SHAKE256_RATE_BYTES], usize) {
    keyed_mu_frame(tag, mu)
}

#[doc(hidden)]
#[inline]
pub fn baggy_secret32_frame(
    role_tag: &[u8],
    pk_seed: &[u8; 32],
    adrs: &HashAdrs,
) -> [u8; SHAKE256_RATE_BYTES] {
    tsw_secret32_frame(role_tag, pk_seed, adrs)
}

/// Verified isolated-party backend driving NIST FIPS 205 `SLH-DSA` ceremonies without
/// reconstructing `SK.seed`, `SK.prf`, or any intermediate WOTS+/FORS chain wire.
///
/// Implementations (`qsag_quorum::cnf_party::IsolatedCnfParty`) MUST run their active
/// multiplication check barrier and verify replicated slot-copy agreement across holders
/// strictly before returning any opened block.
pub trait IsolatedSlhBackend {
    /// Lock `(params, pk_seed)` on this custodian's key state before secret-derived outputs.
    fn bind_slh_profile(
        &mut self,
        params: &Fips205Params,
        pk_seed: &[u8],
    ) -> Result<(), Fips205Error>;

    /// Evaluate multi-block `R = PRF_msg([SK.prf], opt_rand, m_prime)` on shared wires,
    /// run the active multiplication barrier, and open only the `n`-byte `R`.
    fn eval_prf_msg_verified(
        &mut self,
        n: usize,
        opt_rand: &[u8],
        m_prime: &[u8],
    ) -> Result<SlhBlock, Fips205Error>;

    /// Evaluate a batch of `(prf_adrs, step_adrs[0..steps])` chains on shared `SK.seed`,
    /// keeping `SK.seed` and every intermediate chain node shared, run the active
    /// multiplication barrier before opening, and open only each chain's final `n`-byte block.
    fn eval_chains_verified(
        &mut self,
        n: usize,
        pk_seed: &[u8],
        chains: &[(Fips205Adrs, Vec<Fips205Adrs>)],
    ) -> Result<Vec<SlhBlock>, Fips205Error>;
}

/// Sealed [`SlhMpcOracles`] adapter for an [`IsolatedSlhBackend`] (`IsolatedCnfParty`).
pub struct IsolatedCnfSlhOracles<'a, B: IsolatedSlhBackend>(pub &'a mut B);

impl<B: IsolatedSlhBackend> sealed_mpc_oracles::Sealed for IsolatedCnfSlhOracles<'_, B> {}

impl<B: IsolatedSlhBackend> SlhMpcOracles for IsolatedCnfSlhOracles<'_, B> {
    fn bind_key_params(
        &mut self,
        params: &Fips205Params,
        pk_seed: &[u8],
    ) -> Result<(), Fips205Error> {
        self.0.bind_slh_profile(params, pk_seed)
    }

    fn eval_prf_msg_mpc(
        &mut self,
        n: usize,
        opt_rand: &[u8],
        m_prime: &[u8],
    ) -> Result<(SlhBlock, CutBoundaryMacToken), Fips205Error> {
        let r_blk = self.0.eval_prf_msg_verified(n, opt_rand, m_prime)?;
        Ok((r_blk, CutBoundaryMacToken::mint_verified()))
    }

    fn eval_fors_trees_mpc(
        &mut self,
        params: &Fips205Params,
        pk_seed: &[u8],
        base_adrs: Fips205Adrs,
        fors_indices: &[u32],
    ) -> Result<ForsMpcOutput, Fips205Error> {
        self.0.bind_slh_profile(params, pk_seed)?;
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
        let mut all_out = self.0.eval_chains_verified(n, pk_seed, &chains)?;
        if all_out.len() != params.k + total_leaves {
            return Err(Fips205Error::MpcActiveTamperDetected);
        }
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
        self.0.bind_slh_profile(params, pk_seed)?;
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
        let endpoints = self.0.eval_chains_verified(n, pk_seed, &chains)?;
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
        self.0.bind_slh_profile(params, pk_seed)?;
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
        let nodes = self.0.eval_chains_verified(n, pk_seed, &chains)?;
        Ok((nodes, CutBoundaryMacToken::mint_verified()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn make_rngs(n: usize, tag: u8) -> Vec<PartyPrivateRng> {
        (0..n)
            .map(|i| PartyPrivateRng::from_seed([tag.wrapping_add(i as u8); 32], b"cnf-rss-test"))
            .collect()
    }

    #[test]
    fn cnf_rss_combinatorics_dkg_and_serialization() {
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

        // Dealerless DKG and wire roundtrip.
        let mut rngs = make_rngs(5, 0x10);
        let (mut shares, pk_seed) =
            run_dealerless_cnf_rss_dkg([0x41; 32], &c35, 32, &mut rngs).unwrap();
        shares[0].bind_scheme_identity(&[0x99; 32]).unwrap();
        let raw0 = shares[0].to_secret_bytes();
        let decoded0 = CnfRssKeyShare256::from_secret_bytes(&raw0).unwrap();
        assert_eq!(decoded0.party_id, 0);
        assert_eq!(decoded0.pk_seed, pk_seed);
        assert_eq!(decoded0.scheme_identity(), Some([0x99; 32]));
        let mut tampered_raw = raw0.to_vec();
        tampered_raw[13] = 1; // non-zero reserved byte rejected
        assert!(CnfRssKeyShare256::from_secret_bytes(&tampered_raw).is_err());
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
}
