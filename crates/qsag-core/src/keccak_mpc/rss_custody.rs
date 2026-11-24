use super::*;

// ============================================================================
// 1. Active 2-of-3 Replicated Secret Sharing (`RSS`) 64-Way `Keccak-f[1600]`
// ============================================================================

/// Isolated 2-of-3 RSS custody share for party `party_id in 0..3`:
/// holds ONLY `(s_{party_id}, s_{(party_id + 1) % 3})` (`!Clone`, redacted `Debug`, wiped on `Drop`).
pub struct RssKeyShare256 {
    pub party_id: usize,
    pub key_len: usize,
    pub pk_seed: [u8; 32],
    pub(super) sk_seed_primary: [u8; 32],
    pub(super) sk_seed_secondary: [u8; 32],
    pub(super) sk_prf_primary: [u8; 32],
    pub(super) sk_prf_secondary: [u8; 32],
    prg_seed_primary: [u8; 32],
    pub(super) prg_seed_secondary: [u8; 32],
    /// Stateless hash-signature key this share belongs to, recorded by
    /// [`DkgCachedSubtrees::build_distributed_rss`] when the public root is first computed
    /// from the shares. `None` until then.
    pub(super) tsw_binding: Option<TswKeyBinding>,
    /// Identity of the hash-signature key and parameter set this share was generated for,
    /// recorded once by the scheme's key generation (see [`Self::bind_scheme_identity`]).
    pub(super) scheme_identity: Option<[u8; 32]>,
    pub(super) slh_profile_digest: Option<[u64; 4]>,
}

/// Parameter-set digest and public root that a set of RSS key shares was generated for.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) struct TswKeyBinding {
    pub(super) params_digest: [u8; 32],
    pub(super) pk_root: [u8; 32],
}

/// Digest of every field of a stateless hash-signature parameter set.
pub(super) fn tsw_params_digest(params: &PqHashParams) -> [u8; 32] {
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

/// Replicated 200-byte (`[u64; 25]`) `Keccak-f[1600]` state pair `(mine, next)` for one 2-of-3 RSS party.
pub type ReplicatedKeccakStatePair = ([u64; 25], [u64; 25]);

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
        if self.slh_profile_digest.is_some() || self.tsw_binding.is_some() {
            return Err(KeccakMpcError::KeyBindingMismatch);
        }
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

    /// Construct replicated 200-byte (`[u64; 25]`) `Keccak-f[1600]` state shares `(mine, next)`
    /// for a bound scheme identity by folding `public_template` onto slot `0` and embedding this
    /// custodian's `(primary, secondary)` key shares at `secret_byte_offset..secret_byte_offset + key_len`.
    pub fn replicated_keccak_state_shares(
        &self,
        expected_scheme_identity: &[u8; 32],
        use_prf: bool,
        public_template: &[u64; 25],
        secret_byte_offset: usize,
    ) -> Result<SecretBuffer<ReplicatedKeccakStatePair>, KeccakMpcError> {
        if self.party_id >= 3 || !matches!(self.key_len, 16 | 24 | 32) {
            return Err(KeccakMpcError::InvalidParameters);
        }
        match &self.scheme_identity {
            Some(bound) if ct_eq_bytes32(bound, expected_scheme_identity) => {}
            _ => return Err(KeccakMpcError::KeyBindingMismatch),
        }
        let end = secret_byte_offset
            .checked_add(self.key_len)
            .ok_or(KeccakMpcError::InvalidParameters)?;
        if end > 200 {
            return Err(KeccakMpcError::InvalidParameters);
        }
        let (prim, sec) = if use_prf {
            self.sk_prf_shares()
        } else {
            self.sk_seed_shares()
        };
        let mut mine_bytes = SecretBuffer([0u8; 200]);
        let mut next_bytes = SecretBuffer([0u8; 200]);
        if self.party_id == 0 {
            for (i, &w) in public_template.iter().enumerate() {
                mine_bytes[8 * i..8 * i + 8].copy_from_slice(&w.to_le_bytes());
            }
        } else if self.party_id == 2 {
            for (i, &w) in public_template.iter().enumerate() {
                next_bytes[8 * i..8 * i + 8].copy_from_slice(&w.to_le_bytes());
            }
        }
        for k in 0..self.key_len {
            mine_bytes[secret_byte_offset + k] ^= prim[k];
            next_bytes[secret_byte_offset + k] ^= sec[k];
        }
        let mut pair = SecretBuffer(([0u64; 25], [0u64; 25]));
        for i in 0..25 {
            let mut m8 = [0u8; 8];
            let mut n8 = [0u8; 8];
            m8.copy_from_slice(&mine_bytes[8 * i..8 * i + 8]);
            n8.copy_from_slice(&next_bytes[8 * i..8 * i + 8]);
            pair.0.0[i] = u64::from_le_bytes(m8);
            pair.0.1[i] = u64::from_le_bytes(n8);
        }
        Ok(pair)
    }

    /// Canonical `QSRSSK01` secret serialization: the legacy 268-byte form is unchanged.
    /// Byte 11 selects a fail-closed extension: 1 appends a 32-byte SLH profile digest;
    /// 2 appends the 64-byte TSW parameter/root binding. Old decoders reject both.
    pub fn to_secret_bytes(&self) -> crate::wipe::SecretVec<u8> {
        let profile_flag = if self.slh_profile_digest.is_some() {
            1u8
        } else if self.tsw_binding.is_some() {
            2
        } else {
            0
        };
        // Allocate the final capacity before writing secrets; Vec growth would free
        // an unwiped old allocation even though the final buffer wipes on drop.
        let mut out = SecretBuffer(Vec::with_capacity(268 + 32 * usize::from(profile_flag)));
        out.0.extend_from_slice(b"QSRSSK01");
        out.0.push(self.party_id as u8);
        out.0.push(self.key_len as u8);
        let (has_scheme_id, scheme_id_bytes) = match &self.scheme_identity {
            Some(id) => (1u8, *id),
            None => (0u8, [0u8; 32]),
        };
        out.0.push(has_scheme_id);
        out.0.push(profile_flag);
        out.0.extend_from_slice(&self.pk_seed);
        out.0.extend_from_slice(&self.sk_seed_primary);
        out.0.extend_from_slice(&self.sk_seed_secondary);
        out.0.extend_from_slice(&self.sk_prf_primary);
        out.0.extend_from_slice(&self.sk_prf_secondary);
        out.0.extend_from_slice(&self.prg_seed_primary);
        out.0.extend_from_slice(&self.prg_seed_secondary);
        out.0.extend_from_slice(&scheme_id_bytes);
        if let Some(profile) = self.slh_profile_digest {
            for word in profile {
                out.extend_from_slice(&word.to_le_bytes());
            }
        } else if let Some(binding) = self.tsw_binding {
            out.extend_from_slice(&binding.params_digest);
            out.extend_from_slice(&binding.pk_root);
        }
        debug_assert_eq!(out.0.len(), 268 + 32 * usize::from(profile_flag));
        out
    }

    /// Decode a canonical `QSRSSK01` custodian share, retaining suite bindings and rejecting malformed headers
    /// or non-zero trailing `scheme_identity` bytes when `has_scheme_id == 0`.
    pub fn from_secret_bytes(bytes: &[u8]) -> Result<Self, KeccakMpcError> {
        if bytes.len() < 268 || &bytes[0..8] != b"QSRSSK01" {
            return Err(KeccakMpcError::InvalidParameters);
        }
        let party_id = usize::from(bytes[8]);
        let key_len = usize::from(bytes[9]);
        let has_scheme_id = bytes[10];
        let profile_flag = bytes[11];
        if party_id >= 3
            || !matches!(key_len, 16 | 24 | 32)
            || has_scheme_id > 1
            || profile_flag > 2
            || bytes.len() != 268 + 32 * usize::from(profile_flag)
            || (profile_flag != 0 && has_scheme_id != 0)
        {
            return Err(KeccakMpcError::InvalidParameters);
        }
        let read32 = |off: usize| -> [u8; 32] {
            let mut arr = [0u8; 32];
            arr.copy_from_slice(&bytes[off..off + 32]);
            arr
        };
        let slh_profile_digest = (profile_flag == 1).then(|| {
            core::array::from_fn(|i| {
                u64::from_le_bytes(core::array::from_fn(|b| bytes[268 + 8 * i + b]))
            })
        });
        let tsw_binding = (profile_flag == 2).then(|| TswKeyBinding {
            params_digest: read32(268),
            pk_root: read32(300),
        });
        let pk_seed = read32(12);
        let sk_seed_primary = SecretBuffer(read32(44));
        let sk_seed_secondary = SecretBuffer(read32(76));
        let sk_prf_primary = SecretBuffer(read32(108));
        let sk_prf_secondary = SecretBuffer(read32(140));
        let prg_seed_primary = SecretBuffer(read32(172));
        let prg_seed_secondary = SecretBuffer(read32(204));
        let scheme_id_bytes = read32(236);
        let scheme_identity = if has_scheme_id == 1 {
            Some(scheme_id_bytes)
        } else {
            if !ct_eq_bytes32(&scheme_id_bytes, &[0u8; 32]) {
                return Err(KeccakMpcError::InvalidParameters);
            }
            None
        };
        if key_len < 32
            && (!ct_eq_bytes(&pk_seed[key_len..], &[0u8; 32][key_len..])
                || !ct_eq_bytes(&sk_seed_primary[key_len..], &[0u8; 32][key_len..])
                || !ct_eq_bytes(&sk_seed_secondary[key_len..], &[0u8; 32][key_len..])
                || !ct_eq_bytes(&sk_prf_primary[key_len..], &[0u8; 32][key_len..])
                || !ct_eq_bytes(&sk_prf_secondary[key_len..], &[0u8; 32][key_len..]))
        {
            return Err(KeccakMpcError::InvalidParameters);
        }
        Ok(Self {
            party_id,
            key_len,
            pk_seed,
            sk_seed_primary: sk_seed_primary.0,
            sk_seed_secondary: sk_seed_secondary.0,
            sk_prf_primary: sk_prf_primary.0,
            sk_prf_secondary: sk_prf_secondary.0,
            prg_seed_primary: prg_seed_primary.0,
            prg_seed_secondary: prg_seed_secondary.0,
            tsw_binding,
            scheme_identity,
            slh_profile_digest,
        })
    }

    /// Construct a 2-of-3 RSS custodian share directly from replicated share pairs without
    /// assembling any combined secret.
    pub fn from_replicated_shares(
        party_id: usize,
        key_len: usize,
        pk_seed: [u8; 32],
        sk_seed: ([u8; 32], [u8; 32]),
        sk_prf: ([u8; 32], [u8; 32]),
        prg_seed: ([u8; 32], [u8; 32]),
    ) -> Result<Self, KeccakMpcError> {
        let mut sk_seed = SecretBuffer([sk_seed.0, sk_seed.1]);
        let mut sk_prf = SecretBuffer([sk_prf.0, sk_prf.1]);
        let prg_seed = SecretBuffer([prg_seed.0, prg_seed.1]);
        if party_id >= 3 || !matches!(key_len, 16 | 24 | 32) {
            return Err(KeccakMpcError::InvalidParameters);
        }
        let mut pk_norm = pk_seed;
        pk_norm[key_len..32].fill(0);
        sk_seed.0[0][key_len..32].fill(0);
        sk_seed.0[1][key_len..32].fill(0);
        sk_prf.0[0][key_len..32].fill(0);
        sk_prf.0[1][key_len..32].fill(0);
        Ok(Self {
            party_id,
            key_len,
            pk_seed: pk_norm,
            sk_seed_primary: sk_seed.0[0],
            sk_seed_secondary: sk_seed.0[1],
            sk_prf_primary: sk_prf.0[0],
            sk_prf_secondary: sk_prf.0[1],
            prg_seed_primary: prg_seed.0[0],
            prg_seed_secondary: prg_seed.0[1],
            tsw_binding: None,
            scheme_identity: None,
            slh_profile_digest: None,
        })
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
            slh_profile_digest: None,
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
pub(super) struct RssPoisonLatch(AtomicBool);

impl RssPoisonLatch {
    pub(super) const fn new() -> Self {
        Self(AtomicBool::new(false))
    }

    pub(super) fn set(&self) {
        self.0.store(true, Ordering::Relaxed);
    }

    pub(super) fn is_set(&self) -> bool {
        self.0.load(Ordering::Relaxed)
    }

    /// Latches and returns `err`.
    pub(super) fn fail<T>(&self, err: KeccakMpcError) -> Result<T, KeccakMpcError> {
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
pub(super) fn rss_commit_and_open_u64_batch(
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
        opened.push(qsag_verified::rss_reconstruct(qsag_verified::RssShare64 {
            x0: primary_shares[0][k],
            x1: primary_shares[1][k],
            x2: primary_shares[2][k],
        }));
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
    pub(super) shared: bool,
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
    pub(super) fn derive(
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
    pub(super) fn hedge_transcript(&mut self, transcript: &[u8]) {
        for slots in [&mut self.prim, &mut self.sec] {
            for key in slots {
                let mut next = [0; 32];
                crate::preprocessing::HedgedTranscriptRng::derive(
                    key,
                    0,
                    &[],
                    transcript,
                    &mut next,
                );
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
    pub(super) fn chi_streams(
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
pub(super) struct RssProofStreams {
    prim: [Cshake256Xof; 3],
    sec: Option<[Cshake256Xof; 3]>,
}

impl RssProofStreams {
    pub(super) fn new(mask: &RssMaskSession, session_id: &[u8; 32], batch_ctr: u64) -> Self {
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
    pub(super) fn draw(&mut self) -> ([RssProofField; 3], [RssProofField; 3]) {
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
    pub(super) fn zero_share(&mut self) -> [RssProofField; 3] {
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
    pub(super) lane_perms: u64,
    /// Halving-round tables, kept between verifications and all zero outside a proof pass.
    pub(super) fold_tables: RssDzkTables,
    /// Set when a verification of this accumulator failed. A poisoned accumulator records
    /// nothing and never verifies again, so an emptied relation set cannot pass for a
    /// verified one.
    pub(super) poison: RssPoisonLatch,
}

impl RssPendingDzkTriples {
    pub(crate) fn new() -> Self {
        Self {
            a: [Vec::new(), Vec::new(), Vec::new()],
            b: [Vec::new(), Vec::new(), Vec::new()],
            c: [Vec::new(), Vec::new(), Vec::new()],
            lane_perms: 0,
            fold_tables: RssDzkTables::default(),
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

    pub(super) fn clear_and_wipe(&mut self) {
        for s in 0..3 {
            for words in [&mut self.a[s], &mut self.b[s], &mut self.c[s]] {
                wipe_u64s(words);
                words.clear();
            }
        }
    }

    pub(super) fn pad_to_group(&mut self) {
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
