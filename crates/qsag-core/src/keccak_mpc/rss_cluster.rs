use super::*;

#[inline]
pub(super) fn init_rss_state_from_public_midstate(
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
pub(super) fn eval_rss_keccak_f1600_batch64_record(
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
        // Chi: (~b[x+1]) & b[x+2] == b[x+2] ^ (b[x+1] & b[x+2]), so out[x] = b[x] ^ b[x+2] ^ (b[x+1] & b[x+2]).
        // Every party evaluates the uncomplemented product of a = b[x+1] and b = b[x+2]
        // (`a_p & (b_p ^ b_q) ^ a_q & b_p ^ mask`) and XORs `b_p = b[p][x+2]` locally, matching
        // `RssParticipantKeccak.lean` (`productGate` on uncomplemented operands; note `ThresholdMpc.lean`
        // instead complements share 0 of `b[x+1]` before the AND gate, which reconstructs identically
        // while differing on raw per-share gate transcripts under the same mask stream).
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
                    let t = qsag_verified::rss_party_and_local(
                        ap,
                        aq,
                        bp,
                        bq,
                        mp[p][l0 + z],
                        ms[p][l0 + z],
                    ) & active_mask;
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
///   replicated input equality, and runs both passes of `verify_rss_boolean_triples_bbcggi19`
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

pub(super) fn wipe_rss_states<const N: usize>(prim: &mut [[u64; N]; 3], sec: &mut [[u64; N]; 3]) {
    for p in 0..3 {
        wipe_u64s(&mut prim[p]);
        wipe_u64s(&mut sec[p]);
    }
}

/// Cut-boundary share words of the three parties, collected across batches until the cut
/// is verified and opened. Wiped on `Drop`, so an error return clears them as well.
pub(super) struct RssCutBuffer {
    pub(super) prim: [Vec<u64>; 3],
    pub(super) sec: [Vec<u64>; 3],
}

impl RssCutBuffer {
    pub(super) fn new() -> Self {
        Self {
            prim: [Vec::new(), Vec::new(), Vec::new()],
            sec: [Vec::new(), Vec::new(), Vec::new()],
        }
    }

    #[inline]
    pub(super) fn push_party_slices(
        &mut self,
        party: usize,
        prim_slice: &[u64],
        sec_slice: &[u64],
    ) {
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
    pub(super) batch_ctr: u64,
    pub(super) pending_dzk: RssPendingDzkTriples,
    /// Wiped witness allocations retained across independent chunk groups.
    pub(super) chunk_scratch: Vec<RssPendingDzkTriples>,
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

// This interval is part of the transcript: each flush consumes a counter and verifier coins.
// Increasing it preserves final FIPS bytes but changes subsequent secret shares and proofs.
const RSS_DZK_FLUSH_PERMUTATIONS: usize = 16;
const RSS_RELATION_WORDS_PER_PERMUTATION: usize = 24 * 1600;

pub(super) struct RssChunkPlan {
    pub(super) prf: Vec<Fips205Adrs>,
    pub(super) steps: Vec<(Vec<Fips205Adrs>, u64)>,
}

struct RssChunkResult {
    prim: SecretBuffer<[[u64; 256]; 3]>,
    sec: SecretBuffer<[[u64; 256]; 3]>,
    relations: RssPendingDzkTriples,
    permutations: usize,
}

type RssSpongeStates = (
    SecretBuffer<[[u64; 1600]; 3]>,
    SecretBuffer<[[u64; 1600]; 3]>,
);

fn rss_prf_states(
    keys: &[RssKeyShare256; 3],
    pk_seed: &[u8],
    adrs_batch: &[Fips205Adrs],
) -> RssSpongeStates {
    let batch_len = adrs_batch.len();
    let n = keys[0].key_len;
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
        let (sk_p, sk_s) = keys[p].sk_seed_shares();
        for byte_idx in 0..n {
            for bit in 0..8 {
                let mp = 0u64.wrapping_sub(((sk_p[byte_idx] >> bit) & 1) as u64);
                let ms = 0u64.wrapping_sub(((sk_s[byte_idx] >> bit) & 1) as u64);
                st_p[p][sk_bit_off + 8 * byte_idx + bit] = mp & active_mask;
                st_s[p][sk_bit_off + 8 * byte_idx + bit] = ms & active_mask;
            }
        }
    }

    (st_p, st_s)
}

fn rss_f_states(
    n: usize,
    pk_seed: &[u8],
    adrs_batch: &[Fips205Adrs],
    cur_p: &[[u64; 256]; 3],
    cur_s: &[[u64; 256]; 3],
) -> RssSpongeStates {
    let batch_len = adrs_batch.len();
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

    (st_p, st_s)
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
            || keys.iter().any(|k| {
                k.pk_seed != keys[0].pk_seed
                    || k.scheme_identity != keys[0].scheme_identity
                    || k.tsw_binding != keys[0].tsw_binding
                    || k.slh_profile_digest != keys[0].slh_profile_digest
            })
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
            chunk_scratch: Vec::new(),
            mask_session,
            poisoned: RssPoisonLatch::new(),
        })
    }

    /// Bind the complete SLH profile once, and reject a different public seed or suite.
    pub(super) fn bind_slh_params(
        &mut self,
        params: &Fips205Params,
        pk_seed: &[u8],
    ) -> Result<(), Fips205Error> {
        if !params.is_valid()
            || self.keys.iter().any(|key| {
                key.key_len != params.n
                    || key.pk_seed[..key.key_len] != *pk_seed
                    || key.tsw_binding.is_some()
                    || key.scheme_identity.is_some()
                    || key
                        .slh_profile_digest
                        .is_some_and(|bound| bound != slh_profile_digest_u64x4(params))
            })
        {
            return Err(Fips205Error::InvalidParameterSet);
        }
        for key in &mut self.keys {
            key.slh_profile_digest = Some(slh_profile_digest_u64x4(params));
        }
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

    pub(super) fn ensure_live(&self) -> Result<(), KeccakMpcError> {
        if self.is_poisoned() {
            Err(KeccakMpcError::Poisoned)
        } else {
            Ok(())
        }
    }

    /// The stateless hash-signature binding shared by all three key shares, `None` when no
    /// share is bound. Shares that disagree are refused.
    pub(super) fn tsw_binding(&self) -> Result<Option<TswKeyBinding>, KeccakMpcError> {
        if self
            .keys
            .iter()
            .any(|k| k.slh_profile_digest.is_some() || k.scheme_identity.is_some())
        {
            return Err(KeccakMpcError::KeyBindingMismatch);
        }
        let binding = self.keys[0].tsw_binding;
        if self.keys[1].tsw_binding != binding || self.keys[2].tsw_binding != binding {
            return Err(KeccakMpcError::KeyBindingMismatch);
        }
        Ok(binding)
    }

    /// One 64-way replicated permutation followed by the proof of its AND relations, under
    /// this cluster's next batch counter. Outputs remain shared. On any error the cluster
    /// is poisoned and both state arrays are zeroed.
    pub(super) fn permute_batch64(
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
    pub(super) fn permute_batch64_deferred(
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
        const DEFERRED_DZK_FLUSH_WORDS: usize =
            RSS_DZK_FLUSH_PERMUTATIONS * RSS_RELATION_WORDS_PER_PERMUTATION;
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

    /// Evaluate independent chains with reserved counters, then replay their relation
    /// records through the original proof barriers in call order. No worker opens data
    /// or draws verifier coins, so scheduling does not change the transcript.
    pub(super) fn evaluate_chunks(
        &mut self,
        pk_seed: &[u8],
        plans: &[RssChunkPlan],
        cut: &mut RssCutBuffer,
    ) -> Result<(), KeccakMpcError> {
        let group_size = if cfg!(feature = "std") { 12 } else { 1 };
        for group in plans.chunks(group_size) {
            self.evaluate_chunk_group(pk_seed, group, cut)?;
        }
        Ok(())
    }

    fn evaluate_chunk_group(
        &mut self,
        pk_seed: &[u8],
        plans: &[RssChunkPlan],
        cut: &mut RssCutBuffer,
    ) -> Result<(), KeccakMpcError> {
        self.ensure_live()?;
        let initial_pending = self.pending_dzk.len_words() / RSS_RELATION_WORDS_PER_PERMUTATION;
        let mut offset = 0usize;
        let starts: Vec<_> = plans
            .iter()
            .map(|plan| {
                let start = offset;
                offset += 1 + plan.steps.iter().filter(|(_, mask)| *mask != 0).count();
                start
            })
            .collect();
        let mut scratch = core::mem::take(&mut self.chunk_scratch);
        scratch.resize_with(plans.len(), RssPendingDzkTriples::new);
        let session = &self.session_id;
        let keys = &self.keys;
        let mask_session = &self.mask_session;
        let initial_ctr = self.batch_ctr;
        let evaluate = |index: usize,
                        mut relations: RssPendingDzkTriples|
         -> Result<RssChunkResult, KeccakMpcError> {
            let plan = &plans[index];
            let batch_len = plan.prf.len();
            let n_bits = 8 * keys[0].key_len;
            relations.lane_perms = 0;
            // Scratch contains no live witnesses. Reserve once and retain the allocations
            // across groups, avoiding both capacity doublings and repeated large allocations.
            let permutations = 1 + plan.steps.iter().filter(|(_, mask)| *mask != 0).count();
            let words = permutations * RSS_RELATION_WORDS_PER_PERMUTATION;
            for buffer in relations
                .a
                .iter_mut()
                .chain(&mut relations.b)
                .chain(&mut relations.c)
            {
                debug_assert!(buffer.is_empty());
                buffer.reserve_exact(words);
            }
            let mut ordinal = starts[index];
            let mut permute = |prim: &mut [[u64; 1600]; 3], sec: &mut [[u64; 1600]; 3]| {
                let ctr = initial_ctr.wrapping_add(ordinal as u64).wrapping_add(
                    ((initial_pending + ordinal) / RSS_DZK_FLUSH_PERMUTATIONS) as u64,
                );
                ordinal += 1;
                eval_rss_keccak_f1600_batch64_record(
                    session,
                    ctr,
                    batch_len,
                    prim,
                    sec,
                    mask_session,
                    &mut relations,
                )
            };
            let (mut state_p, mut state_s) = rss_prf_states(keys, pk_seed, &plan.prf);
            permute(&mut state_p, &mut state_s)?;
            let mut prim = SecretBuffer([[0u64; 256]; 3]);
            let mut sec = SecretBuffer([[0u64; 256]; 3]);
            for party in 0..3 {
                prim[party][..n_bits].copy_from_slice(&state_p[party][..n_bits]);
                sec[party][..n_bits].copy_from_slice(&state_s[party][..n_bits]);
            }
            for (addresses, exec_mask) in &plan.steps {
                if *exec_mask == 0 {
                    continue;
                }
                let (mut state_p, mut state_s) =
                    rss_f_states(keys[0].key_len, pk_seed, addresses, &prim, &sec);
                permute(&mut state_p, &mut state_s)?;
                for party in 0..3 {
                    for bit in 0..n_bits {
                        prim[party][bit] =
                            (prim[party][bit] & !exec_mask) | (state_p[party][bit] & exec_mask);
                        sec[party][bit] =
                            (sec[party][bit] & !exec_mask) | (state_s[party][bit] & exec_mask);
                    }
                }
            }
            Ok(RssChunkResult {
                prim,
                sec,
                relations,
                permutations: ordinal - starts[index],
            })
        };
        #[cfg(feature = "std")]
        let results = {
            let mut results: Vec<_> = (0..plans.len()).map(|_| None).collect();
            let workers = std::thread::available_parallelism()
                .map_or(1, usize::from)
                .min(12);
            let chunk_size = plans.len().div_ceil(workers).max(1);
            std::thread::scope(|scope| {
                for (chunk, (slots, buffers)) in results
                    .chunks_mut(chunk_size)
                    .zip(scratch.chunks_mut(chunk_size))
                    .enumerate()
                {
                    let evaluate = &evaluate;
                    scope.spawn(move || {
                        for (offset, (slot, buffer)) in slots.iter_mut().zip(buffers).enumerate() {
                            let relations = core::mem::replace(buffer, RssPendingDzkTriples::new());
                            *slot = Some(evaluate(chunk * chunk_size + offset, relations));
                        }
                    });
                }
            });
            results
                .into_iter()
                .map(|result| result.expect("every chunk evaluated"))
                .collect::<Vec<_>>()
        };
        #[cfg(not(feature = "std"))]
        let results = scratch
            .into_iter()
            .enumerate()
            .map(|(index, relations)| evaluate(index, relations))
            .collect::<Vec<_>>();
        for (plan, result) in plans.iter().zip(results) {
            let mut result = match result {
                Ok(result) => result,
                Err(error) => return self.poisoned.fail(error),
            };
            if self.pending_dzk.len_words() == 0
                && result.permutations <= RSS_DZK_FLUSH_PERMUTATIONS
            {
                // Aligned chains already own exactly the next proof's witnesses.
                // Transfer allocations instead of copying and wiping them twice.
                core::mem::swap(&mut self.pending_dzk.a, &mut result.relations.a);
                core::mem::swap(&mut self.pending_dzk.b, &mut result.relations.b);
                core::mem::swap(&mut self.pending_dzk.c, &mut result.relations.c);
                self.pending_dzk.lane_perms += result.relations.lane_perms;
                self.batch_ctr = self.batch_ctr.wrapping_add(result.permutations as u64);
                if result.permutations == RSS_DZK_FLUSH_PERMUTATIONS {
                    let ctr = self.next_ctr();
                    if let Err(error) = verify_rss_boolean_triples_bbcggi19(
                        &self.session_id,
                        ctr,
                        &mut self.pending_dzk,
                        &self.mask_session,
                        &mut self.party_rngs,
                    ) {
                        return self.poisoned.fail(error);
                    }
                }
            } else {
                for permutation in 0..result.permutations {
                    self.next_ctr();
                    let start = permutation * RSS_RELATION_WORDS_PER_PERMUTATION;
                    let end = start + RSS_RELATION_WORDS_PER_PERMUTATION;
                    for party in 0..3 {
                        secret_vec_extend_from_slice(
                            &mut self.pending_dzk.a[party],
                            &result.relations.a[party][start..end],
                        );
                        secret_vec_extend_from_slice(
                            &mut self.pending_dzk.b[party],
                            &result.relations.b[party][start..end],
                        );
                        secret_vec_extend_from_slice(
                            &mut self.pending_dzk.c[party],
                            &result.relations.c[party][start..end],
                        );
                    }
                    self.pending_dzk.lane_perms += plan.prf.len() as u64;
                    if self.pending_dzk.len_words()
                        >= RSS_DZK_FLUSH_PERMUTATIONS * RSS_RELATION_WORDS_PER_PERMUTATION
                    {
                        let ctr = self.next_ctr();
                        if let Err(error) = verify_rss_boolean_triples_bbcggi19(
                            &self.session_id,
                            ctr,
                            &mut self.pending_dzk,
                            &self.mask_session,
                            &mut self.party_rngs,
                        ) {
                            return self.poisoned.fail(error);
                        }
                    }
                }
            }
            for party in 0..3 {
                cut.push_party_slices(
                    party,
                    &result.prim[party][..8 * self.keys[0].key_len],
                    &result.sec[party][..8 * self.keys[0].key_len],
                );
            }
            result.relations.clear_and_wipe();
            self.chunk_scratch.push(result.relations);
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
    pub(super) fn flush_verify_and_open_cut(
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
    pub(super) fn eval_prf_batch64_secret(
        &mut self,
        pk_seed: &[u8],
        adrs_batch: &[Fips205Adrs],
    ) -> Result<RssCutShares, KeccakMpcError> {
        self.eval_prf_batch64_secret_impl(pk_seed, adrs_batch, false)
    }

    pub(super) fn eval_prf_batch64_secret_deferred(
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
        let (mut st_p, mut st_s) = rss_prf_states(&self.keys, pk_seed, adrs_batch);

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
    #[cfg(test)]
    pub(super) fn eval_f_step_masked_batch64(
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
        let n_bits = 8 * self.keys[0].key_len;
        let (mut st_p, mut st_s) =
            rss_f_states(self.keys[0].key_len, pk_seed, adrs_batch, cur_p, cur_s);

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
    pub(super) fn verify_and_open_cut_blocks(
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
    pub(super) fn prf_msg_shared(
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
    fn bind_key_params(
        &mut self,
        params: &Fips205Params,
        pk_seed: &[u8],
    ) -> Result<(), Fips205Error> {
        if self.is_poisoned() {
            return Err(Fips205Error::MpcActiveTamperDetected);
        }
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
        if n != self.keys[0].key_len
            || opt_rand.len() != n
            || self
                .keys
                .iter()
                .any(|k| k.tsw_binding.is_some() || k.scheme_identity.is_some())
        {
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
        let mut plans = Vec::new();
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
            plans.push(RssChunkPlan {
                prf: prf_batch,
                steps: vec![(leaf_batch, batch_active_mask(chunk_len))],
            });
            chunk_sizes.push(chunk_len);
            leaf_cursor += chunk_len;
        }

        self.evaluate_chunks(pk_seed, &plans, &mut cut)
            .map_err(rss_oracle_abort)?;

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

        let mut plans = Vec::new();
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
            let mut steps = Vec::with_capacity(15);
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
                steps.push((step_batch, mask));
            }
            plans.push(RssChunkPlan {
                prf: prf_batch,
                steps,
            });
            chunk_sizes.push(chunk_len);
            cursor += chunk_len;
        }

        self.evaluate_chunks(pk_seed, &plans, &mut cut)
            .map_err(rss_oracle_abort)?;

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

        let mut plans = Vec::new();
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
            let mut steps = Vec::with_capacity(15);
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
                steps.push((step_batch, exec_mask));
            }
            plans.push(RssChunkPlan {
                prf: prf_batch,
                steps,
            });
            chunk_sizes.push(chunk_len);
            cursor += chunk_len;
        }

        self.evaluate_chunks(pk_seed, &plans, &mut cut)
            .map_err(rss_oracle_abort)?;

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
