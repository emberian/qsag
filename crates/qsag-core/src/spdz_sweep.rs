//! `t`-of-`n` engine for the `Baggy` chain sweep: authenticated Shamir shares over
//! `GF(2^8)` with two-lane `Tower128` MACs, the dishonest-majority machinery of
//! [`crate::keccak_mpc::SpdzSlhMpcCluster`], driving the tweakable hashes of
//! [`crate::tsw_baggy`] instead of the FIPS 205 ones.
//!
//! [`SpdzSweepEngine`] implements [`BaggyEngine`], so [`crate::baggy::baggy_keygen_mpc`],
//! [`crate::baggy::baggy_sign_mpc`] and [`crate::baggy::WaistbandCache::precompute`] run on
//! it unchanged and produce the same public keys and signatures as the 2-of-3 engine and the
//! single-party reference: the threshold is the engine's, the scheme is not touched.
//!
//! * **Quorum.** The engine is built over the key shares of the parties that take part, `m`
//!   of them with `t <= m <= n`. Every opening reconstructs a degree-`< t` polynomial from
//!   all `m` shares and checks it against the MACs, so fewer than `t` parties learn nothing
//!   and any wrong share aborts.
//! * **Sweep.** Lanes are evaluated 64 at a time, one bitsliced `Keccak-f[1600]` per level:
//!   one `PRF` level and up to three `F` levels. Each permutation passes the batched
//!   `MacCheck` over all its Beaver openings before it returns, so by the time
//!   [`BaggyEngine::barrier`] is reached nothing is unverified.
//! * **Openings.** [`BaggyEngine::open_round`] opens exactly the picked `(lane, position)`
//!   values: the shares of every other lane of a batch are masked to zero before the
//!   committed opening.
//! * **Failure.** Any failed check poisons the engine and the vaults in use; it then
//!   evaluates and opens nothing.
//!
//! Triples come from a [`SpdzTripleSource`], one request per permutation
//! ([`TRIPLE_WORDS_PER_PERMUTATION`] words). A permutation's triples are about 243 MB per
//! party, which is why they are requested as they are used and not held for a whole sweep.
//! [`DealerlessPcgTripleSource`] produces them with the dealerless generator under the
//! session MAC key.

use alloc::vec;
use alloc::vec::Vec;

use crate::baggy::{
    BaggyEngine, BaggyError, TAG_BAGGY_OPT_RAND, TAG_BAGGY_R, keyed_mu_frame,
};
use crate::field::tower::{BitslicedGf256x64, Tower128, TowerGf256, bs_gf256_extract_lane};
use crate::keccak_mpc::{
    KeccakMpcError, SpdzAuthenticatedKeyShare, SpdzMacWord, TSW_F_SECRET_OFFSET,
    TSW_PRF_SECRET_OFFSET, TSW_SUITE_MIDSTATE, add_public_u64_to_spdz_word,
    eval_spdz_keccak_f1600_batch64, tsw_secret32_frame, verify_pending_spdz_mac_batch,
};
use crate::preprocessing::{
    OtMesh, PartyPrivateRng, PreprocessedKeccakPartyVault,
    commit_and_open_spdz_bs_gf256_batch_quorum, run_dealerless_pcg_keccak_vaults_with_alpha,
    validate_all_eval_points_gf256,
};
use crate::rss256::Rss256Error;
use crate::sponge::keccak::SHAKE256_RATE_BYTES;
use crate::tsw_baggy::{HashAdrs, TAG_PRF, TAG_TH_F};
use crate::wipe::{SecretVec, secret_vec_push, secret_vecs_with_capacity};
use crate::wots_c::LaneSpec;

/// Sponge instances per bitsliced permutation.
const BATCH: usize = 64;
/// Bit positions of one `Keccak-f[1600]` state.
const STATE_BITS: usize = 1600;
/// Bit positions of a 32-byte digest.
const DIGEST_BITS: usize = 256;
/// Triple words one 64-instance permutation consumes: 24 rounds of 1600 AND gates.
pub const TRIPLE_WORDS_PER_PERMUTATION: usize = 24 * STATE_BITS;

fn mpc(e: KeccakMpcError) -> BaggyError {
    BaggyError::Engine(Rss256Error::Mpc(e))
}

/// Supplier of authenticated `Keccak` triples for one quorum.
pub trait SpdzTripleSource {
    /// Fresh vaults, one per quorum member in quorum order, each holding at least `words`
    /// unused triple words under the MAC key the key shares are authenticated with. Every
    /// call returns triples that were never returned before.
    fn vaults(&mut self, words: usize)
    -> Result<Vec<PreprocessedKeccakPartyVault>, KeccakMpcError>;
}

/// [`SpdzTripleSource`] over the dealerless generator
/// ([`run_dealerless_pcg_keccak_vaults_with_alpha`]) under an existing MAC key. The
/// generator runs among all the parties that hold the MAC key (`eval_points`, with their
/// own preprocessing RNGs); the vaults of the signing quorum are handed to the engine and
/// the others are dropped, which wipes them.
pub struct DealerlessPcgTripleSource<'a> {
    pub session_id: [u8; 32],
    pub t: usize,
    pub eval_points: &'a [TowerGf256],
    /// The signing quorum, as strictly increasing indices into `eval_points`, in the order
    /// of the engine's key shares.
    pub quorum: &'a [usize],
    pub tree_depth: usize,
    pub alpha_contribs: &'a [[Tower128; 2]],
    pub alpha_shamir: &'a [[Tower128; 2]],
    pub ot_mesh: &'a mut OtMesh,
    pub party_rngs: &'a mut [PartyPrivateRng],
    /// Requests served so far; separates their sessions.
    pub requests: u64,
}

impl SpdzTripleSource for DealerlessPcgTripleSource<'_> {
    fn vaults(
        &mut self,
        words: usize,
    ) -> Result<Vec<PreprocessedKeccakPartyVault>, KeccakMpcError> {
        let mut session = self.session_id;
        for (byte, ctr) in session.iter_mut().zip(self.requests.to_le_bytes()) {
            *byte ^= ctr;
        }
        self.requests = self
            .requests
            .checked_add(1)
            .ok_or(KeccakMpcError::InvalidParameters)?;
        if self.quorum.windows(2).any(|w| w[0] >= w[1])
            || self.quorum.last().is_none_or(|&p| p >= self.eval_points.len())
        {
            return Err(KeccakMpcError::InvalidParameters);
        }
        let all = run_dealerless_pcg_keccak_vaults_with_alpha(
            session,
            self.t,
            self.eval_points,
            self.tree_depth,
            words,
            self.alpha_contribs,
            self.alpha_shamir,
            self.ot_mesh,
            self.party_rngs,
        )?;
        Ok(all
            .into_iter()
            .enumerate()
            .filter(|(p, _)| self.quorum.contains(p))
            .map(|(_, vault)| vault)
            .collect())
    }
}

/// Shares and MAC shares of the 256 bits of 64 digests: `sh[party][bit]`, bit `i` of every
/// plane belonging to instance `i`.
struct SharedDigests {
    sh: SecretVec<Vec<BitslicedGf256x64>>,
    mac: SecretVec<Vec<SpdzMacWord>>,
}

/// Writes the shared inputs of a permutation into its public initial states.
type Absorb<'f, 'e> =
    &'f mut dyn FnMut(&SpdzSweepEngine<'e>, &mut [Vec<BitslicedGf256x64>], &mut [Vec<SpdzMacWord>]);

/// Shared results of one [`SpdzSweepEngine`] sweep: per 64-lane batch, the lanes' values
/// after `0, 1, ..` applications of `F`.
pub struct SpdzSweep {
    lanes: Vec<LaneSpec>,
    pos: Vec<Vec<SharedDigests>>,
}

/// The `t`-of-`n` [`BaggyEngine`]. See the module documentation.
pub struct SpdzSweepEngine<'a> {
    session_id: [u8; 32],
    t: usize,
    quorum_pts: Vec<TowerGf256>,
    keys: &'a [SpdzAuthenticatedKeyShare],
    party_rngs: &'a mut [PartyPrivateRng],
    triples: &'a mut dyn SpdzTripleSource,
    /// MAC key shares of the quorum, as the most recent vaults carried them.
    alpha: Option<SecretVec<[Tower128; 2]>>,
    perm_ctr: usize,
    poisoned: bool,
}

impl<'a> SpdzSweepEngine<'a> {
    /// Engine over the quorum holding `keys` (`t <= keys.len()`), all shares of one 32-byte
    /// key pair under one `pk_seed`.
    pub fn new(
        session_id: [u8; 32],
        t: usize,
        keys: &'a [SpdzAuthenticatedKeyShare],
        party_rngs: &'a mut [PartyPrivateRng],
        triples: &'a mut dyn SpdzTripleSource,
    ) -> Result<Self, KeccakMpcError> {
        let m = keys.len();
        if t < 2 || m < t || party_rngs.len() != m {
            return Err(KeccakMpcError::InvalidParameters);
        }
        let quorum_pts: Vec<TowerGf256> = keys.iter().map(|k| k.eval_point).collect();
        validate_all_eval_points_gf256(&quorum_pts)?;
        let identity0 = keys[0].scheme_identity()?;
        for key in keys {
            if key.key_len != 32 || key.pk_seed != keys[0].pk_seed {
                return Err(KeccakMpcError::InvalidParameters);
            }
            if key.scheme_identity()? != identity0 {
                return Err(KeccakMpcError::KeyBindingMismatch);
            }
        }
        Ok(Self {
            session_id,
            t,
            quorum_pts,
            keys,
            party_rngs,
            triples,
            alpha: None,
            perm_ctr: 0,
            poisoned: false,
        })
    }

    /// Threshold `t` and quorum size `m`.
    pub fn threshold_and_quorum(&self) -> (usize, usize) {
        (self.t, self.quorum_pts.len())
    }

    /// Permutations evaluated so far.
    pub fn permutations(&self) -> usize {
        self.perm_ctr
    }

    pub fn is_poisoned(&self) -> bool {
        self.poisoned
    }

    fn live(&self) -> Result<(), BaggyError> {
        if self.poisoned {
            return Err(mpc(KeccakMpcError::Poisoned));
        }
        Ok(())
    }

    fn fail<T>(&mut self, e: KeccakMpcError) -> Result<T, BaggyError> {
        self.poisoned = true;
        Err(mpc(e))
    }

    /// Shares of the public initial states `midstate ^ frame` of up to 64 instances.
    fn public_states(
        &self,
        alpha: &[[Tower128; 2]],
        frames: &[[u8; SHAKE256_RATE_BYTES]],
    ) -> (SecretVec<Vec<BitslicedGf256x64>>, SecretVec<Vec<SpdzMacWord>>) {
        let m = self.quorum_pts.len();
        let mut sh = SecretVec::new(vec![vec![[0u64; 8]; STATE_BITS]; m]);
        let mut mac = SecretVec::new(vec![vec![[[Tower128::ZERO; 64]; 2]; STATE_BITS]; m]);
        for pos in 0..STATE_BITS {
            let mid_bit = (TSW_SUITE_MIDSTATE[pos / 64] >> (pos % 64)) & 1;
            let mut word = 0u64;
            for (i, frame) in frames.iter().enumerate() {
                let frame_bit = if pos < 8 * SHAKE256_RATE_BYTES {
                    u64::from((frame[pos / 8] >> (pos % 8)) & 1)
                } else {
                    0
                };
                word |= (mid_bit ^ frame_bit) << i;
            }
            if word != 0 {
                for p in 0..m {
                    add_public_u64_to_spdz_word(word, &mut sh[p][pos], &mut mac[p][pos], &alpha[p]);
                }
            }
        }
        (sh, mac)
    }

    /// One 64-instance permutation on fresh triples, followed by the batched `MacCheck` of
    /// every Beaver opening it made. Returns the output digests, still shared.
    fn permute(
        &mut self,
        frames: &[[u8; SHAKE256_RATE_BYTES]],
        absorb: Absorb<'_, 'a>,
    ) -> Result<SharedDigests, BaggyError> {
        self.live()?;
        let m = self.quorum_pts.len();
        let mut vaults = match self.triples.vaults(TRIPLE_WORDS_PER_PERMUTATION) {
            Ok(v) => v,
            Err(e) => return self.fail(e),
        };
        if vaults.len() != m
            || vaults.iter().zip(&self.quorum_pts).any(|(v, pt)| {
                v.poisoned
                    || v.eval_point != *pt
                    || v.remaining() < TRIPLE_WORDS_PER_PERMUTATION
            })
        {
            return self.fail(KeccakMpcError::InvalidParameters);
        }
        let alpha = SecretVec::new(
            vaults
                .iter()
                .map(|v| v.mac_alpha_lanes)
                .collect::<Vec<[Tower128; 2]>>(),
        );
        // Any degree-`< t` sharing of the session MAC key checks any MAC under that key, so
        // a source may re-share it between requests. Shares of another key fail the checks.
        self.alpha = Some(SecretVec::new(alpha.to_vec()));
        let (mut sh, mut mac) = self.public_states(&alpha, frames);
        absorb(self, &mut sh, &mut mac);

        let mut pending_opened = Vec::new();
        let mut pending_macs = SecretVec::new(vec![Vec::new(); m]);
        let ctr = self.perm_ctr;
        self.perm_ctr += 1;
        let evaluated = eval_spdz_keccak_f1600_batch64(
            &self.session_id,
            ctr,
            self.t,
            &self.quorum_pts,
            &mut sh,
            &mut mac,
            &mut vaults,
            &mut pending_opened,
            &mut pending_macs,
            self.party_rngs,
        )
        .and_then(|()| {
            Ok(verify_pending_spdz_mac_batch(
                &self.session_id,
                "baggy_spdz_chi",
                self.t,
                &self.quorum_pts,
                &pending_opened,
                &pending_macs,
                &alpha,
                self.party_rngs,
            )?)
        });
        if let Err(e) = evaluated {
            for v in &mut vaults {
                v.poison_and_wipe();
            }
            return self.fail(e);
        }
        for party in sh.iter_mut() {
            party.truncate(DIGEST_BITS);
        }
        for party in mac.iter_mut() {
            party.truncate(DIGEST_BITS);
        }
        // `truncate` leaves the capacity states behind; they are wiped with the vectors.
        Ok(SharedDigests { sh, mac })
    }

    /// XOR the shared 32-byte key `words` into the secret slot at byte `offset` of the
    /// first `active` instances.
    fn absorb_key(
        &self,
        words: impl Fn(&SpdzAuthenticatedKeyShare) -> (&[BitslicedGf256x64; 4], &[SpdzMacWord; 4]),
        offset: usize,
        active: usize,
        sh: &mut [Vec<BitslicedGf256x64>],
        mac: &mut [Vec<SpdzMacWord>],
    ) {
        let active_mask = if active >= BATCH {
            u64::MAX
        } else {
            (1u64 << active) - 1
        };
        for (p, key) in self.keys.iter().enumerate() {
            let (key_sh, key_mac) = words(key);
            for bit in 0..DIGEST_BITS {
                let (w, b) = (bit / 64, bit % 64);
                let elem = bs_gf256_extract_lane(&key_sh[w], b);
                let pos = 8 * offset + bit;
                for (pl, plane) in sh[p][pos].iter_mut().enumerate() {
                    *plane ^= 0u64.wrapping_sub(u64::from((elem.0 >> pl) & 1)) & active_mask;
                }
                for l in 0..2 {
                    for slot in mac[p][pos][l][..active].iter_mut() {
                        slot.0 ^= key_mac[w][l][b].0;
                    }
                }
            }
        }
    }

    /// XOR shared digests into the secret slot at byte `offset` of every instance.
    fn absorb_digests(
        value: &SharedDigests,
        offset: usize,
        sh: &mut [Vec<BitslicedGf256x64>],
        mac: &mut [Vec<SpdzMacWord>],
    ) {
        let slot = 8 * offset..8 * offset + DIGEST_BITS;
        for (state, digest) in sh.iter_mut().zip(value.sh.iter()) {
            for (word, add) in state[slot.clone()].iter_mut().zip(digest) {
                for (plane, a) in word.iter_mut().zip(add) {
                    *plane ^= a;
                }
            }
        }
        for (state, digest) in mac.iter_mut().zip(value.mac.iter()) {
            for (tags, add) in state[slot.clone()].iter_mut().zip(digest) {
                for (lane, a) in tags.iter_mut().zip(add) {
                    for (tag, x) in lane.iter_mut().zip(a) {
                        tag.0 ^= x.0;
                    }
                }
            }
        }
    }

    /// Committed opening and `MacCheck` of the selected instances of each `(digests, mask)`
    /// group, in one round. Returns, per group, the 64 digests (zero where not selected).
    fn open_masked(
        &mut self,
        groups: &[(&SharedDigests, u64)],
    ) -> Result<Vec<Vec<[u8; 32]>>, BaggyError> {
        self.live()?;
        let Some(alpha) = self.alpha.as_ref().map(|a| SecretVec::new(a.to_vec())) else {
            // Nothing was ever evaluated, so there is nothing to open.
            return self.fail(KeccakMpcError::InvalidParameters);
        };
        let m = self.quorum_pts.len();
        let cut_words = groups.len() * DIGEST_BITS;
        let mut cut_sh = secret_vecs_with_capacity(m, cut_words);
        let mut cut_mac = secret_vecs_with_capacity(m, cut_words);
        for &(value, mask) in groups {
            for p in 0..m {
                for bit in 0..DIGEST_BITS {
                    let mut word = value.sh[p][bit];
                    for plane in &mut word {
                        *plane &= mask;
                    }
                    let mut tags = value.mac[p][bit];
                    for lane in &mut tags {
                        for (i, tag) in lane.iter_mut().enumerate() {
                            if (mask >> i) & 1 == 0 {
                                *tag = Tower128::ZERO;
                            }
                        }
                    }
                    secret_vec_push(&mut cut_sh[p], word);
                    secret_vec_push(&mut cut_mac[p], tags);
                }
            }
        }
        debug_assert!(
            cut_sh.iter().all(|v| v.capacity() == cut_words)
                && cut_mac.iter().all(|v| v.capacity() == cut_words)
        );
        let opened = match commit_and_open_spdz_bs_gf256_batch_quorum(
            &self.session_id,
            "baggy_spdz_open",
            self.t,
            &self.quorum_pts,
            &cut_sh,
            &cut_mac,
            &alpha,
            self.party_rngs,
        ) {
            Ok(words) => words,
            Err(e) => return self.fail(e.into()),
        };
        // Every opened value is a bit: planes 1..8 are zero.
        if opened.len() != groups.len() * DIGEST_BITS || opened.iter().any(|w| w[1..] != [0u64; 7])
        {
            return self.fail(KeccakMpcError::SpdzMacAbort);
        }
        Ok(opened
            .as_chunks::<DIGEST_BITS>()
            .0
            .iter()
            .map(|words| {
                (0..BATCH)
                    .map(|i| {
                        let mut out = [0u8; 32];
                        for (bit, word) in words.iter().enumerate() {
                            out[bit / 8] |= (((word[0] >> i) & 1) as u8) << (bit % 8);
                        }
                        out
                    })
                    .collect()
            })
            .collect())
    }
}

impl BaggyEngine for SpdzSweepEngine<'_> {
    type Sweep = SpdzSweep;

    fn pk_seed(&self) -> [u8; 32] {
        self.keys[0].pk_seed
    }

    fn session_id(&self) -> &[u8; 32] {
        &self.session_id
    }

    fn key_identity(&self) -> Result<Option<[u8; 32]>, BaggyError> {
        let first = self.keys[0].scheme_identity().map_err(mpc)?;
        for key in self.keys {
            if key.scheme_identity().map_err(mpc)? != first {
                return Err(mpc(KeccakMpcError::KeyBindingMismatch));
            }
        }
        Ok(first)
    }

    fn bind_key_identity(&mut self, identity: &[u8; 32]) -> Result<(), BaggyError> {
        self.live()?;
        // Check all shares before writing any, so a refusal changes none of them.
        for key in self.keys {
            if key
                .scheme_identity()
                .map_err(mpc)?
                .is_some_and(|bound| bound != *identity)
            {
                return Err(mpc(KeccakMpcError::KeyBindingMismatch));
            }
        }
        for key in self.keys {
            key.bind_scheme_identity(identity).map_err(mpc)?;
        }
        Ok(())
    }

    fn randomiser(&mut self, mu: &[u8; 32]) -> Result<[u8; 32], BaggyError> {
        let (frame, off) = keyed_mu_frame(TAG_BAGGY_OPT_RAND, mu);
        let opt_rand = self.permute(&[frame], &mut |engine, sh, mac| {
            engine.absorb_key(|k| (&k.sk_prf_words, &k.sk_prf_macs), off, 1, sh, mac);
        })?;
        let (frame, off) = keyed_mu_frame(TAG_BAGGY_R, mu);
        let r = self.permute(&[frame], &mut |_, sh, mac| {
            Self::absorb_digests(&opt_rand, off, sh, mac);
        })?;
        Ok(self.open_masked(&[(&r, 1)])?[0][0])
    }

    fn sweep(
        &mut self,
        pk_seed: &[u8; 32],
        lanes: Vec<LaneSpec>,
    ) -> Result<SpdzSweep, BaggyError> {
        self.live()?;
        if lanes.is_empty()
            || lanes.windows(2).any(|w| w[0].steps < w[1].steps)
            || *pk_seed != self.keys[0].pk_seed
        {
            return Err(BaggyError::Engine(Rss256Error::InvalidParameters));
        }
        let mut pos: Vec<Vec<SharedDigests>> = Vec::with_capacity(lanes.len().div_ceil(BATCH));
        for chunk in lanes.chunks(BATCH) {
            let frames: Vec<[u8; SHAKE256_RATE_BYTES]> = chunk
                .iter()
                .map(|l| tsw_secret32_frame(TAG_PRF, pk_seed, &l.prf))
                .collect();
            let secrets = self.permute(&frames, &mut |engine, sh, mac| {
                engine.absorb_key(
                    |k| (&k.sk_seed_words, &k.sk_seed_macs),
                    TSW_PRF_SECRET_OFFSET,
                    chunk.len(),
                    sh,
                    mac,
                );
            })?;
            let mut wave = vec![secrets];
            for step in 0..chunk[0].steps {
                let running = chunk.iter().take_while(|l| l.steps > step).count();
                let frames: Vec<[u8; SHAKE256_RATE_BYTES]> = chunk[..running]
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
                let prev = &wave[usize::from(step)];
                let next = self.permute(&frames, &mut |_, sh, mac| {
                    Self::absorb_digests(prev, TSW_F_SECRET_OFFSET, sh, mac);
                })?;
                wave.push(next);
            }
            pos.push(wave);
        }
        Ok(SpdzSweep { lanes, pos })
    }

    fn barrier(&mut self) -> Result<(), BaggyError> {
        // Every permutation was verified before it returned.
        self.live()
    }

    fn open_round(
        &mut self,
        sweep: &SpdzSweep,
        picks: &[(usize, u8)],
    ) -> Result<Vec<[u8; 32]>, BaggyError> {
        self.live()?;
        // Group by (batch, position): one masked opening each, all in the same round.
        let mut groups: Vec<(usize, u8, u64, Vec<usize>)> = Vec::new();
        for (i, &(lane, position)) in picks.iter().enumerate() {
            if lane >= sweep.lanes.len() || position > sweep.lanes[lane].steps {
                return Err(BaggyError::Engine(Rss256Error::InvalidParameters));
            }
            let wave = lane / BATCH;
            let slot = match groups.iter().position(|g| g.0 == wave && g.1 == position) {
                Some(idx) => idx,
                None => {
                    groups.push((wave, position, 0, Vec::new()));
                    groups.len() - 1
                }
            };
            groups[slot].2 |= 1u64 << (lane % BATCH);
            groups[slot].3.push(i);
        }
        if groups.is_empty() {
            return Ok(Vec::new());
        }
        let cuts: Vec<(&SharedDigests, u64)> = groups
            .iter()
            .map(|g| (&sweep.pos[g.0][usize::from(g.1)], g.2))
            .collect();
        let opened = self.open_masked(&cuts)?;
        let mut out = vec![[0u8; 32]; picks.len()];
        for (group, digests) in groups.iter().zip(&opened) {
            for &i in &group.3 {
                out[i] = digests[picks[i].0 % BATCH];
            }
        }
        Ok(out)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::baggy::{
        BaggyFewTime, BaggyKeyBinding, BaggyParams, MemoryFirstSigned, WaistbandCache,
        baggy_keygen_mpc, baggy_reference_keygen, baggy_reference_sign, baggy_sign_mpc,
        baggy_verify,
    };
    use crate::pors_fp::PorsFpParams;
    use crate::keccak_mpc::tests::SpdzTestDealer;
    use crate::tsw_baggy::PqSecretKey;

    /// Test-only source: a trusted dealer under one MAC key. It stands in for dealerless
    /// preprocessing so these tests exercise the online protocol. The dealer shares at the
    /// quorum's evaluation points only; the polynomials have degree `< t` either way.
    pub(crate) struct DealerSource {
        pub(crate) dealer: SpdzTestDealer,
        pub(crate) requests: usize,
        /// Flip one bit of one triple of this request (counted from zero).
        pub(crate) corrupt_request: Option<usize>,
    }

    impl SpdzTripleSource for DealerSource {
        fn vaults(
            &mut self,
            words: usize,
        ) -> Result<Vec<PreprocessedKeccakPartyVault>, KeccakMpcError> {
            let mut vaults = self.dealer.vaults(words);
            if self.corrupt_request == Some(self.requests) {
                vaults[0].triples[words / 2].c[0] ^= 1 << 7;
            }
            self.requests += 1;
            Ok(vaults)
        }
    }

    pub(crate) fn sk() -> PqSecretKey {
        PqSecretKey {
            sk_seed: core::array::from_fn(|i| (i as u8).wrapping_mul(13) ^ 0x51),
            sk_prf: core::array::from_fn(|i| (i as u8).wrapping_mul(7) ^ 0xa4),
            pk_seed: [0x3c; 32],
        }
    }

    pub(crate) struct Setup {
        pub(crate) keys: Vec<SpdzAuthenticatedKeyShare>,
        pub(crate) rngs: Vec<PartyPrivateRng>,
        pub(crate) source: DealerSource,
    }

    /// `t`-of-`n` shares of [`sk`] for the quorum `quorum` (party indices in `0..n`; party
    /// `p` evaluates at `p + 1`).
    pub(crate) fn setup(t: usize, n: usize, quorum: &[usize], tag: u8) -> Setup {
        assert!(quorum.iter().all(|&p| p < n));
        let pts: Vec<TowerGf256> = quorum.iter().map(|&p| TowerGf256(p as u8 + 1)).collect();
        let mut dealer = SpdzTestDealer::new(&[tag, t as u8, n as u8], t, &pts);
        let sk = sk();
        let keys = dealer.key_shares(32, sk.pk_seed, &sk.sk_seed, &sk.sk_prf);
        let rngs = quorum
            .iter()
            .map(|&p| PartyPrivateRng::from_seed([tag ^ p as u8; 32], b"spdz-sweep-test"))
            .collect();
        Setup {
            keys,
            rngs,
            source: DealerSource {
                dealer,
                requests: 0,
                corrupt_request: None,
            },
        }
    }

    #[test]
    fn sweep_openings_match_the_reference_and_reveal_only_the_picks() {
        // 3-of-5 with the non-prefix quorum {1, 2, 4}.
        let mut s = setup(3, 5, &[1, 2, 4], 0x11);
        let sk = sk();
        let mut engine =
            SpdzSweepEngine::new([0x21; 32], 3, &s.keys, &mut s.rngs, &mut s.source).unwrap();
        // 70 lanes: two batches, WOTS chains then few-time leaves.
        let mut lanes: Vec<LaneSpec> = (0..66).map(|c| LaneSpec::wots(1, 5, 2, c)).collect();
        lanes.extend((0..2).map(|leaf| LaneSpec::fors(5, 2, 1, leaf)));
        lanes.extend((0..2).map(|leaf| LaneSpec::pors(5, 2, leaf)));
        let sweep = engine.sweep(&sk.pk_seed, lanes.clone()).unwrap();
        // Batch 0 runs PRF + 3 steps; batch 1 holds 2 chains and 4 one-step lanes.
        assert_eq!(engine.permutations(), 8);
        engine.barrier().unwrap();

        let reference = |lane: &LaneSpec, position: u8| {
            let mut v = crate::tsw_baggy::th_secret_prf(
                crate::tsw_baggy::Cshake256Suite,
                &sk.pk_seed,
                &sk.sk_seed,
                &lane.prf,
            );
            for step in 0..position {
                let adrs = if lane.step_indexed {
                    HashAdrs {
                        hash_step: u32::from(step),
                        ..lane.f
                    }
                } else {
                    lane.f
                };
                v = crate::tsw_baggy::th_chain_f(
                    crate::tsw_baggy::Cshake256Suite,
                    &sk.pk_seed,
                    &adrs,
                    &v,
                );
            }
            v
        };
        let picks: Vec<(usize, u8)> = vec![
            (0, 3),
            (0, 0),
            (17, 2),
            (63, 1),
            (64, 3),
            (65, 0),
            (66, 1),
            (67, 0),
            (68, 1),
            (69, 0),
        ];
        let opened = engine.open_round(&sweep, &picks).unwrap();
        for (&(lane, position), value) in picks.iter().zip(&opened) {
            assert_eq!(*value, reference(&lanes[lane], position), "lane {lane}");
        }
        // Positions a lane does not have, and lanes that do not exist, are refused.
        for bad in [(66usize, 2u8), (0, 4), (70, 0)] {
            assert!(engine.open_round(&sweep, &[bad]).is_err());
        }
        assert!(!engine.is_poisoned());
    }

    /// One layer of two leaves over a 16-leaf `PORS+FP` tree: a signature costs 20
    /// permutations (18 for the sweep, 2 for the randomiser), each several seconds here.
    const TINY_V2: BaggyParams = BaggyParams {
        subtree_height: 1,
        num_layers: 1,
        few_time: BaggyFewTime::PorsFp(PorsFpParams {
            tree_height: 4,
            reveal: 4,
            max_auth_nodes: 7,
        }),
        ..BaggyParams::TEST_SMALL_V2
    };

    /// The same hypertree over two `FORS+C` trees of four leaves (one of them signed).
    const TINY_V1: BaggyParams = BaggyParams {
        subtree_height: 1,
        num_layers: 1,
        fors_trees: 2,
        fors_height: 2,
        ..BaggyParams::TEST_SMALL
    };

    /// Sign under MPC with the quorum `quorum` of a `t`-of-`n` sharing and compare with the
    /// single-party reference. The public key is the reference one and the shares are
    /// bound to it directly; [`keygen_two_of_three_equals_the_reference`] covers key
    /// generation.
    fn sign_and_compare(params: &BaggyParams, t: usize, n: usize, quorum: &[usize], tag: u8) {
        let mut s = setup(t, n, quorum, tag);
        let sk = sk();
        let pk = baggy_reference_keygen(params, &sk).unwrap();
        let binding = BaggyKeyBinding::new(params, &pk);
        let mut engine =
            SpdzSweepEngine::new([tag; 32], t, &s.keys, &mut s.rngs, &mut s.source).unwrap();
        let sign = |engine: &mut SpdzSweepEngine<'_>, msg: &[u8]| {
            baggy_sign_mpc(
                engine,
                params,
                &pk,
                &binding,
                &mut WaistbandCache::disabled(),
                &mut MemoryFirstSigned::new(),
                msg,
            )
        };
        // Unbound shares sign nothing, and nothing is evaluated for them.
        assert_eq!(
            sign(&mut engine, b"unbound"),
            Err(BaggyError::KeyBindingMismatch)
        );
        assert_eq!(engine.permutations(), 0);
        engine.bind_key_identity(&binding.identity()).unwrap();
        let msg = b"threshold root certificate";
        let sig = sign(&mut engine, msg).unwrap();
        assert_eq!(engine.permutations(), 20);
        assert_eq!(engine.threshold_and_quorum(), (t, quorum.len()));
        assert!(baggy_verify(params, &pk, msg, &sig));
        assert_eq!(Some(sig), baggy_reference_sign(params, &sk, &pk, msg));
    }

    #[test]
    fn baggy_v2_two_of_three_equals_the_reference() {
        sign_and_compare(&TINY_V2, 2, 3, &[0, 2], 0x31);
    }

    #[test]
    fn baggy_v2_three_of_five_equals_the_reference() {
        sign_and_compare(&TINY_V2, 3, 5, &[0, 3, 4], 0x32);
    }

    #[test]
    fn baggy_v2_five_of_seven_equals_the_reference() {
        sign_and_compare(&TINY_V2, 5, 7, &[0, 1, 3, 5, 6], 0x33);
    }

    #[test]
    fn baggy_v2_all_of_three_equals_the_reference() {
        sign_and_compare(&TINY_V2, 3, 3, &[0, 1, 2], 0x34);
    }

    #[test]
    fn baggy_v1_three_of_five_with_a_spare_party_equals_the_reference() {
        // Four parties of a 3-of-5 sharing: more than the threshold take part.
        sign_and_compare(&TINY_V1, 3, 5, &[1, 2, 3, 4], 0x35);
    }

    #[test]
    fn keygen_two_of_three_equals_the_reference() {
        let mut s = setup(2, 3, &[1, 2], 0x36);
        let sk = sk();
        let mut engine =
            SpdzSweepEngine::new([0x36; 32], 2, &s.keys, &mut s.rngs, &mut s.source).unwrap();
        let (pk, binding) =
            baggy_keygen_mpc(&mut engine, &TINY_V2, &mut WaistbandCache::disabled()).unwrap();
        assert_eq!(Some(pk), baggy_reference_keygen(&TINY_V2, &sk));
        assert_eq!(engine.key_identity().unwrap(), Some(binding.identity()));
        // The shares now belong to this key under these parameters only.
        assert!(
            baggy_keygen_mpc(&mut engine, &TINY_V1, &mut WaistbandCache::disabled()).is_err()
        );
    }

    /// No dealer anywhere: dealerless key generation, MAC key, key-share authentication and
    /// triples for a 3-of-4 sharing, then a sweep by the quorum `{0, 2, 3}` checked against
    /// the hash of the key reconstructed from the same shares.
    #[test]
    fn dealerless_keys_and_triples_drive_a_three_of_four_sweep() {
        use crate::dkg::run_dealerless_dkg_seed32_gf256;
        use crate::field::tower::lagrange_weights_zero_gf256;
        use crate::keccak_mpc::authenticate_dkg_seed_shares_for_spdz;
        use crate::preprocessing::{PCG_DEFAULT_TREE_DEPTH, spdz_setup_alpha_gf256};
        use crate::tsw_baggy::{Cshake256Suite, th_chain_f, th_secret_prf};

        let (t, n) = (3usize, 4usize);
        let pts: Vec<TowerGf256> = (1..=n as u8).map(TowerGf256).collect();
        let mut rngs: Vec<PartyPrivateRng> = (0..n)
            .map(|i| PartyPrivateRng::from_seed([0x50 + i as u8; 32], b"spdz-sweep-dealerless"))
            .collect();
        let mut mesh = OtMesh::try_establish([0xc0; 32], &mut rngs).unwrap();
        let (seed_shares, pk_seed) =
            run_dealerless_dkg_seed32_gf256([0xc1; 32], t, &pts, &mut mesh, &mut rngs).unwrap();
        let (prf_shares, _) =
            run_dealerless_dkg_seed32_gf256([0xc2; 32], t, &pts, &mut mesh, &mut rngs).unwrap();
        let (alpha_c, alpha_sh) = spdz_setup_alpha_gf256(&[0xc3; 32], t, &pts, &mut rngs).unwrap();
        let mut keys = authenticate_dkg_seed_shares_for_spdz(
            &[0xc4; 32],
            t,
            &pts,
            32,
            pk_seed,
            &seed_shares,
            &prf_shares,
            &alpha_c,
            &alpha_sh,
            &mut mesh,
            &mut rngs,
        )
        .unwrap();

        let quorum = [0usize, 2, 3];
        let weights = lagrange_weights_zero_gf256(&[pts[0], pts[2], pts[3]]).unwrap();
        let mut sk_seed = [0u8; 32];
        for bit in 0..256 {
            let mut value = TowerGf256::ZERO;
            for (weight, &p) in weights.iter().zip(&quorum) {
                value = value.add(weight.mul(seed_shares[p].bit_shares[bit]));
            }
            assert!(value.0 <= 1);
            sk_seed[bit / 8] |= value.0 << (bit % 8);
        }

        keys.remove(1);
        let mut session_rngs: Vec<PartyPrivateRng> = quorum
            .iter()
            .map(|&p| PartyPrivateRng::from_seed([0x60 + p as u8; 32], b"spdz-sweep-session"))
            .collect();
        let mut source = DealerlessPcgTripleSource {
            session_id: [0xc5; 32],
            t,
            eval_points: &pts,
            quorum: &quorum,
            tree_depth: PCG_DEFAULT_TREE_DEPTH,
            alpha_contribs: &alpha_c,
            alpha_shamir: &alpha_sh,
            ot_mesh: &mut mesh,
            party_rngs: &mut rngs,
            requests: 0,
        };
        let mut engine =
            SpdzSweepEngine::new([0xc6; 32], t, &keys, &mut session_rngs, &mut source).unwrap();
        let lane = LaneSpec::pors(9, 1, 5);
        let sweep = engine.sweep(&pk_seed, vec![lane]).unwrap();
        engine.barrier().unwrap();
        let opened = engine.open_round(&sweep, &[(0, 1)]).unwrap();
        let secret = th_secret_prf(Cshake256Suite, &pk_seed, &sk_seed, &lane.prf);
        assert_eq!(
            opened[0],
            th_chain_f(Cshake256Suite, &pk_seed, &lane.f, &secret)
        );
        assert_eq!(engine.permutations(), 2);
    }

    #[test]
    fn below_threshold_wrong_shares_and_bad_triples_are_refused() {
        let sk = sk();
        // Fewer parties than the threshold cannot form an engine.
        let mut s = setup(3, 5, &[0, 1], 0x41);
        assert!(matches!(
            SpdzSweepEngine::new([0x41; 32], 3, &s.keys, &mut s.rngs, &mut s.source),
            Err(KeccakMpcError::InvalidParameters)
        ));

        // A changed key share enters the first permutation's Beaver openings and fails
        // their batched MAC check: no digest exists to open, and the engine stays dead.
        let mut s = setup(3, 5, &[0, 1, 2], 0x42);
        s.keys[1].sk_seed_words[0][0] ^= 1;
        let mut engine =
            SpdzSweepEngine::new([0x42; 32], 3, &s.keys, &mut s.rngs, &mut s.source).unwrap();
        assert!(engine.sweep(&sk.pk_seed, vec![LaneSpec::pors(0, 0, 0)]).is_err());
        assert!(engine.is_poisoned());
        assert_eq!(engine.permutations(), 1);
        assert!(engine.sweep(&sk.pk_seed, vec![LaneSpec::pors(0, 0, 1)]).is_err());
        assert!(engine.randomiser(&[0; 32]).is_err());
        assert!(engine.barrier().is_err());
        assert_eq!(engine.permutations(), 1);

        // A corrupted triple fails the batched check of its own permutation.
        let mut s = setup(2, 3, &[0, 1], 0x43);
        s.source.corrupt_request = Some(1);
        let mut engine =
            SpdzSweepEngine::new([0x43; 32], 2, &s.keys, &mut s.rngs, &mut s.source).unwrap();
        assert!(engine.sweep(&sk.pk_seed, vec![LaneSpec::pors(0, 0, 0)]).is_err());
        assert!(engine.is_poisoned());
        assert_eq!(engine.permutations(), 2);

        // Shares bound to one scheme identity refuse another, and refuse to sign unbound.
        let mut s = setup(2, 3, &[1, 2], 0x44);
        let mut engine =
            SpdzSweepEngine::new([0x44; 32], 2, &s.keys, &mut s.rngs, &mut s.source).unwrap();
        assert_eq!(engine.key_identity().unwrap(), None);
        engine.bind_key_identity(&[7; 32]).unwrap();
        engine.bind_key_identity(&[7; 32]).unwrap();
        assert!(engine.bind_key_identity(&[8; 32]).is_err());
        assert_eq!(engine.key_identity().unwrap(), Some([7; 32]));
    }
}
