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
//!   one `PRF` level and up to three `F` levels. Beaver MAC checks are queued until
//!   [`BaggyEngine::barrier`] or an output opening, with an automatic flush after
//!   two full waves to bound retained tag memory. No output bypasses the check.
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

use crate::baggy::{BaggyEngine, BaggyError, TAG_BAGGY_OPT_RAND, TAG_BAGGY_R, keyed_mu_frame};
use crate::field::tower::{
    BitslicedGf256x64, Tower128, TowerGf256, bs_gf256_extract_lane, bs_gf256_insert_lane,
};
use crate::keccak_mpc::{
    KeccakMpcError, SpdzAuthenticatedKeyShare, SpdzMacWord, TSW_F_SECRET_OFFSET,
    TSW_PRF_SECRET_OFFSET, TSW_SUITE_MIDSTATE, add_public_u64_to_spdz_word,
    eval_spdz_keccak_f1600_batch64, eval_spdz_keccak_f1600_single, tsw_secret32_frame,
    verify_pending_spdz_mac_batch_with_mesh,
};
use crate::preprocessing::{
    KeccakBitTripleShare64, OtMesh, PartyPrivateRng, PreprocessedKeccakPartyVault,
    commit_and_open_spdz_bs_gf256_batch_quorum_with_mesh,
    run_dealerless_pcg_keccak_vaults_with_alpha, validate_all_eval_points_gf256,
};
use crate::rss256::Rss256Error;
use crate::sponge::keccak::SHAKE256_RATE_BYTES;
use crate::tsw_baggy::{HashAdrs, TAG_PRF, TAG_TH_F};
use crate::wipe::{
    SecretVec, SecretWipe, secret_vec_push, secret_vec_reserve, secret_vecs_with_capacity,
};
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
/// the others are dropped, which wipes them. Any failed request permanently poisons this
/// source and wipes the caller's borrowed MAC-key buffers.
pub struct DealerlessPcgTripleSource<'a> {
    pub session_id: [u8; 32],
    pub t: usize,
    pub eval_points: &'a [TowerGf256],
    /// The signing quorum, as strictly increasing indices into `eval_points`, in the order
    /// of the engine's key shares.
    pub quorum: &'a [usize],
    pub tree_depth: usize,
    /// Borrowed mutably so failure can wipe the caller's contribution buffers.
    pub alpha_contribs: &'a mut [[Tower128; 2]],
    /// Matching Shamir MAC-key shares, also wiped on failure.
    pub alpha_shamir: &'a mut [[Tower128; 2]],
    pub ot_mesh: &'a mut OtMesh,
    pub party_rngs: &'a mut [PartyPrivateRng],
    /// Requests served so far; separates their sessions. `u64::MAX` is terminal:
    /// a failed request wipes both borrowed MAC-key buffers and poisons this source.
    pub requests: u64,
}

impl SpdzTripleSource for DealerlessPcgTripleSource<'_> {
    fn vaults(
        &mut self,
        words: usize,
    ) -> Result<Vec<PreprocessedKeccakPartyVault>, KeccakMpcError> {
        if self.requests == u64::MAX {
            return Err(KeccakMpcError::Poisoned);
        }
        let result = self.try_vaults(words);
        if result.is_err() {
            self.requests = u64::MAX;
            for key in self
                .alpha_contribs
                .iter_mut()
                .chain(self.alpha_shamir.iter_mut())
            {
                crate::field::tower::wipe_tower128(key);
            }
        }
        result
    }
}

impl DealerlessPcgTripleSource<'_> {
    fn try_vaults(
        &mut self,
        words: usize,
    ) -> Result<Vec<PreprocessedKeccakPartyVault>, KeccakMpcError> {
        let req_bytes = self.requests.to_le_bytes();
        let session = crate::sponge::keccak::cshake256_32_multi_frame(
            b"QSAG.SPDZ_SWEEP.PCG_REQ.V1",
            &[&self.session_id, &req_bytes],
        );
        self.requests = self
            .requests
            .checked_add(1)
            .ok_or(KeccakMpcError::InvalidParameters)?;
        if self.quorum.windows(2).any(|w| w[0] >= w[1])
            || self
                .quorum
                .last()
                .is_none_or(|&p| p >= self.eval_points.len())
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

/// [`SpdzTripleSource`] over vaults generated ahead of signing, so that a permutation costs its
/// evaluation and MAC check only.
///
/// A request moves its triples out and overwrites their slots, so no triple is returned twice
/// and none outlives its use here. The store is memory only on purpose: a triple restored from
/// disk after a crash could mask two different wires, and the two openings would reveal their
/// difference.
pub struct StagedTripleSource {
    vaults: Vec<PreprocessedKeccakPartyVault>,
}

impl StagedTripleSource {
    /// `vaults`: one per quorum member in quorum order, as a generator returned them, all with
    /// the same number of unused triple words.
    pub fn new(vaults: Vec<PreprocessedKeccakPartyVault>) -> Result<Self, KeccakMpcError> {
        let Some(first) = vaults.first().map(PreprocessedKeccakPartyVault::remaining) else {
            return Err(KeccakMpcError::InvalidParameters);
        };
        if vaults.iter().any(|v| v.poisoned || v.remaining() != first) {
            return Err(KeccakMpcError::InvalidParameters);
        }
        Ok(Self { vaults })
    }

    /// Unused triple words per party.
    pub fn remaining_words(&self) -> usize {
        self.vaults
            .first()
            .map_or(0, PreprocessedKeccakPartyVault::remaining)
    }
}

impl SpdzTripleSource for StagedTripleSource {
    fn vaults(
        &mut self,
        words: usize,
    ) -> Result<Vec<PreprocessedKeccakPartyVault>, KeccakMpcError> {
        if self
            .vaults
            .iter()
            .any(|v| v.poisoned || v.remaining() < words)
        {
            return Err(crate::preprocessing::PreprocessError::VaultExhausted {
                kind: "staged keccak triples",
            }
            .into());
        }
        Ok(self
            .vaults
            .iter_mut()
            .map(|staged| {
                let start = staged.cursor;
                staged.cursor += words;
                // `replace` leaves zeros behind; a plain move would leave a copy in the buffer.
                let triples = staged.triples[start..start + words]
                    .iter_mut()
                    .map(|slot| {
                        core::mem::replace(
                            slot,
                            KeccakBitTripleShare64 {
                                a: [0; 8],
                                b: [0; 8],
                                c: [0; 8],
                                a_mac: [[Tower128::ZERO; 64]; 2],
                                b_mac: [[Tower128::ZERO; 64]; 2],
                                c_mac: [[Tower128::ZERO; 64]; 2],
                            },
                        )
                    })
                    .collect();
                PreprocessedKeccakPartyVault {
                    party_id: staged.party_id,
                    eval_point: staged.eval_point,
                    mac_alpha_lanes: staged.mac_alpha_lanes,
                    triples,
                    cursor: 0,
                    poisoned: false,
                }
            })
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
    online_mesh: Option<&'a mut OtMesh>,
    owned_online_mesh: Option<OtMesh>,
    /// MAC key shares of the quorum, as the most recent vaults carried them.
    alpha: Option<SecretVec<[Tower128; 2]>>,
    perm_ctr: usize,
    flush_ctr: u64,
    open_ctr: u64,
    pending_opened: Vec<BitslicedGf256x64>,
    pending_macs: SecretVec<Vec<SpdzMacWord>>,
    #[cfg(test)]
    verify_each_permutation: bool,
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
            online_mesh: None,
            owned_online_mesh: None,
            alpha: None,
            perm_ctr: 0,
            flush_ctr: 0,
            open_ctr: 0,
            pending_opened: Vec::new(),
            pending_macs: secret_vecs_with_capacity(m, 0),
            #[cfg(test)]
            verify_each_permutation: false,
            poisoned: false,
        })
    }

    /// Reuse a separately provisioned online mesh for all MAC barriers and cut openings.
    /// The mesh must have one endpoint per signing quorum member, in that same order.
    pub fn new_with_mesh(
        session_id: [u8; 32],
        t: usize,
        keys: &'a [SpdzAuthenticatedKeyShare],
        party_rngs: &'a mut [PartyPrivateRng],
        triples: &'a mut dyn SpdzTripleSource,
        online_mesh: &'a mut OtMesh,
    ) -> Result<Self, KeccakMpcError> {
        if online_mesh.n != keys.len() {
            return Err(KeccakMpcError::InvalidParameters);
        }
        let mut engine = Self::new(session_id, t, keys, party_rngs, triples)?;
        engine.online_mesh = Some(online_mesh);
        Ok(engine)
    }

    fn ensure_online_mesh(&mut self) -> Result<(), BaggyError> {
        if self.online_mesh.is_none() && self.owned_online_mesh.is_none() {
            let sid = crate::sponge::keccak::cshake256_32_multi_frame(
                b"QSAG.SPDZ.BLIND.OT/v1",
                &[&self.session_id, b"spdz-sweep-online"],
            );
            match OtMesh::try_establish(sid, self.party_rngs) {
                Ok(mesh) => self.owned_online_mesh = Some(mesh),
                Err(e) => return self.fail(e.into()),
            }
        }
        Ok(())
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

    /// Check all queued Beaver openings immediately. This is also called by
    /// `barrier` and every output opening; a failed check permanently poisons
    /// this engine. Large sweeps flush at a bounded two-permutation buffer.
    pub fn verify_now(&mut self) -> Result<(), BaggyError> {
        self.live()?;
        if self.pending_opened.is_empty() {
            return Ok(());
        }
        let flush_idx = self.flush_ctr;
        self.flush_ctr = match self.flush_ctr.checked_add(1) {
            Some(next) => next,
            None => return self.fail(KeccakMpcError::InvalidParameters),
        };
        let verify_sid = crate::sponge::keccak::cshake256_32_multi_frame(
            b"QSAG.SPDZ_SWEEP.VERIFY.V1",
            &[&self.session_id, &flush_idx.to_le_bytes()],
        );
        self.ensure_online_mesh()?;
        if self.alpha.is_none() {
            // Unchecked openings are pending and nothing can check them: fail closed.
            return self.fail(KeccakMpcError::InvalidParameters);
        }
        let alpha = self
            .alpha
            .as_ref()
            .ok_or_else(|| mpc(KeccakMpcError::InvalidParameters))?;
        let checked = verify_pending_spdz_mac_batch_with_mesh(
            &verify_sid,
            "baggy_spdz_chi",
            self.t,
            &self.quorum_pts,
            &self.pending_opened,
            &self.pending_macs,
            alpha,
            self.party_rngs,
            self.online_mesh
                .as_deref_mut()
                .or(self.owned_online_mesh.as_mut()),
        );
        self.pending_opened.clear();
        for macs in self.pending_macs.iter_mut() {
            macs.secret_wipe();
            macs.clear();
        }
        match checked {
            Ok(()) => Ok(()),
            Err(e) => self.fail(e.into()),
        }
    }

    fn live(&self) -> Result<(), BaggyError> {
        if self.poisoned {
            return Err(mpc(KeccakMpcError::Poisoned));
        }
        Ok(())
    }

    fn fail<T>(&mut self, e: KeccakMpcError) -> Result<T, BaggyError> {
        self.poisoned = true;
        self.pending_opened.clear();
        for macs in self.pending_macs.iter_mut() {
            macs.secret_wipe();
            macs.clear();
        }
        Err(mpc(e))
    }

    /// Shares of the public initial states `midstate ^ frame` of up to 64 instances.
    fn public_states(
        &self,
        alpha: &[[Tower128; 2]],
        frames: &[[u8; SHAKE256_RATE_BYTES]],
    ) -> (
        SecretVec<Vec<BitslicedGf256x64>>,
        SecretVec<Vec<SpdzMacWord>>,
    ) {
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

    /// Up to 64 instances on fresh triples. Returns shared digests; the queued
    /// Beaver MACs must pass `verify_now` before any digest is released.
    fn permute(
        &mut self,
        frames: &[[u8; SHAKE256_RATE_BYTES]],
        absorb: Absorb<'_, 'a>,
    ) -> Result<SharedDigests, BaggyError> {
        self.live()?;
        let m = self.quorum_pts.len();
        let active = frames.len();
        if active == 0 || active > BATCH {
            return self.fail(KeccakMpcError::InvalidParameters);
        }
        let words = 600 * active;
        // Bound retained tag memory to one full 64-lane wave. Sparse waves share the
        // same barrier without paying for an independent coin per permutation, and
        // pooled OtMesh checks take ~31 us per flush.
        if self.pending_opened.len() + 2 * words > 2 * TRIPLE_WORDS_PER_PERMUTATION {
            self.verify_now()?;
        }
        let mut vaults = match self.triples.vaults(words) {
            Ok(v) => v,
            Err(e) => return self.fail(e),
        };
        if vaults.len() != m
            || vaults
                .iter()
                .zip(&self.quorum_pts)
                .any(|(v, pt)| v.poisoned || v.eval_point != *pt || v.remaining() < words)
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

        self.pending_opened.reserve(2 * words);
        for macs in self.pending_macs.iter_mut() {
            secret_vec_reserve(macs, 2 * words);
        }
        let ctr = self.perm_ctr;
        self.perm_ctr += 1;
        let evaluated = if active == BATCH {
            eval_spdz_keccak_f1600_batch64(
                &self.session_id,
                ctr * BATCH,
                self.t,
                &self.quorum_pts,
                &mut sh,
                &mut mac,
                &mut vaults,
                &mut self.pending_opened,
                &mut self.pending_macs,
                self.party_rngs,
            )
        } else {
            // Pack state bits within a sponge into words. A sparse wave consumes
            // 600 words per live sponge, rather than 38,400 padded words.
            (0..active).try_for_each(|instance| {
                let mut single_sh = SecretVec::new(vec![[[0u64; 8]; 25]; m]);
                let mut single_mac = SecretVec::new(vec![[[[Tower128::ZERO; 64]; 2]; 25]; m]);
                for p in 0..m {
                    for bit in 0..STATE_BITS {
                        bs_gf256_insert_lane(
                            &mut single_sh[p][bit / 64],
                            bit % 64,
                            bs_gf256_extract_lane(&sh[p][bit], instance),
                        );
                        for ml in 0..2 {
                            single_mac[p][bit / 64][ml][bit % 64] = mac[p][bit][ml][instance];
                        }
                    }
                }
                eval_spdz_keccak_f1600_single(
                    &self.session_id,
                    ctr * BATCH + instance,
                    self.t,
                    &self.quorum_pts,
                    &mut single_sh,
                    &mut single_mac,
                    &mut vaults,
                    &mut self.pending_opened,
                    &mut self.pending_macs,
                    self.party_rngs,
                )?;
                for p in 0..m {
                    for bit in 0..DIGEST_BITS {
                        bs_gf256_insert_lane(
                            &mut sh[p][bit],
                            instance,
                            bs_gf256_extract_lane(&single_sh[p][bit / 64], bit % 64),
                        );
                        for ml in 0..2 {
                            mac[p][bit][ml][instance] = single_mac[p][bit / 64][ml][bit % 64];
                        }
                    }
                }
                Ok(())
            })
        };
        if let Err(e) = evaluated {
            for v in &mut vaults {
                v.poison_and_wipe();
            }
            return self.fail(e);
        }
        // Release the permutation's triple buffer (~243 MB/party) immediately so it never
        // overlaps with `verify_now` or subsequent permutations.
        drop(vaults);
        #[cfg(test)]
        if self.verify_each_permutation {
            self.verify_now()?;
        }
        // Copy only the 256 digest positions into exact-capacity buffers so the 1,600-bit
        // full-state vectors (6.25x larger) are wiped and freed immediately on drop.
        let dig_sh = SecretVec::new(
            sh.iter()
                .map(|party| party[..DIGEST_BITS].to_vec())
                .collect::<Vec<_>>(),
        );
        drop(sh);
        let dig_mac = SecretVec::new(
            mac.iter()
                .map(|party| party[..DIGEST_BITS].to_vec())
                .collect::<Vec<_>>(),
        );
        drop(mac);
        Ok(SharedDigests {
            sh: dig_sh,
            mac: dig_mac,
        })
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
        self.verify_now()?;
        self.ensure_online_mesh()?;
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
        let open_idx = self.open_ctr;
        self.open_ctr = match self.open_ctr.checked_add(1) {
            Some(next) => next,
            None => return self.fail(KeccakMpcError::InvalidParameters),
        };
        let open_sid = crate::sponge::keccak::cshake256_32_multi_frame(
            b"QSAG.SPDZ_SWEEP.OPEN.V1",
            &[&self.session_id, &open_idx.to_le_bytes()],
        );
        let opened = match commit_and_open_spdz_bs_gf256_batch_quorum_with_mesh(
            &open_sid,
            "baggy_spdz_open",
            self.t,
            &self.quorum_pts,
            &cut_sh,
            &cut_mac,
            &alpha,
            self.online_mesh
                .as_deref_mut()
                .or(self.owned_online_mesh.as_mut()),
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

    fn sweep(&mut self, pk_seed: &[u8; 32], lanes: Vec<LaneSpec>) -> Result<SpdzSweep, BaggyError> {
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
        self.verify_now()
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

/// Which engine a `Baggy` committee runs on.
///
/// Both engines keep the key private against `t - 1` corrupt custodians and abort on any wrong
/// share. They differ in who must be online and in what a permutation costs:
/// [`crate::rss256::Rss256Engine`] needs no preprocessing but all three custodians of a 2-of-3
/// sharing, while [`SpdzSweepEngine`] runs with any `t` of `n` and pays for authenticated
/// Beaver triples on every permutation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BaggyRoute {
    Replicated2of3,
    AuthenticatedShamir,
}

impl BaggyRoute {
    /// The engine for a `t`-of-`n` committee with `online` custodians taking part, or `None`
    /// if that quorum cannot sign. A 2-of-3 committee is replicated only while all three are
    /// online: with two, one corrupt participant is half of the parties present, which the
    /// replicated engine does not tolerate.
    pub const fn select(t: usize, n: usize, online: usize) -> Option<Self> {
        if t == 0 || t > n || online < t || online > n {
            return None;
        }
        if t == 2 && n == 3 && online == 3 {
            Some(Self::Replicated2of3)
        } else {
            Some(Self::AuthenticatedShamir)
        }
    }
}

/// A committee engine chosen by [`BaggyRoute`], so one ceremony is written for both.
#[expect(
    clippy::large_enum_variant,
    reason = "Preserves inline SpdzSweepEngine variant without extra heap indirection"
)]
pub enum RoutedEngine<'a> {
    Replicated2of3(alloc::boxed::Box<crate::rss256::Rss256Engine>),
    AuthenticatedShamir(SpdzSweepEngine<'a>),
}

/// Shared chain values of one [`RoutedEngine`] sweep.
pub enum RoutedSweep {
    Replicated2of3(crate::wots_c::Sweep),
    AuthenticatedShamir(SpdzSweep),
}

impl RoutedEngine<'_> {
    pub const fn route(&self) -> BaggyRoute {
        match self {
            Self::Replicated2of3(_) => BaggyRoute::Replicated2of3,
            Self::AuthenticatedShamir(_) => BaggyRoute::AuthenticatedShamir,
        }
    }
}

impl BaggyEngine for RoutedEngine<'_> {
    type Sweep = RoutedSweep;

    fn pk_seed(&self) -> [u8; 32] {
        match self {
            Self::Replicated2of3(e) => BaggyEngine::pk_seed(&**e),
            Self::AuthenticatedShamir(e) => e.pk_seed(),
        }
    }

    fn session_id(&self) -> &[u8; 32] {
        match self {
            Self::Replicated2of3(e) => BaggyEngine::session_id(&**e),
            Self::AuthenticatedShamir(e) => e.session_id(),
        }
    }

    fn key_identity(&self) -> Result<Option<[u8; 32]>, BaggyError> {
        match self {
            Self::Replicated2of3(e) => BaggyEngine::key_identity(&**e),
            Self::AuthenticatedShamir(e) => e.key_identity(),
        }
    }

    fn bind_key_identity(&mut self, identity: &[u8; 32]) -> Result<(), BaggyError> {
        match self {
            Self::Replicated2of3(e) => BaggyEngine::bind_key_identity(&mut **e, identity),
            Self::AuthenticatedShamir(e) => e.bind_key_identity(identity),
        }
    }

    fn randomiser(&mut self, mu: &[u8; 32]) -> Result<[u8; 32], BaggyError> {
        match self {
            Self::Replicated2of3(e) => BaggyEngine::randomiser(&mut **e, mu),
            Self::AuthenticatedShamir(e) => e.randomiser(mu),
        }
    }

    fn sweep(
        &mut self,
        pk_seed: &[u8; 32],
        lanes: Vec<LaneSpec>,
    ) -> Result<RoutedSweep, BaggyError> {
        match self {
            Self::Replicated2of3(e) => {
                BaggyEngine::sweep(&mut **e, pk_seed, lanes).map(RoutedSweep::Replicated2of3)
            }
            Self::AuthenticatedShamir(e) => e
                .sweep(pk_seed, lanes)
                .map(RoutedSweep::AuthenticatedShamir),
        }
    }

    fn barrier(&mut self) -> Result<(), BaggyError> {
        match self {
            Self::Replicated2of3(e) => BaggyEngine::barrier(&mut **e),
            Self::AuthenticatedShamir(e) => e.barrier(),
        }
    }

    fn open_round(
        &mut self,
        sweep: &RoutedSweep,
        picks: &[(usize, u8)],
    ) -> Result<Vec<[u8; 32]>, BaggyError> {
        match (self, sweep) {
            (Self::Replicated2of3(e), RoutedSweep::Replicated2of3(s)) => {
                BaggyEngine::open_round(&mut **e, s, picks)
            }
            (Self::AuthenticatedShamir(e), RoutedSweep::AuthenticatedShamir(s)) => {
                e.open_round(s, picks)
            }
            // A sweep of the other engine holds shares this one cannot open.
            _ => Err(BaggyError::InvalidParameters),
        }
    }
}

#[cfg(test)]
pub(crate) mod tests {
    extern crate std;
    use super::*;
    use crate::baggy::{
        BaggyKeyBinding, BaggyParams, MemoryFirstSigned, WaistbandCache, baggy_keygen_mpc,
        baggy_reference_keygen, baggy_reference_sign, baggy_sign_mpc, baggy_verify,
    };
    use crate::keccak_mpc::tests::SpdzTestDealer;
    use crate::pors_fp::PorsFpParams;
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
    fn dealerless_source_error_wipes_keys_and_refuses_retry() {
        let sid = [0xe2; 32];
        let points = [TowerGf256(1), TowerGf256(2)];
        let mut rngs: Vec<_> = (0..2)
            .map(|p| PartyPrivateRng::from_seed([0x61 + p; 32], b"source-poison"))
            .collect();
        let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut rngs);
        let mut alpha = [[Tower128(19), Tower128(23)]; 2];
        let mut shamir = [[Tower128(29), Tower128(31)]; 2];
        let mut source = DealerlessPcgTripleSource {
            session_id: sid,
            t: 0, // Reaches the generator and induces InvalidThreshold.
            eval_points: &points,
            quorum: &[0, 1],
            tree_depth: 1,
            alpha_contribs: &mut alpha,
            alpha_shamir: &mut shamir,
            ot_mesh: &mut mesh,
            party_rngs: &mut rngs,
            requests: 0,
        };
        assert!(matches!(
            source.vaults(1),
            Err(KeccakMpcError::Preprocess(
                crate::preprocessing::PreprocessError::InvalidThreshold { .. }
            ))
        ));
        assert_eq!(source.requests, u64::MAX);
        assert!(
            source
                .alpha_contribs
                .iter()
                .chain(source.alpha_shamir.iter())
                .flatten()
                .all(|x| *x == Tower128::ZERO)
        );
        // Repairing the initial parameter cannot revive a failed source.
        source.t = 2;
        let before = source.ot_mesh.transcript_digest();
        assert!(matches!(source.vaults(1), Err(KeccakMpcError::Poisoned)));
        assert_eq!(source.ot_mesh.transcript_digest(), before);
        assert_eq!(alpha, [[Tower128::ZERO; 2]; 2]);
        assert_eq!(shamir, [[Tower128::ZERO; 2]; 2]);
    }

    #[test]
    fn sweep_openings_match_the_reference_and_reveal_only_the_picks() {
        let _memory = crate::test_budget::reserve_mb(1900);
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
    const TINY: BaggyParams = BaggyParams {
        subtree_height: 1,
        num_layers: 1,
        pors: PorsFpParams {
            tree_height: 4,
            reveal: 4,
            max_auth_nodes: 7,
        },
        ..BaggyParams::TEST_SMALL
    };

    /// A different root-key binding for the parameter-refusal test.
    const OTHER_PARAMS: BaggyParams = BaggyParams {
        num_layers: 2,
        ..TINY
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
    fn route_is_replicated_only_for_two_of_three_with_everyone_online() {
        use BaggyRoute::{AuthenticatedShamir, Replicated2of3};
        assert_eq!(BaggyRoute::select(2, 3, 3), Some(Replicated2of3));
        for (t, n, online) in [(2, 3, 2), (3, 3, 3), (3, 5, 4), (2, 4, 3)] {
            assert_eq!(BaggyRoute::select(t, n, online), Some(AuthenticatedShamir));
        }
        for (t, n, online) in [(0, 3, 3), (4, 3, 3), (2, 3, 1), (2, 3, 4)] {
            assert_eq!(BaggyRoute::select(t, n, online), None);
        }
    }

    /// The same ceremony code signs on either route, and the two routes cannot open each
    /// other's sweeps.
    #[test]
    fn routed_engines_sign_the_reference_signature_and_reject_foreign_sweeps() {
        let _memory = crate::test_budget::reserve_mb(1500);
        use crate::keccak_mpc::run_dealerless_rss_dkg_2of3;
        use crate::rss256::Rss256Engine;

        let params = &TINY;
        let sign = |engine: &mut RoutedEngine<'_>, sk: &PqSecretKey| {
            let pk = baggy_reference_keygen(params, sk).unwrap();
            let binding = BaggyKeyBinding::new(params, &pk);
            engine.bind_key_identity(&binding.identity()).unwrap();
            let msg = b"routed committee";
            let sig = baggy_sign_mpc(
                engine,
                params,
                &pk,
                &binding,
                &mut WaistbandCache::disabled(),
                &mut MemoryFirstSigned::new(),
                msg,
            )
            .unwrap();
            assert_eq!(Some(sig), baggy_reference_sign(params, sk, &pk, msg));
        };

        let sid = [0x48; 32];
        let mut dkg_rngs: [PartyPrivateRng; 3] = core::array::from_fn(|p| {
            PartyPrivateRng::from_seed([0x48 ^ ((p as u8) << 4); 32], b"routed-dkg")
        });
        let (rss_keys, _) = run_dealerless_rss_dkg_2of3(sid, 32, &mut dkg_rngs).unwrap();
        let rss = Rss256Engine::new(sid, rss_keys, dkg_rngs).unwrap();
        let xor3 = |slots: [&[u8]; 3]| -> [u8; 32] {
            core::array::from_fn(|i| slots[0][i] ^ slots[1][i] ^ slots[2][i])
        };
        let rss_sk = PqSecretKey {
            sk_seed: xor3(rss.sk_seed_slots()),
            sk_prf: xor3(rss.sk_prf_slots()),
            pk_seed: Rss256Engine::pk_seed(&rss),
        };
        let mut replicated = RoutedEngine::Replicated2of3(alloc::boxed::Box::new(rss));
        assert_eq!(Some(replicated.route()), BaggyRoute::select(2, 3, 3));
        sign(&mut replicated, &rss_sk);

        let mut s = setup(2, 3, &[0, 2], 0x49);
        let mut shamir = RoutedEngine::AuthenticatedShamir(
            SpdzSweepEngine::new([0x49; 32], 2, &s.keys, &mut s.rngs, &mut s.source).unwrap(),
        );
        assert_eq!(Some(shamir.route()), BaggyRoute::select(2, 3, 2));
        sign(&mut shamir, &sk());

        let lanes = vec![LaneSpec::pors(0, 0, 0)];
        let foreign = replicated.sweep(&rss_sk.pk_seed, lanes).unwrap();
        assert_eq!(
            shamir.open_round(&foreign, &[(0, 0)]),
            Err(BaggyError::InvalidParameters)
        );
    }

    #[test]
    fn baggy_two_of_three_equals_the_reference() {
        let _memory = crate::test_budget::reserve_mb(900);
        sign_and_compare(&TINY, 2, 3, &[0, 2], 0x31);
    }

    #[test]
    fn baggy_three_of_five_equals_the_reference() {
        let _memory = crate::test_budget::reserve_mb(1200);
        sign_and_compare(&TINY, 3, 5, &[0, 3, 4], 0x32);
    }

    #[test]
    fn baggy_five_of_seven_equals_the_reference() {
        let _memory = crate::test_budget::reserve_mb(1700);
        sign_and_compare(&TINY, 5, 7, &[0, 1, 3, 5, 6], 0x33);
    }

    #[test]
    fn baggy_all_of_three_equals_the_reference() {
        let _memory = crate::test_budget::reserve_mb(1200);
        sign_and_compare(&TINY, 3, 3, &[0, 1, 2], 0x34);
    }

    #[test]
    fn baggy_three_of_five_with_a_spare_party_equals_the_reference() {
        let _memory = crate::test_budget::reserve_mb(1500);
        // Four parties of a 3-of-5 sharing: more than the threshold take part.
        sign_and_compare(&TINY, 3, 5, &[1, 2, 3, 4], 0x35);
    }

    #[test]
    fn keygen_two_of_three_equals_the_reference() {
        let _memory = crate::test_budget::reserve_mb(900);
        let mut s = setup(2, 3, &[1, 2], 0x36);
        let sk = sk();
        let mut engine =
            SpdzSweepEngine::new([0x36; 32], 2, &s.keys, &mut s.rngs, &mut s.source).unwrap();
        let (pk, binding) =
            baggy_keygen_mpc(&mut engine, &TINY, &mut WaistbandCache::disabled()).unwrap();
        assert_eq!(Some(pk), baggy_reference_keygen(&TINY, &sk));
        assert_eq!(engine.key_identity().unwrap(), Some(binding.identity()));
        // The shares now belong to this key under these parameters only.
        assert!(
            baggy_keygen_mpc(&mut engine, &OTHER_PARAMS, &mut WaistbandCache::disabled()).is_err()
        );
    }

    /// No dealer anywhere: dealerless key generation, MAC key, key-share authentication and
    /// triples for a 3-of-4 sharing, then a sweep by the quorum `{0, 2, 3}` checked against
    /// the hash of the key reconstructed from the same shares.
    #[test]
    fn dealerless_keys_and_triples_drive_a_three_of_four_sweep() {
        let _memory = crate::test_budget::reserve_mb(1800);
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
        let (mut alpha_c, mut alpha_sh) =
            spdz_setup_alpha_gf256(&[0xc3; 32], t, &pts, &mut rngs).unwrap();
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
            alpha_contribs: &mut alpha_c,
            alpha_shamir: &mut alpha_sh,
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
    #[ignore = "full dealerless permutation performance measurement"]
    fn measurement_dealerless_full_wave() {
        use crate::dkg::run_dealerless_dkg_seed32_gf256;
        use crate::field::tower::lagrange_weights_zero_gf256;
        use crate::keccak_mpc::authenticate_dkg_seed_shares_for_spdz;
        use crate::preprocessing::{PCG_DEFAULT_TREE_DEPTH, spdz_setup_alpha_gf256};
        use crate::tsw_baggy::{Cshake256Suite, th_secret_prf};

        let (t, n) = (2usize, 3usize);
        let pts: Vec<TowerGf256> = (1..=n as u8).map(TowerGf256).collect();
        let mut rngs: Vec<PartyPrivateRng> = (0..n)
            .map(|i| PartyPrivateRng::from_seed([0x50 + i as u8; 32], b"spdz-sweep-dealerless"))
            .collect();
        let mut mesh = OtMesh::try_establish([0xc0; 32], &mut rngs).unwrap();
        let (seed_shares, pk_seed) =
            run_dealerless_dkg_seed32_gf256([0xc1; 32], t, &pts, &mut mesh, &mut rngs).unwrap();
        let (prf_shares, _) =
            run_dealerless_dkg_seed32_gf256([0xc2; 32], t, &pts, &mut mesh, &mut rngs).unwrap();
        let (mut alpha_c, mut alpha_sh) =
            spdz_setup_alpha_gf256(&[0xc3; 32], t, &pts, &mut rngs).unwrap();
        let keys = authenticate_dkg_seed_shares_for_spdz(
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

        let quorum = [0usize, 1, 2];
        let weights = lagrange_weights_zero_gf256(&[pts[0], pts[1]]).unwrap();
        let mut sk_seed = [0u8; 32];
        for bit in 0..256 {
            let mut value = TowerGf256::ZERO;
            for (weight, &p) in weights.iter().zip(&quorum[..t]) {
                value = value.add(weight.mul(seed_shares[p].bit_shares[bit]));
            }
            assert!(value.0 <= 1);
            sk_seed[bit / 8] |= value.0 << (bit % 8);
        }

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
            alpha_contribs: &mut alpha_c,
            alpha_shamir: &mut alpha_sh,
            ot_mesh: &mut mesh,
            party_rngs: &mut rngs,
            requests: 0,
        };
        let mut engine =
            SpdzSweepEngine::new([0xc6; 32], t, &keys, &mut session_rngs, &mut source).unwrap();
        let lane = LaneSpec::pors(9, 1, 5);
        let frame = tsw_secret32_frame(TAG_PRF, &pk_seed, &lane.prf);
        let started = std::time::Instant::now();
        let digests = engine
            .permute(&[frame; 64], &mut |engine, sh, mac| {
                engine.absorb_key(
                    |k| (&k.sk_seed_words, &k.sk_seed_macs),
                    TSW_PRF_SECRET_OFFSET,
                    64,
                    sh,
                    mac,
                );
            })
            .unwrap();
        engine.verify_now().unwrap();
        let elapsed = started.elapsed();
        std::eprintln!(
            "authenticated full 64-lane permutation with dealerless triples: {elapsed:?}"
        );
        let opened = engine.open_masked(&[(&digests, u64::MAX)]).unwrap();
        let expected = th_secret_prf(Cshake256Suite, &pk_seed, &sk_seed, &lane.prf);
        assert!(opened[0].iter().all(|value| *value == expected));
    }

    /// Online cost alone: the triples of one full wave are staged before the clock starts.
    #[test]
    #[ignore = "online full-wave permutation performance measurement"]
    fn measurement_online_full_wave_with_staged_triples() {
        use crate::tsw_baggy::{Cshake256Suite, th_secret_prf};

        for (t, n, quorum) in [(2usize, 3usize, &[0usize, 1][..]), (3, 5, &[0, 2, 4][..])] {
            let mut s = setup(t, n, quorum, 0x4a);
            let mut staged =
                StagedTripleSource::new(s.source.dealer.vaults(TRIPLE_WORDS_PER_PERMUTATION))
                    .unwrap();
            let sk = sk();
            let mut engine =
                SpdzSweepEngine::new([0x4a; 32], t, &s.keys, &mut s.rngs, &mut staged).unwrap();
            let lane = LaneSpec::pors(9, 1, 5);
            let frame = tsw_secret32_frame(TAG_PRF, &sk.pk_seed, &lane.prf);
            let started = std::time::Instant::now();
            let digests = engine
                .permute(&[frame; 64], &mut |engine, sh, mac| {
                    engine.absorb_key(
                        |k| (&k.sk_seed_words, &k.sk_seed_macs),
                        TSW_PRF_SECRET_OFFSET,
                        64,
                        sh,
                        mac,
                    );
                })
                .unwrap();
            let evaluated = started.elapsed();
            engine.verify_now().unwrap();
            let checked = started.elapsed();
            std::eprintln!(
                "online {t}-of-{n} 64-lane permutation, staged triples: eval {evaluated:?}, with MAC check {checked:?}"
            );
            let opened = engine.open_masked(&[(&digests, u64::MAX)]).unwrap();
            let expected = th_secret_prf(Cshake256Suite, &sk.pk_seed, &sk.sk_seed, &lane.prf);
            assert!(opened[0].iter().all(|value| *value == expected));
        }
    }

    #[test]
    fn staged_source_hands_out_each_triple_once_and_then_refuses() {
        let mut s = setup(2, 3, &[0, 2], 0x4b);
        let dealt = s.source.dealer.vaults(1200);
        let at =
            |k: usize| -> Vec<BitslicedGf256x64> { dealt.iter().map(|v| v.triples[k].a).collect() };
        let (first, later) = (at(0), at(600));
        assert_ne!(first, later);
        let mut staged = StagedTripleSource::new(dealt).unwrap();
        assert_eq!(staged.remaining_words(), 1200);

        let one = staged.vaults(600).unwrap();
        assert!(one.iter().all(|v| v.remaining() == 600));
        assert_eq!(
            one.iter().map(|v| v.triples[0].a).collect::<Vec<_>>(),
            first
        );
        assert!(staged.vaults.iter().all(|v| {
            v.triples[..600]
                .iter()
                .all(|tr| tr.a == [0; 8] && tr.c_mac == [[Tower128::ZERO; 64]; 2])
        }));
        assert!(staged.vaults(601).is_err());
        assert_eq!(staged.remaining_words(), 600);

        let two = staged.vaults(600).unwrap();
        assert_eq!(
            two.iter().map(|v| v.triples[0].a).collect::<Vec<_>>(),
            later
        );
        assert_eq!(staged.remaining_words(), 0);
        assert!(staged.vaults(1).is_err());

        // The same sweep opens the same value whether its triples were staged or dealt on demand.
        let lane = || vec![LaneSpec::pors(0, 0, 0)];
        let seed = s.keys[0].pk_seed;
        let mut on_demand =
            SpdzSweepEngine::new([0x4b; 32], 2, &s.keys, &mut s.rngs, &mut s.source).unwrap();
        let sweep = on_demand.sweep(&seed, lane()).unwrap();
        let expected = on_demand.open_round(&sweep, &[(0, 0)]).unwrap();
        let used = on_demand.permutations();
        drop(on_demand);
        let mut staged = StagedTripleSource::new(s.source.dealer.vaults(600 * used)).unwrap();
        let mut engine =
            SpdzSweepEngine::new([0x4c; 32], 2, &s.keys, &mut s.rngs, &mut staged).unwrap();
        let sweep = engine.sweep(&seed, lane()).unwrap();
        assert_eq!(engine.open_round(&sweep, &[(0, 0)]).unwrap(), expected);
        drop(engine);
        assert_eq!(staged.remaining_words(), 0);
    }

    #[test]
    fn deferred_fault_is_rejected_before_any_cut_and_poison_is_permanent() {
        let mut s = setup(2, 3, &[0, 1], 0x47);
        s.source.corrupt_request = Some(0);
        let seed = s.keys[0].pk_seed;
        let mut engine =
            SpdzSweepEngine::new([0x47; 32], 2, &s.keys, &mut s.rngs, &mut s.source).unwrap();
        let sweep = engine.sweep(&seed, vec![LaneSpec::pors(0, 0, 0)]).unwrap();
        assert!(!engine.pending_opened.is_empty());
        assert!(!engine.is_poisoned());
        assert!(engine.open_round(&sweep, &[(0, 1)]).is_err());
        assert!(engine.is_poisoned());
        assert!(engine.pending_opened.is_empty());
        assert!(engine.pending_macs.iter().all(Vec::is_empty));
        assert!(engine.verify_now().is_err());
        assert!(engine.barrier().is_err());
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
        engine.verify_each_permutation = true;
        assert!(
            engine
                .sweep(&sk.pk_seed, vec![LaneSpec::pors(0, 0, 0)])
                .is_err()
        );
        assert!(engine.is_poisoned());
        assert_eq!(engine.permutations(), 1);
        assert!(
            engine
                .sweep(&sk.pk_seed, vec![LaneSpec::pors(0, 0, 1)])
                .is_err()
        );
        assert!(engine.randomiser(&[0; 32]).is_err());
        assert!(engine.barrier().is_err());
        assert_eq!(engine.permutations(), 1);

        // A corrupted triple fails the batched check of its own permutation.
        let mut s = setup(2, 3, &[0, 1], 0x43);
        s.source.corrupt_request = Some(1);
        let mut engine =
            SpdzSweepEngine::new([0x43; 32], 2, &s.keys, &mut s.rngs, &mut s.source).unwrap();
        engine.verify_each_permutation = true;
        assert!(
            engine
                .sweep(&sk.pk_seed, vec![LaneSpec::pors(0, 0, 0)])
                .is_err()
        );
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
