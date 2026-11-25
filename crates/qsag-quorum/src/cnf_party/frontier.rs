//! The two production FrontierSumFts profiles over the isolated CNF Keccak engine.
//! Public prefix blocks are permuted locally. Every permutation after the first
//! secret byte uses authenticated CNF lanes. Keygen opens only the root.

#![forbid(unsafe_code)]
use super::*;
use qsag_core::sponge::keccak::{cshake256_static_midstate, keccak_f1600};
use qsag_fts::frontier::{TAG_CHAIN, TAG_LEAF, TAG_MERGE, TAG_RAND};
use qsag_fts::{
    FrontierDpTable, FrontierFtsProfile, FrontierFtsPublicKey, FrontierFtsSignature, FtsEpochWal,
    verify_frontier_fts,
};

enum Field<'a> {
    Public(&'a [u8]),
    Seed,
    Prf,
    Node(&'a CachedKeyPlanes),
}

struct Frame<'a> {
    clear: Vec<u8>,
    secrets: Vec<(usize, &'a CachedKeyPlanes)>,
}

impl<T: WireTransport, J: PoisonJournal> IsolatedCnfParty<T, J> {
    fn frontier_batch(
        &mut self,
        tag: &[u8],
        messages: &[Vec<Field<'_>>],
    ) -> Result<Vec<CachedKeyPlanes>, CnfPartyError> {
        let mut result = Vec::with_capacity(messages.len());
        for chunk in messages.chunks(BATCH_SPONGES) {
            let mut frames = Vec::with_capacity(chunk.len());
            for fields in chunk {
                let mut clear = (fields.len() as u64).to_le_bytes().to_vec();
                let mut secrets = Vec::new();
                for field in fields {
                    if let Field::Public(b) = field {
                        clear.extend_from_slice(&(b.len() as u64).to_le_bytes());
                        clear.extend_from_slice(b);
                        continue;
                    }
                    let value = match field {
                        Field::Seed => self.cached_sk_seed.as_ref(),
                        Field::Prf => self.cached_sk_prf.as_ref(),
                        Field::Node(v) => Some(*v),
                        Field::Public(_) => unreachable!(),
                    }
                    .ok_or(CnfPartyError::InvalidParameters)?;
                    clear.extend_from_slice(&32u64.to_le_bytes());
                    let offset = clear.len();
                    // All four canonical Frontier frames place whole secret words
                    // inside one rate block. Reject an unsupported framing change.
                    if value.words != 4 || offset % RATE_BYTES + 32 > RATE_BYTES {
                        return Err(CnfPartyError::InvalidParameters);
                    }
                    secrets.push((offset, value));
                    clear.resize(offset + 32, 0);
                }
                let end = clear.len();
                clear.resize((end / RATE_BYTES + 1) * RATE_BYTES, 0);
                clear[end] = 4;
                let last = clear.len() - 1;
                clear[last] ^= 128;
                frames.push(Frame { clear, secrets });
            }
            let start = frames[0].secrets[0].0 / RATE_BYTES;
            let blocks = frames[0].clear.len() / RATE_BYTES;
            let count = chunk.len();
            let mut state = BatchPlaneStates::zero(self.topo.held.len(), count);
            // Absorb every secret into the correct block before the first MPC
            // permutation. Subsequent blocks in these frames are all public.
            for (sp, frame) in frames.iter().enumerate() {
                if frame.clear.len() != blocks * RATE_BYTES
                    || frame.secrets.iter().any(|(o, _)| o / RATE_BYTES != start)
                {
                    return Err(CnfPartyError::InvalidParameters);
                }
                let mut pre = cshake256_static_midstate(tag);
                for block in frame.clear[..start * RATE_BYTES]
                    .as_chunks::<RATE_BYTES>()
                    .0
                {
                    for (word, b) in pre.iter_mut().zip(block.as_chunks::<8>().0) {
                        *word ^= u64::from_le_bytes(*b);
                    }
                    keccak_f1600(&mut pre);
                }
                if let Some(l) = self.topo.local[0] {
                    state.bits[l][sp] = pre;
                }
                for (l, &r) in self.r.iter().enumerate() {
                    for k in 0..128 {
                        let mask = 0u64.wrapping_sub(core::hint::black_box((r >> k) as u64 & 1));
                        state.rand[l][k * count + sp] = pre.map(|v| v & mask);
                    }
                }
                for (o, v) in &frame.secrets {
                    state.absorb_secret_words(sp, o % RATE_BYTES, 4, &v.bits, &v.rand);
                }
            }
            // Only the clear frame bytes survive across mutable calls on the engine.
            let clear: Vec<_> = frames.into_iter().map(|f| f.clear).collect();
            for block in start..blocks {
                for (sp, bytes) in clear.iter().enumerate() {
                    self.xor_public_block_into_sponge(
                        &mut state,
                        sp,
                        &bytes.as_chunks::<RATE_BYTES>().0[block],
                    );
                }
                self.keccak_f_batch(&mut state)?;
            }
            for sp in 0..count {
                let (bits, rand) = state.extract_secret_words(sp, 4);
                result.push(CachedKeyPlanes {
                    words: 4,
                    bits,
                    rand,
                });
            }
        }
        Ok(result)
    }

    fn frontier_open(&mut self, nodes: &[&CachedKeyPlanes]) -> Result<Vec<u8>, CnfPartyError> {
        self.barrier_inner()?;
        let shares = SecretBuffer(
            (0..self.topo.held.len())
                .map(|l| {
                    let mut bytes = Vec::with_capacity(nodes.len() * 32);
                    for n in nodes {
                        words_to_bytes(&n.bits[l], &mut bytes);
                    }
                    bytes
                })
                .collect::<Vec<_>>(),
        );
        self.open_shares(ROUND_CNF_OPEN, &shares)
    }

    /// Evaluate all endpoints bottom-up. Keep only the active level and the
    /// requested frontier positions. No interior endpoint is made public.
    fn frontier_tree(
        &mut self,
        profile: FrontierFtsProfile,
        picks: &[(u32, u8)],
    ) -> Result<(Vec<u8>, Vec<CachedKeyPlanes>), CnfPartyError> {
        use Field::{Node, Public, Seed};
        self.ensure_key_seed_planes()?;
        let p = profile.params();
        let pid = profile.pid_bytes();
        let seed = self.pk_seed;
        let mut level = Vec::new();
        let mut selected: Vec<Option<CachedKeyPlanes>> = (0..picks.len()).map(|_| None).collect();
        for depth in (0..=p.tree_height).rev() {
            let count = 1usize << depth;
            let addresses: Vec<_> = (count..2 * count)
                .map(|v| (v as u64).to_be_bytes())
                .collect();
            let mut frames = Vec::with_capacity(count);
            for (i, address) in addresses.iter().enumerate() {
                let mut f = vec![Public(&pid), Public(&seed), Public(address)];
                if depth == p.tree_height {
                    f.push(Seed);
                } else {
                    f.extend([Node(&level[2 * i]), Node(&level[2 * i + 1])]);
                }
                frames.push(f);
            }
            let tag = if depth == p.tree_height {
                TAG_LEAF
            } else {
                TAG_MERGE
            };
            level = self.frontier_batch(tag, &frames)?;
            if depth == 0 {
                break;
            }
            for step in 0..p.winternitz_w {
                for (idx, &(v, pos)) in picks.iter().enumerate() {
                    if usize::from(pos) == step && (count..2 * count).contains(&(v as usize)) {
                        let n = &level[v as usize - count];
                        selected[idx] = Some(CachedKeyPlanes {
                            words: 4,
                            bits: n.bits.clone(),
                            rand: n.rand.clone(),
                        });
                    }
                }
                if step + 1 == p.winternitz_w {
                    break;
                }
                let j = (step as u64).to_be_bytes();
                let f: Vec<_> = addresses
                    .iter()
                    .zip(&level)
                    .map(|(v, n)| vec![Public(&pid), Public(&seed), Public(v), Public(&j), Node(n)])
                    .collect();
                level = self.frontier_batch(TAG_CHAIN, &f)?;
            }
        }
        let root = self.frontier_open(&[&level[0]])?;
        Ok((
            root,
            selected
                .into_iter()
                .collect::<Option<Vec<_>>>()
                .ok_or(CnfPartyError::InvalidParameters)?,
        ))
    }

    fn agree_frontier(&mut self, operation: &[u8], fields: &[&[u8]]) -> Result<(), CnfPartyError> {
        const INTENT: u32 = 0x0408_0000;
        let intent = h32(
            b"QSAG.CNF.FRONTIER.INTENT/v1",
            &[&self.session, operation, &h32(b"fields", fields)],
        );
        for peer in self.topo.peers() {
            self.transport.send_frame(peer, INTENT, &intent)?;
        }
        for peer in self.topo.peers() {
            if self.recv(peer, INTENT, 32)? != intent {
                return Err(CnfPartyError::ConsistencyMismatch { peer });
            }
        }
        Ok(())
    }

    fn lock_frontier(&mut self, profile: FrontierFtsProfile) -> Result<(), CnfPartyError> {
        let id = h32(
            b"QSAG.CNF.FRONTIER/v1",
            &[&profile.pid_bytes(), &self.pk_seed],
        );
        if self.key_len != 32
            || self.slh_profile_digest.is_some()
            || self.scheme_identity.is_some_and(|prev| prev != id)
        {
            return Err(CnfPartyError::InvalidParameters);
        }
        self.scheme_identity = Some(id);
        Ok(())
    }

    pub fn frontier_public_key(
        &mut self,
        profile: FrontierFtsProfile,
    ) -> Result<FrontierFtsPublicKey, CnfPartyError> {
        self.lock_frontier(profile)?;
        self.guarded(|p| {
            let seed = p.pk_seed;
            p.agree_frontier(b"public", &[&profile.pid_bytes(), &seed])?;
            Ok(FrontierFtsPublicKey {
                profile,
                pk_seed: p.pk_seed,
                root: p.frontier_tree(profile, &[])?.0,
            })
        })
    }

    /// Reserve the only use before opening even the randomizer. Each party's
    /// WAL must enforce the use limit across concurrent sessions and restarts.
    pub fn frontier_sign(
        &mut self,
        pk: &FrontierFtsPublicKey,
        msg: &[u8],
        hedge: &[u8; 32],
        wal: &mut impl FtsEpochWal,
    ) -> Result<FrontierFtsSignature, CnfPartyError> {
        use Field::{Prf, Public};
        if self.is_poisoned() {
            return Err(CnfPartyError::Poisoned);
        }
        if pk.pk_seed != self.pk_seed || pk.root.len() != 32 {
            return Err(CnfPartyError::InvalidParameters);
        }
        self.lock_frontier(pk.profile)?;
        let key = pk.wal_key();
        if wal
            .uses_completed(&key)
            .map_err(|_| CnfPartyError::Journal)?
            != 0
        {
            return Err(CnfPartyError::Journal);
        }
        wal.reserve_use(&key, 1)
            .map_err(|_| CnfPartyError::Journal)?;
        self.guarded(|p| {
            let digest = pk.message_digest(msg);
            p.agree_frontier(
                b"sign",
                &[
                    &pk.profile.pid_bytes(),
                    &pk.pk_seed,
                    &pk.root,
                    &digest,
                    hedge,
                ],
            )?;
            p.ensure_key_prf_planes()?;
            let pid = pk.profile.pid_bytes();
            let random = p.frontier_batch(
                TAG_RAND,
                &[vec![
                    Public(&pid),
                    Prf,
                    Public(&pk.pk_seed),
                    Public(&pk.root),
                    Public(hedge),
                    Public(&[0]),
                    Public(&digest),
                ]],
            )?;
            let r: [u8; 32] = p
                .frontier_open(&[&random[0]])?
                .try_into()
                .map_err(|_| CnfPartyError::InvalidParameters)?;
            let dp = FrontierDpTable::build(pk.profile);
            let (grind_counter, nodes, offsets) = pk
                .signing_frontier(&dp, &digest, &r)
                .map_err(|_| CnfPartyError::InvalidParameters)?;
            let picks: Vec<_> = nodes.into_iter().zip(offsets).collect();
            let (root, selected) = p.frontier_tree(pk.profile, &picks)?;
            if root != pk.root {
                return Err(CnfPartyError::InvalidParameters);
            }
            let mut sig = FrontierFtsSignature {
                grind_counter,
                randomizer: r.to_vec(),
                chain_values: p.frontier_open(&selected.iter().collect::<Vec<_>>())?,
            };
            if verify_frontier_fts(pk, &dp, msg, &sig).is_err() {
                wipe_bytes(&mut sig.chain_values);
                return Err(CnfPartyError::MultiplicationCheckFailed);
            }
            Ok(sig)
        })
    }
}
