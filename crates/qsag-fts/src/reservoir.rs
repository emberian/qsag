//! Bounded, explicitly driven dealerless preprocessing. Each refill is a complete
//! DKG consistency barrier under the existing secret/MAC keys. No unverified pool
//! is exposed to a signer, and no previously consumed tuple is regenerated.
use super::dkg::finalize_dkg;
use super::*;

/// An activated key with a bounded power reservoir. Drivers prepare one leaf (or
/// sign one message), then refill before the next operation when needed. Tree
/// height changes the number of refills, not the preprocessing allocation.
///
/// This is an in-memory protocol state, not a crash-recovery format. Persist burn
/// state as usual; never restore a snapshot of a consumed preprocessing pool.
pub struct ParallelSeededDkgReservoir {
    output: ParallelSeededDkgOutput,
    generation: u64,
}
impl ParallelSeededDkgReservoir {
    /// Adopt an already activated, bounded initial ceremony.
    pub fn new(output: ParallelSeededDkgOutput) -> Result<Self, ParallelSeededError> {
        if output.share.is_poisoned()
            || output.share.beaver_pool.len() > DEFAULT_BEAVER_TRIPLE_POOL
            || output.beaver_triples.len() > DEFAULT_BEAVER_TRIPLE_POOL
        {
            return Err(ParallelSeededError::InvalidThresholdParameters);
        }
        Ok(Self {
            output,
            generation: 0,
        })
    }
    pub fn pk_seed_bytes(&self) -> [u8; 32] {
        self.output.pk_seed_bytes
    }
    pub const fn generation(&self) -> u64 {
        self.generation
    }
    pub const fn party_id(&self) -> u16 {
        self.output.share.party_id
    }
    pub const fn params(&self) -> ParallelSeededParams {
        self.output.share.params
    }
    pub fn committee(&self) -> &[u16] {
        &self.output.share.committee
    }
    pub fn share_mut(&mut self) -> &mut ParallelSeededPartyShare {
        self.output.share_mut()
    }
    /// Serialize this custodian's activated reservoir (excluding already-consumed power tuples)
    /// into a zeroizing byte buffer for encrypted local vault persistence.
    ///
    /// Callers MUST still enforce monotonic epoch burns (`FsWalFtsEpochLatch` / `FsCeremonyJournal`
    /// and external hardware/directory anchor) and atomically replace the stored reservoir before
    /// reusing any preprocessing pool across process restarts.
    pub fn to_secret_bytes(&self) -> Result<SecretVec<u8>, ParallelSeededError> {
        let share = &self.output.share;
        if share.poisoned {
            return Err(ParallelSeededError::Poisoned);
        }
        if !share.pending_openings.is_empty()
            || !ct_eq_bytes(&self.output.pk_seed_bytes, &share.key_seed)
            || share.params.validate().is_err()
            || share.committee.len() < 2
            || share.committee.len() > 255
            || !share.committee.windows(2).all(|w| w[0] < w[1])
            || !share.committee.contains(&share.party_id)
            || share.pairwise_zero_seeds.len() + 1 != share.committee.len()
            || share.beaver_cursor > share.beaver_pool.len()
        {
            return Err(ParallelSeededError::InvalidThresholdParameters);
        }
        let unspent_powers = &share.beaver_pool[share.beaver_cursor..];
        if unspent_powers.len() > DEFAULT_BEAVER_TRIPLE_POOL
            || self.output.beaver_triples.len() > DEFAULT_BEAVER_TRIPLE_POOL
            || share.epoch_uses.len() != (1usize << share.params.tree_height)
        {
            return Err(ParallelSeededError::InvalidThresholdParameters);
        }
        let exact_len = 8 // QSFTSRS1
            + 8 // generation
            + 32 // pk_seed_bytes
            + 2 // party_id
            + 16 // params (4 * u32)
            + 2 + share.committee.len() * 2
            + 32 // sk_seed_lanes
            + 64 // sk_seed_macs
            + 32 // sk_prf_lanes
            + 64 // sk_prf_macs
            + 32 // bdoz_alpha_share
            + 32 // local_salt_seed
            + 2 + share.pairwise_zero_seeds.len() * 34
            + 4 + share.epoch_uses.len()
            + 4 + unspent_powers.len() * 336
            + 4 + self.output.beaver_triples.len() * 144
            + 32; // domain integrity tag
        let mut out = SecretBuffer(Vec::with_capacity(exact_len));
        out.extend_from_slice(b"QSFTSRS1");
        out.extend_from_slice(&self.generation.to_be_bytes());
        out.extend_from_slice(&self.output.pk_seed_bytes);
        out.extend_from_slice(&share.party_id.to_be_bytes());
        out.extend_from_slice(&(share.params.tree_height as u32).to_be_bytes());
        out.extend_from_slice(&(share.params.winternitz_w as u32).to_be_bytes());
        out.extend_from_slice(&(share.params.num_chains as u32).to_be_bytes());
        out.extend_from_slice(&(share.params.target_sum as u32).to_be_bytes());
        out.extend_from_slice(&(share.committee.len() as u16).to_be_bytes());
        for &member in &share.committee {
            out.extend_from_slice(&member.to_be_bytes());
        }
        for &lane in &share.sk_seed_lanes {
            out.extend_from_slice(&lane.to_le_bytes());
        }
        for mac in &share.sk_seed_macs {
            for &m in mac {
                out.extend_from_slice(&m.to_le_bytes());
            }
        }
        for &lane in &share.sk_prf_lanes {
            out.extend_from_slice(&lane.to_le_bytes());
        }
        for mac in &share.sk_prf_macs {
            for &m in mac {
                out.extend_from_slice(&m.to_le_bytes());
            }
        }
        for &alpha in &share.bdoz_alpha_share {
            out.extend_from_slice(&alpha.to_le_bytes());
        }
        out.extend_from_slice(&share.local_salt_seed);
        out.extend_from_slice(&(share.pairwise_zero_seeds.len() as u16).to_be_bytes());
        for &(peer, ref seed) in &share.pairwise_zero_seeds {
            out.extend_from_slice(&peer.to_be_bytes());
            out.extend_from_slice(seed);
        }
        out.extend_from_slice(&(share.epoch_uses.len() as u32).to_be_bytes());
        out.extend_from_slice(&share.epoch_uses);
        out.extend_from_slice(&(unspent_powers.len() as u32).to_be_bytes());
        for tuple in unspent_powers {
            for wire in &tuple.powers {
                out.extend_from_slice(&wire.val_sh.to_le_bytes());
                out.extend_from_slice(&wire.mac[0].to_le_bytes());
                out.extend_from_slice(&wire.mac[1].to_le_bytes());
            }
        }
        out.extend_from_slice(&(self.output.beaver_triples.len() as u32).to_be_bytes());
        for triple in &self.output.beaver_triples {
            for idx in 0..3 {
                out.extend_from_slice(&triple.values[idx].to_le_bytes());
                out.extend_from_slice(&triple.macs[idx][0].to_le_bytes());
                out.extend_from_slice(&triple.macs[idx][1].to_le_bytes());
            }
        }
        let tag = cshake256_framed_32(b"QSAG.FTS.RESERVOIR.TAG.V1", &[&out]);
        out.extend_from_slice(&tag);
        debug_assert_eq!(out.len(), exact_len);
        Ok(out)
    }

    /// Rehydrate an activated reservoir serialized with [`Self::to_secret_bytes`].
    pub fn from_secret_bytes(bytes: &[u8]) -> Result<Self, ParallelSeededError> {
        let invalid = ParallelSeededError::InvalidThresholdParameters;
        if bytes.len() < 8 + 8 + 32 + 2 + 16 + 2 + 256 + 2 + 4 + 4 + 4 + 32
            || &bytes[..8] != b"QSFTSRS1"
        {
            return Err(invalid);
        }
        let body = &bytes[..bytes.len() - 32];
        let expected_tag = cshake256_framed_32(b"QSAG.FTS.RESERVOIR.TAG.V1", &[body]);
        if !ct_eq_bytes(&expected_tag, &bytes[bytes.len() - 32..]) {
            return Err(invalid);
        }
        let mut cursor = 8usize;
        let take = |cursor: &mut usize, len: usize| -> Result<&[u8], ParallelSeededError> {
            let end = cursor.checked_add(len).ok_or(invalid)?;
            let slice = body.get(*cursor..end).ok_or(invalid)?;
            *cursor = end;
            Ok(slice)
        };
        let read_u16 = |cursor: &mut usize| -> Result<u16, ParallelSeededError> {
            let b = take(cursor, 2)?;
            Ok(u16::from_be_bytes([b[0], b[1]]))
        };
        let read_u32 = |cursor: &mut usize| -> Result<u32, ParallelSeededError> {
            let b = take(cursor, 4)?;
            Ok(u32::from_be_bytes([b[0], b[1], b[2], b[3]]))
        };
        let read_u64 = |cursor: &mut usize| -> Result<u64, ParallelSeededError> {
            let b = take(cursor, 8)?;
            let mut arr = [0u8; 8];
            arr.copy_from_slice(b);
            Ok(u64::from_be_bytes(arr))
        };
        let read_u128_le = |cursor: &mut usize| -> Result<u128, ParallelSeededError> {
            let b = take(cursor, 16)?;
            let mut arr = [0u8; 16];
            arr.copy_from_slice(b);
            let v = u128::from_le_bytes(arr);
            ct_zeroize_bytes(&mut arr);
            Ok(v)
        };
        let read_bytes32 = |cursor: &mut usize| -> Result<[u8; 32], ParallelSeededError> {
            let b = take(cursor, 32)?;
            let mut arr = [0u8; 32];
            arr.copy_from_slice(b);
            Ok(arr)
        };

        let generation = read_u64(&mut cursor)?;
        let pk_seed_bytes = read_bytes32(&mut cursor)?;
        let party_id = read_u16(&mut cursor)?;
        let params = ParallelSeededParams {
            tree_height: read_u32(&mut cursor)? as usize,
            winternitz_w: read_u32(&mut cursor)? as usize,
            num_chains: read_u32(&mut cursor)? as usize,
            target_sum: read_u32(&mut cursor)? as usize,
        };
        params.validate()?;
        let committee_len = read_u16(&mut cursor)? as usize;
        if !(2..=255).contains(&committee_len) {
            return Err(invalid);
        }
        let mut committee = Vec::with_capacity(committee_len);
        for _ in 0..committee_len {
            committee.push(read_u16(&mut cursor)?);
        }
        if !committee.windows(2).all(|w| w[0] < w[1]) || !committee.contains(&party_id) {
            return Err(invalid);
        }
        let sk_seed_lanes = SecretBuffer([read_u128_le(&mut cursor)?, read_u128_le(&mut cursor)?]);
        let sk_seed_macs = SecretBuffer([
            [read_u128_le(&mut cursor)?, read_u128_le(&mut cursor)?],
            [read_u128_le(&mut cursor)?, read_u128_le(&mut cursor)?],
        ]);
        let sk_prf_lanes = SecretBuffer([read_u128_le(&mut cursor)?, read_u128_le(&mut cursor)?]);
        let sk_prf_macs = SecretBuffer([
            [read_u128_le(&mut cursor)?, read_u128_le(&mut cursor)?],
            [read_u128_le(&mut cursor)?, read_u128_le(&mut cursor)?],
        ]);
        let bdoz_alpha_share =
            SecretBuffer([read_u128_le(&mut cursor)?, read_u128_le(&mut cursor)?]);
        let local_salt_seed = SecretBytes::new(read_bytes32(&mut cursor)?);
        let pairwise_len = read_u16(&mut cursor)? as usize;
        if pairwise_len + 1 != committee_len {
            return Err(invalid);
        }
        let mut pairwise_zero_seeds: Vec<(u16, [u8; 32])> = Vec::with_capacity(pairwise_len);
        let mut expected_peers = committee.iter().copied().filter(|&id| id != party_id);
        for _ in 0..pairwise_len {
            let peer = read_u16(&mut cursor)?;
            if expected_peers.next() != Some(peer) {
                for (_, s) in &mut pairwise_zero_seeds {
                    ct_zeroize_bytes(s);
                }
                return Err(invalid);
            }
            let seed = SecretBytes::new(read_bytes32(&mut cursor)?);
            pairwise_zero_seeds.push((peer, *seed));
        }
        let epoch_uses_len = read_u32(&mut cursor)? as usize;
        let expected_leaves = 1usize << params.tree_height;
        if epoch_uses_len != expected_leaves {
            for (_, s) in &mut pairwise_zero_seeds {
                ct_zeroize_bytes(s);
            }
            return Err(invalid);
        }
        let epoch_uses_slice = take(&mut cursor, epoch_uses_len)?;
        if epoch_uses_slice.iter().any(|&u| u > 1) {
            for (_, s) in &mut pairwise_zero_seeds {
                ct_zeroize_bytes(s);
            }
            return Err(invalid);
        }
        let epoch_uses = epoch_uses_slice.to_vec();

        let unspent_powers_len = read_u32(&mut cursor)? as usize;
        if unspent_powers_len > DEFAULT_BEAVER_TRIPLE_POOL {
            for (_, s) in &mut pairwise_zero_seeds {
                ct_zeroize_bytes(s);
            }
            return Err(invalid);
        }
        let mut beaver_pool = Vec::with_capacity(unspent_powers_len);
        for _ in 0..unspent_powers_len {
            let mut powers: [AuthWire128; 7] = core::array::from_fn(|_| AuthWire128 {
                val_sh: 0,
                mac: [0; 2],
            });
            for wire in &mut powers {
                wire.val_sh = read_u128_le(&mut cursor)?;
                wire.mac[0] = read_u128_le(&mut cursor)?;
                wire.mac[1] = read_u128_le(&mut cursor)?;
            }
            beaver_pool.push(AuthenticatedPowerShare { powers });
        }

        let beaver_triples_len = read_u32(&mut cursor)? as usize;
        if beaver_triples_len > DEFAULT_BEAVER_TRIPLE_POOL {
            for (_, s) in &mut pairwise_zero_seeds {
                ct_zeroize_bytes(s);
            }
            return Err(invalid);
        }
        let mut beaver_triples = Vec::with_capacity(beaver_triples_len);
        for _ in 0..beaver_triples_len {
            let mut values = [0u128; 3];
            let mut macs = [[0u128; 2]; 3];
            for idx in 0..3 {
                values[idx] = read_u128_le(&mut cursor)?;
                macs[idx][0] = read_u128_le(&mut cursor)?;
                macs[idx][1] = read_u128_le(&mut cursor)?;
            }
            beaver_triples.push(ParallelSeededDkgBeaverShare { values, macs });
        }

        if cursor != body.len() {
            for (_, s) in &mut pairwise_zero_seeds {
                ct_zeroize_bytes(s);
            }
            return Err(invalid);
        }

        let share = ParallelSeededPartyShare {
            party_id,
            params,
            key_seed: pk_seed_bytes,
            committee,
            sk_seed_lanes: *sk_seed_lanes,
            sk_seed_macs: *sk_seed_macs,
            sk_prf_lanes: *sk_prf_lanes,
            sk_prf_macs: *sk_prf_macs,
            bdoz_alpha_share: *bdoz_alpha_share,
            local_salt_seed: *local_salt_seed,
            pairwise_zero_seeds,
            beaver_pool,
            beaver_cursor: 0,
            epoch_uses,
            poisoned: false,
            pending_openings: Vec::new(),
            #[cfg(test)]
            power_fault: false,
        };
        Ok(Self {
            output: ParallelSeededDkgOutput {
                pk_seed_bytes,
                share,
                beaver_triples,
            },
            generation,
        })
    }
    #[cfg(test)]
    pub(crate) fn first_mask_for_test(&self) -> u128 {
        self.output.share.beaver_pool[0].powers[0].val_sh
    }
    #[cfg(test)]
    pub(crate) fn corrupt_seed_for_test(&mut self) {
        self.output.share.sk_seed_lanes[0] ^= 1;
    }
    pub fn remaining_powers(&self) -> usize {
        self.output.share.beaver_pool.len() - self.output.share.beaver_cursor
    }
    /// Move ordinary Beaver triples out before refilling, if the caller needs them.
    pub fn take_beaver_triples(&mut self) -> Vec<ParallelSeededDkgBeaverShare> {
        core::mem::take(&mut self.output.beaver_triples)
    }
    /// Consume this reservoir and start a fresh, bounded ceremony. Unused tuples
    /// are deliberately discarded, never reused. All parties must agree on the
    /// session, counts and generation and supply fresh independent private entropy.
    /// Even a repeated caller session/entropy cannot repeat a previous generation's
    /// masks: the monotonically increasing generation is bound into the context.
    /// Any failure consumes the key; the driver must abort the whole ceremony.
    pub fn into_refill(
        self,
        session: [u8; 32],
        power_count: usize,
        beaver_count: usize,
        entropy: [u8; 32],
    ) -> Result<ParallelSeededDkgRefillState, ParallelSeededError> {
        let entropy = SecretBytes::new(entropy);
        let mut share = self.output.share;
        if share.poisoned
            || !share.pending_openings.is_empty()
            || power_count == 0
            || power_count > DEFAULT_BEAVER_TRIPLE_POOL
            || beaver_count > DEFAULT_BEAVER_TRIPLE_POOL
        {
            return Err(ParallelSeededError::InvalidThresholdParameters);
        }
        let generation = self
            .generation
            .checked_add(1)
            .ok_or(ParallelSeededError::InvalidThresholdParameters)?;
        let session = cshake256_framed_32(
            b"QSAG.DKG.REFILL.V1",
            &[&share.key_seed, &session, &generation.to_be_bytes()],
        );
        let state = ParallelSeededDkgRound1State::begin(
            ParallelSeededDkgConfig {
                params: share.params,
                roster: share.committee.clone(),
                session,
                power_count,
                beaver_count,
            },
            share.party_id,
            *entropy,
        )?;
        // Free/wipe the old pool before allocating the next one. Keep key shares,
        // authentication keys and the monotonic per-leaf burn state.
        share.beaver_pool = Vec::new();
        share.beaver_cursor = 0;
        Ok(ParallelSeededDkgRefillState {
            state,
            share,
            generation,
        })
    }
}

/// Per-party refill commitment state. Same authenticated/private transport
/// obligations as [`ParallelSeededDkgRound1State`].
pub struct ParallelSeededDkgRefillState {
    state: ParallelSeededDkgRound1State,
    share: ParallelSeededPartyShare,
    generation: u64,
}
impl ParallelSeededDkgRefillState {
    pub fn commitment(&self) -> ParallelSeededDkgRound1Commit {
        self.state.commitment()
    }
    pub fn open(
        &mut self,
        commits: &[ParallelSeededDkgRound1Commit],
    ) -> Result<ParallelSeededDkgRound2Open, ParallelSeededError> {
        self.state.open(commits)
    }
    pub fn private_packages(
        &mut self,
    ) -> Result<Vec<ParallelSeededDkgSharePackage>, ParallelSeededError> {
        self.state.private_packages()
    }
    pub fn finalize<T: ParallelSeededDkgProducts>(
        self,
        openings: &[ParallelSeededDkgRound2Open],
        packages: Vec<ParallelSeededDkgSharePackage>,
        backend: &mut T,
    ) -> Result<ParallelSeededDkgRefillUnverified, ParallelSeededError> {
        Ok(ParallelSeededDkgRefillUnverified {
            pending: finalize_dkg(self.state, openings, packages, backend, Some(self.share))?,
            generation: self.generation,
        })
    }
}

/// An unverified refill. Delegates every sacrifice and both committed MAC lanes
/// to the same implementation as initial setup; there is no unchecked install API.
pub struct ParallelSeededDkgRefillUnverified {
    pending: ParallelSeededDkgUnverifiedOutput,
    generation: u64,
}
impl ParallelSeededDkgRefillUnverified {
    pub fn check_commitment(&self) -> ParallelSeededDkgCheckCommit {
        self.pending.check_commitment()
    }
    pub fn reveal_check_coin(
        &mut self,
        commits: &[ParallelSeededDkgCheckCommit],
    ) -> Result<ParallelSeededDkgCheckCoin, ParallelSeededError> {
        self.pending.reveal_check_coin(commits)
    }
    pub fn masked_shares(
        &mut self,
        coins: &[ParallelSeededDkgCheckCoin],
    ) -> Result<ParallelSeededDkgCheckShares, ParallelSeededError> {
        self.pending.masked_shares(coins)
    }
    pub fn tag_commitment(
        &mut self,
        shares: &[ParallelSeededDkgCheckShares],
    ) -> Result<ParallelSeededDkgCheckTagCommit, ParallelSeededError> {
        self.pending.tag_commitment(shares)
    }
    pub fn open_tags(
        &mut self,
        commits: &[ParallelSeededDkgCheckTagCommit],
    ) -> Result<ParallelSeededDkgCheckTagOpen, ParallelSeededError> {
        self.pending.open_tags(commits)
    }
    pub fn activate(
        self,
        openings: &[ParallelSeededDkgCheckTagOpen],
    ) -> Result<ParallelSeededDkgReservoir, ParallelSeededError> {
        Ok(ParallelSeededDkgReservoir {
            output: self.pending.activate(openings)?,
            generation: self.generation,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reservoir_secret_bytes_roundtrip_and_tamper_refusal() {
        let accel = qsag_accel::CpuReferenceBackend::new();
        let params = ParallelSeededParams {
            tree_height: 2,
            winternitz_w: 3,
            num_chains: 4,
            target_sum: 4,
        };
        let setup = ParallelSeededThresholdSetup::trusted_dealer_setup_for_testing(
            params,
            2,
            [0x11; 32],
            [0x22; 32],
            &accel,
        )
        .unwrap();
        let pk = setup.pk;
        let public_tree_layers = setup.public_tree_layers;
        let mut reservoirs: Vec<ParallelSeededDkgReservoir> = setup
            .shares
            .into_iter()
            .map(|mut share| {
                share.beaver_pool.truncate(params.signing_power_count() * 2);
                let pk_seed_bytes = share.key_seed;
                ParallelSeededDkgReservoir::new(ParallelSeededDkgOutput {
                    pk_seed_bytes,
                    share,
                    beaver_triples: Vec::new(),
                })
                .unwrap()
            })
            .collect();

        let encoded: Vec<SecretVec<u8>> = reservoirs
            .iter()
            .map(|r| r.to_secret_bytes().unwrap())
            .collect();
        drop(reservoirs);

        // Tampered or truncated bytes must fail closed.
        let mut bad = encoded[0].0.clone();
        let last = bad.len() - 1;
        bad[last] ^= 0x01;
        assert!(ParallelSeededDkgReservoir::from_secret_bytes(&bad).is_err());
        assert!(ParallelSeededDkgReservoir::from_secret_bytes(&encoded[0][..24]).is_err());

        reservoirs = encoded
            .iter()
            .map(|raw| ParallelSeededDkgReservoir::from_secret_bytes(raw).unwrap())
            .collect();
        assert_eq!(
            reservoirs[0].remaining_powers(),
            params.signing_power_count() * 2
        );

        let mut restored_setup = ParallelSeededThresholdSetup {
            pk: pk.clone(),
            shares: reservoirs.into_iter().map(|r| r.output.share).collect(),
            public_tree_layers,
            #[cfg(test)]
            test_fault: None,
        };
        let mut log = InMemoryBurnLog::default();
        let sig = restored_setup
            .threshold_sign(0, b"persisted-reservoir-msg", [0x55; 32], &mut log, &accel)
            .unwrap();
        verify_parallel_seeded_fts(&pk, b"persisted-reservoir-msg", &sig, &accel).unwrap();
    }
}
