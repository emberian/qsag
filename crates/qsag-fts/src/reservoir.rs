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
    pub fn share_mut(&mut self) -> &mut ParallelSeededPartyShare {
        self.output.share_mut()
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
