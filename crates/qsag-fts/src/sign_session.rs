//! Transport-facing signing and public leaf preparation. Each state exclusively
//! borrows one custodian. Transport supplies authenticated, consistent broadcasts.
use super::*;
use qsag_accel::CpuReferenceBackend;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParallelSeededSignMessage {
    Commitment {
        party_id: u16,
        session: [u8; 32],
        round: u32,
        digest: [u8; 32],
    },
    Opening {
        party_id: u16,
        session: [u8; 32],
        round: u32,
        values: Vec<u128>,
        salt: [u8; 32],
    },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParallelSeededSignResult {
    Signature(ParallelSeededSignature),
    Leaf { epoch: u32, digest: [u64; 4] },
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Randomizer,
    Chains,
    Leaf,
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum Phase {
    PowerCommit,
    PowerOpen,
    IntermediateMacCommit,
    IntermediateMacOpen,
    ValueCommit,
    ValueOpen,
    MacCommit,
    MacOpen,
    Complete,
    Aborted,
}
struct Job {
    state: [AuthWire128; 2],
    original: [AuthWire128; 2],
    tweak: (u128, u128),
    chain: u16,
    remaining: usize,
    step: u8,
    done: bool,
}

pub struct ParallelSeededSignSession<'a> {
    share: &'a mut ParallelSeededPartyShare,
    pk: ParallelSeededPublicKey,
    roster: Vec<u16>,
    session: [u8; 32],
    epoch: u32,
    msg: Vec<u8>,
    siblings: Vec<[u64; 4]>,
    mode: Mode,
    phase: Phase,
    sequence: u32,
    spn_round: usize,
    jobs: Vec<Job>,
    powers: Vec<AuthenticatedPowerShare>,
    masked: Vec<AuthWire128>,
    payload: Vec<u128>,
    commitments: Vec<(u16, [u8; 32])>,
    opened: Vec<u128>,
    randomizer: [u8; 32],
    grind_counter: u32,
    result: Option<ParallelSeededSignResult>,
    complete: bool,
}
impl Drop for ParallelSeededSignSession<'_> {
    fn drop(&mut self) {
        ct_zeroize_u128s(&mut self.payload);
        // Once MAC differences can have been sent, an interrupted check may have
        // exposed the authentication key. Retain custody bytes but quarantine
        // this authentication context until freshly authenticated preprocessing.
        if !self.complete && matches!(self.phase, Phase::IntermediateMacOpen | Phase::MacOpen) {
            self.share.poison();
        }
        self.share.pending_openings.clear();
        ct_zeroize_u128s(&mut self.opened);
    }
}
fn encode_values(values: &[u128]) -> Vec<u8> {
    let mut out = Vec::with_capacity(8 + values.len() * 16);
    out.extend_from_slice(&(values.len() as u64).to_be_bytes());
    for value in values {
        out.extend_from_slice(&value.to_le_bytes());
    }
    out
}
/// The public statement of one signing session. All parties must supply the same value.
#[derive(Clone, Copy, Debug)]
pub struct ParallelSeededSignRequest<'r> {
    /// Public key, authenticated by the caller.
    pub pk: &'r ParallelSeededPublicKey,
    pub epoch: u32,
    pub msg: &'r [u8],
    pub session_id: [u8; 32],
    /// Canonical ascending committee roster.
    pub roster: &'r [u16],
    /// Merkle authentication path of leaf `epoch`.
    pub siblings: &'r [[u64; 4]],
}
impl<'a> ParallelSeededSignSession<'a> {
    /// All parties must agree on the same canonical roster, key, message, epoch,
    /// use count and session identifier. Burn persistence completes before any
    /// secret wire is evaluated. The caller authenticates the supplied public key.
    pub fn begin(
        share: &'a mut ParallelSeededPartyShare,
        request: &ParallelSeededSignRequest<'_>,
        persistence: &mut impl LeafBurnPersistence,
    ) -> Result<Self, ParallelSeededError> {
        let ParallelSeededSignRequest {
            pk,
            epoch,
            msg,
            siblings,
            roster,
            ..
        } = *request;
        Self::validate(share, pk, epoch, roster)?;
        if siblings.len() != pk.params.tree_height {
            return Err(ParallelSeededError::InvalidAuthenticationPath);
        }
        let count = share.epoch_uses[epoch as usize];
        if count >= 1 {
            return Err(ParallelSeededError::EpochUseBudgetExhausted);
        }
        let needed = 2 * SPN_ROUNDS * (1 + pk.params.num_chains + pk.params.target_sum);
        if share.beaver_pool.len().saturating_sub(share.beaver_cursor) < needed {
            return Err(ParallelSeededError::BeaverPreprocessingExhausted);
        }
        persistence.burn_epoch_before_sign(&pk.pk_seed_bytes, share.party_id, epoch, count + 1)?;
        share.epoch_uses[epoch as usize] = count + 1;
        let mut state = Self::new(share, request, Mode::Randomizer, count + 1);
        let original = core::array::from_fn(|lane| AuthWire128 {
            val_sh: state.share.sk_prf_lanes[lane],
            mac: state.share.sk_prf_macs[lane],
        });
        let tweak = derive_rand_tweak(&pk.pk_seed_bytes, epoch, count + 1, msg);
        state.jobs.push(Job {
            state: original.clone(),
            original,
            tweak,
            chain: 0,
            remaining: 0,
            step: 0,
            done: false,
        });
        state.prepare_power()?;
        Ok(state)
    }
    /// Offline public-leaf computation using the same authenticated network.
    /// Opening endpoints does not reveal intermediate chain preimages. Prepare
    /// all leaves, then assemble the public tree; no full seed is reconstructed.
    pub fn begin_leaf_preparation(
        share: &'a mut ParallelSeededPartyShare,
        epoch: u32,
        session_id: [u8; 32],
        roster: &[u16],
    ) -> Result<Self, ParallelSeededError> {
        let pk = ParallelSeededPublicKey {
            params: share.params,
            pk_seed_bytes: share.key_seed,
            pk_seed_limbs: poseidon2_hash_limbs(
                0x5345_4544_3536_5633,
                &pack_bytes32_to_limbs56(&share.key_seed),
            ),
            merkle_root: [0; 4],
        };
        Self::validate(share, &pk, epoch, roster)?;
        let needed = 2 * SPN_ROUNDS * pk.params.num_chains * pk.params.winternitz_w;
        if share.beaver_pool.len().saturating_sub(share.beaver_cursor) < needed {
            return Err(ParallelSeededError::BeaverPreprocessingExhausted);
        }
        let request = ParallelSeededSignRequest {
            pk: &pk,
            epoch,
            msg: &[],
            session_id,
            roster,
            siblings: &[],
        };
        let mut state = Self::new(share, &request, Mode::Leaf, 0);
        let targets = vec![(pk.params.winternitz_w - 1) as u8; pk.params.num_chains];
        state.seed_jobs(&targets);
        state.prepare_power()?;
        Ok(state)
    }
    fn validate(
        share: &ParallelSeededPartyShare,
        pk: &ParallelSeededPublicKey,
        epoch: u32,
        roster: &[u16],
    ) -> Result<(), ParallelSeededError> {
        pk.params.validate()?;
        if share.poisoned {
            return Err(ParallelSeededError::Poisoned);
        }
        if share.params != pk.params
            || share.key_seed != pk.pk_seed_bytes
            || roster != share.committee
            || roster.len() < 2
            || roster.windows(2).any(|w| w[0] >= w[1])
            || !roster.contains(&share.party_id)
            || share.epoch_uses.len() != (1usize << pk.params.tree_height)
            || pk.pk_seed_limbs
                != poseidon2_hash_limbs(
                    0x5345_4544_3536_5633,
                    &pack_bytes32_to_limbs56(&pk.pk_seed_bytes),
                )
        {
            return Err(ParallelSeededError::InvalidThresholdParameters);
        }
        if epoch as usize >= share.epoch_uses.len() {
            return Err(ParallelSeededError::EpochOutOfRange);
        }
        Ok(())
    }
    fn new(
        share: &'a mut ParallelSeededPartyShare,
        request: &ParallelSeededSignRequest<'_>,
        mode: Mode,
        count: u8,
    ) -> Self {
        let ParallelSeededSignRequest {
            pk,
            epoch,
            msg,
            session_id: sid,
            roster,
            siblings,
        } = *request;
        let mut context = Vec::new();
        for &id in roster {
            context.extend_from_slice(&id.to_be_bytes());
        }
        for limb in pk.merkle_root {
            context.extend_from_slice(&limb.to_le_bytes());
        }
        for value in [
            pk.params.tree_height,
            pk.params.winternitz_w,
            pk.params.num_chains,
            pk.params.target_sum,
        ] {
            context.extend_from_slice(&(value as u64).to_be_bytes());
        }
        let session = cshake256_framed_32(
            b"QSAG.PSFTS.DISTRIBUTED.V4",
            &[
                &sid,
                &pk.pk_seed_bytes,
                &epoch.to_be_bytes(),
                &[count, if mode == Mode::Leaf { 1 } else { 0 }],
                msg,
                &context,
            ],
        );
        Self {
            share,
            pk: pk.clone(),
            roster: roster.to_vec(),
            session,
            epoch,
            msg: msg.to_vec(),
            siblings: siblings.to_vec(),
            mode,
            phase: Phase::PowerCommit,
            sequence: 0,
            spn_round: 0,
            jobs: Vec::new(),
            powers: Vec::new(),
            masked: Vec::new(),
            payload: Vec::new(),
            commitments: Vec::new(),
            opened: Vec::new(),
            randomizer: [0; 32],
            grind_counter: 0,
            result: None,
            complete: false,
        }
    }
    fn salt(&self) -> [u8; 32] {
        cshake256_framed_32(
            b"QSAG.PSFTS.ROUND_SALT.V4",
            &[
                &self.share.local_salt_seed,
                &self.session,
                &self.sequence.to_be_bytes(),
            ],
        )
    }
    fn own_commitment(&self) -> [u8; 32] {
        commit_mpc_broadcast(
            &self.session,
            self.sequence,
            self.share.party_id,
            &encode_values(&self.payload),
            &self.salt(),
        )
    }
    pub fn outbound(&self) -> Result<ParallelSeededSignMessage, ParallelSeededError> {
        if self.share.poisoned || self.phase == Phase::Aborted {
            return Err(ParallelSeededError::Poisoned);
        }
        match self.phase {
            Phase::PowerCommit
            | Phase::IntermediateMacCommit
            | Phase::ValueCommit
            | Phase::MacCommit => Ok(ParallelSeededSignMessage::Commitment {
                party_id: self.share.party_id,
                session: self.session,
                round: self.sequence,
                digest: self.own_commitment(),
            }),
            Phase::PowerOpen | Phase::IntermediateMacOpen | Phase::ValueOpen | Phase::MacOpen => {
                Ok(ParallelSeededSignMessage::Opening {
                    party_id: self.share.party_id,
                    session: self.session,
                    round: self.sequence,
                    values: self.payload.clone(),
                    salt: self.salt(),
                })
            }
            Phase::Complete | Phase::Aborted => {
                Err(ParallelSeededError::SignatureVerificationFailed)
            }
        }
    }
    /// A complete authenticated broadcast set advances exactly one phase. Any
    /// malformed set, reordered phase, commitment failure or MAC failure poisons
    /// this session immediately. The burned epoch and consumed preprocessing stay spent;
    /// an unauthenticated abort never erases long-term custody material.
    pub fn advance(
        &mut self,
        messages: &[ParallelSeededSignMessage],
    ) -> Result<(), ParallelSeededError> {
        if self.share.poisoned || self.phase == Phase::Aborted {
            return Err(ParallelSeededError::Poisoned);
        }
        let result = self.advance_inner(messages);
        if result.is_err() {
            if matches!(result, Err(ParallelSeededError::BdozMacCheckFailed)) {
                self.share.poison();
            }
            self.phase = Phase::Aborted;
            ct_zeroize_u128s(&mut self.payload);
            self.share.pending_openings.clear();
        }
        result
    }
    fn advance_inner(
        &mut self,
        messages: &[ParallelSeededSignMessage],
    ) -> Result<(), ParallelSeededError> {
        if messages.len() != self.roster.len() {
            return Err(ParallelSeededError::BdozMacCheckFailed);
        }
        if matches!(
            self.phase,
            Phase::PowerCommit
                | Phase::IntermediateMacCommit
                | Phase::ValueCommit
                | Phase::MacCommit
        ) {
            let mut commits = Vec::with_capacity(messages.len());
            for &id in &self.roster {
                let mut matching=messages.iter().filter(|m|matches!(m,ParallelSeededSignMessage::Commitment {party_id,..} if *party_id==id));
                let m = matching
                    .next()
                    .ok_or(ParallelSeededError::BdozMacCheckFailed)?;
                if matching.next().is_some() {
                    return Err(ParallelSeededError::BdozMacCheckFailed);
                }
                if let ParallelSeededSignMessage::Commitment {
                    session,
                    round,
                    digest,
                    ..
                } = m
                {
                    if *session != self.session
                        || *round != self.sequence
                        || (id == self.share.party_id && *digest != self.own_commitment())
                    {
                        return Err(ParallelSeededError::CommitmentMismatch { party_id: id });
                    }
                    commits.push((id, *digest));
                }
            }
            self.commitments = commits;
            self.phase = match self.phase {
                Phase::PowerCommit => Phase::PowerOpen,
                Phase::ValueCommit => Phase::ValueOpen,
                Phase::IntermediateMacCommit => Phase::IntermediateMacOpen,
                _ => Phase::MacOpen,
            };
            return Ok(());
        }
        if self.phase == Phase::Complete {
            return Err(ParallelSeededError::SignatureVerificationFailed);
        }
        let mut values = vec![0u128; self.payload.len()];
        for &(id, digest) in &self.commitments {
            let mut matching = messages.iter().filter(
                |m| matches!(m,ParallelSeededSignMessage::Opening {party_id,..} if *party_id==id),
            );
            let m = matching
                .next()
                .ok_or(ParallelSeededError::BdozMacCheckFailed)?;
            if matching.next().is_some() {
                return Err(ParallelSeededError::BdozMacCheckFailed);
            }
            if let ParallelSeededSignMessage::Opening {
                session,
                round,
                values: part,
                salt,
                ..
            } = m
            {
                if *session != self.session
                    || *round != self.sequence
                    || part.len() != values.len()
                    || !ct_eq_bytes(
                        &digest,
                        &commit_mpc_broadcast(
                            &self.session,
                            self.sequence,
                            id,
                            &encode_values(part),
                            salt,
                        ),
                    )
                {
                    return Err(ParallelSeededError::CommitmentMismatch { party_id: id });
                }
                for (sum, &value) in values.iter_mut().zip(part) {
                    *sum ^= value;
                }
            }
        }
        self.sequence = self
            .sequence
            .checked_add(1)
            .ok_or(ParallelSeededError::BdozMacCheckFailed)?;
        match self.phase {
            Phase::PowerOpen => self.apply_open_powers(&values),
            Phase::ValueOpen => self.prepare_mac(values),
            Phase::IntermediateMacOpen => {
                if values.iter().any(|&v| v != 0) {
                    return Err(ParallelSeededError::BdozMacCheckFailed);
                }
                self.share.pending_openings.clear();
                ct_zeroize_u128s(&mut self.payload);
                self.payload = self
                    .jobs
                    .iter()
                    .flat_map(|j| j.state.iter().map(|w| w.val_sh))
                    .collect();
                self.phase = Phase::ValueCommit;
                Ok(())
            }
            Phase::MacOpen => {
                if values != [0, 0] {
                    return Err(ParallelSeededError::BdozMacCheckFailed);
                }
                self.share.pending_openings.clear();
                self.after_mac()
            }
            _ => Err(ParallelSeededError::BdozMacCheckFailed),
        }
    }
    fn seed_jobs(&mut self, targets: &[u8]) {
        self.jobs = targets
            .iter()
            .enumerate()
            .map(|(chain, &target)| {
                let original = core::array::from_fn(|lane| AuthWire128 {
                    val_sh: self.share.sk_seed_lanes[lane],
                    mac: self.share.sk_seed_macs[lane],
                });
                Job {
                    state: original.clone(),
                    original,
                    tweak: derive_seed_tweak(&self.pk.pk_seed_bytes, self.epoch, chain as u16),
                    chain: chain as u16,
                    remaining: target as usize,
                    step: 0,
                    done: false,
                }
            })
            .collect();
        self.spn_round = 0;
    }
    fn prepare_power(&mut self) -> Result<(), ParallelSeededError> {
        self.masked.clear();
        self.powers.clear();
        ct_zeroize_u128s(&mut self.payload);
        self.payload.clear();
        let party = if self.share.party_id == self.roster[0] {
            0
        } else {
            1
        };
        for job in self.jobs.iter_mut().filter(|j| !j.done) {
            let rc = round_constants(job.tweak.0, job.tweak.1, self.spn_round);
            for (lane, wire) in job.state.iter_mut().enumerate() {
                *wire = auth_add_pub_const(
                    party,
                    self.share.bdoz_alpha_share,
                    wire,
                    if lane == 0 { rc.0 } else { rc.1 },
                );
                let source = self
                    .share
                    .beaver_pool
                    .get_mut(self.share.beaver_cursor)
                    .ok_or(ParallelSeededError::BeaverPreprocessingExhausted)?;
                let power = core::mem::replace(
                    source,
                    AuthenticatedPowerShare {
                        powers: core::array::from_fn(|_| AuthWire128 {
                            val_sh: 0,
                            mac: [0; 2],
                        }),
                    },
                );
                self.share.beaver_cursor += 1;
                let masked = auth_xor(wire, &power.powers[0]);
                self.payload.push(masked.val_sh);
                self.masked.push(masked);
                self.powers.push(power);
            }
        }
        self.phase = Phase::PowerCommit;
        Ok(())
    }
    fn apply_open_powers(&mut self, values: &[u128]) -> Result<(), ParallelSeededError> {
        let first = self.share.party_id == self.roster[0];
        for (&opened, wire) in values.iter().zip(&self.masked) {
            self.share.pending_openings.push((opened, wire.clone()));
        }
        let mut outputs = self
            .powers
            .iter()
            .zip(values)
            .map(|(power, &d)| apply_power(power, d, self.share.bdoz_alpha_share, first));
        for job in self.jobs.iter_mut().filter(|j| !j.done) {
            let x = outputs
                .next()
                .ok_or(ParallelSeededError::BdozMacCheckFailed)?;
            let y = outputs
                .next()
                .ok_or(ParallelSeededError::BdozMacCheckFailed)?;
            job.state = [
                auth_xor(&x, &auth_scale_const(&y, GF128_MDS_A)),
                auth_xor(&y, &auth_scale_const(&x, GF128_MDS_B)),
            ];
        }
        self.spn_round += 1;
        if self.spn_round == SPN_ROUNDS {
            self.spn_round = 0;
            for job in self.jobs.iter_mut().filter(|j| !j.done) {
                for (wire, original) in job.state.iter_mut().zip(&job.original) {
                    *wire = auth_xor(wire, original);
                }
                if job.remaining == 0 {
                    job.done = true;
                } else {
                    job.remaining -= 1;
                    job.original = job.state.clone();
                    job.tweak =
                        derive_chain_tweak(&self.pk.pk_seed_bytes, self.epoch, job.chain, job.step);
                    job.step += 1;
                }
            }
        }
        if self.jobs.iter().all(|j| j.done) {
            self.prepare_intermediate_mac();
            self.powers.clear();
            self.masked.clear();
            self.phase = Phase::IntermediateMacCommit;
            Ok(())
        } else {
            self.prepare_power()
        }
    }
    fn prepare_intermediate_mac(&mut self) {
        // No output value is read or encoded before every intermediate MAC passes.
        let values: Vec<_> = self
            .share
            .pending_openings
            .iter()
            .map(|(v, _)| *v)
            .collect();
        let digest = cshake256_framed_32(
            b"QSAG.PSFTS.INTERMEDIATE.V5",
            &[
                &self.session,
                &self.sequence.to_be_bytes(),
                &encode_values(&values),
            ],
        );
        ct_zeroize_u128s(&mut self.payload);
        self.payload.clear();
        for (index, (value, wire)) in self.share.pending_openings.iter().enumerate() {
            let mut sigma = core::array::from_fn::<_, 2, _>(|lane| {
                wire.mac[lane] ^ gf2_128_mul(self.share.bdoz_alpha_share[lane], *value)
            });
            for (_, seed) in &self.share.pairwise_zero_seeds {
                let mut bytes = cshake256_framed_32(
                    b"QSAG.PSFTS.INTERMEDIATE.ZERO.V5",
                    &[seed, &digest, &(index as u64).to_be_bytes()],
                );
                let zero = bytes32_to_lanes(&bytes);
                sigma[0] ^= zero.0;
                sigma[1] ^= zero.1;
                ct_zeroize_bytes(&mut bytes);
            }
            self.payload.extend_from_slice(&sigma);
            ct_zeroize_u128s(&mut sigma);
        }
    }
    fn prepare_mac(&mut self, opened: Vec<u128>) -> Result<(), ParallelSeededError> {
        let mut values = opened.clone();
        values.extend(self.share.pending_openings.iter().map(|(value, _)| *value));
        let digest = cshake256_framed_32(
            b"QSAG.PSFTS.BATCH_VALUES.V4",
            &[
                &self.session,
                &self.sequence.to_be_bytes(),
                &encode_values(&values),
            ],
        );
        let wires = self
            .jobs
            .iter()
            .flat_map(|job| job.state.iter())
            .chain(self.share.pending_openings.iter().map(|(_, wire)| wire));
        let mut sigma = [0u128; 2];
        for (index, (wire, &value)) in wires.zip(&values).enumerate() {
            let random = cshake256_framed_32(
                b"QSAG.PSFTS.BATCH_WEIGHT.V4",
                &[&digest, &(index as u64).to_be_bytes()],
            );
            let weight = bytes32_to_lanes(&random);
            for (lane, sum) in sigma.iter_mut().enumerate() {
                *sum ^= gf2_128_mul(
                    if lane == 0 { weight.0 } else { weight.1 },
                    wire.mac[lane] ^ gf2_128_mul(self.share.bdoz_alpha_share[lane], value),
                );
            }
        }
        for (_, seed) in &self.share.pairwise_zero_seeds {
            let mut bytes =
                cshake256_framed_32(b"QSAG.PSFTS.BATCH_ZERO.V4", &[seed, &self.session, &digest]);
            let zero = bytes32_to_lanes(&bytes);
            sigma[0] ^= zero.0;
            sigma[1] ^= zero.1;
            ct_zeroize_bytes(&mut bytes);
        }
        ct_zeroize_u128s(&mut self.payload);
        self.payload = sigma.to_vec();
        ct_zeroize_u128s(&mut sigma);
        self.opened = opened;
        self.phase = Phase::MacCommit;
        Ok(())
    }
    fn after_mac(&mut self) -> Result<(), ParallelSeededError> {
        if self.mode == Mode::Randomizer {
            self.randomizer = lanes_to_bytes32(self.opened[0], self.opened[1]);
            let mut chosen = None;
            for counter in 0..1_000_000 {
                if let Some(offsets) = derive_sum_constrained_offsets(
                    &self.pk.params,
                    &self.pk.pk_seed_bytes,
                    &self.pk.merkle_root,
                    self.epoch,
                    &self.randomizer,
                    &self.msg,
                    counter,
                ) {
                    chosen = Some((counter, offsets));
                    break;
                }
            }
            let (counter, offsets) = chosen.ok_or(ParallelSeededError::GrindingExhausted)?;
            self.grind_counter = counter;
            self.mode = Mode::Chains;
            self.seed_jobs(&offsets);
            self.prepare_power()
        } else {
            let nodes: Vec<_> = self
                .opened
                .as_chunks::<2>()
                .0
                .iter()
                .map(|pair| lanes_to_bytes32(pair[0], pair[1]))
                .collect();
            self.result = Some(if self.mode == Mode::Leaf {
                ParallelSeededSignResult::Leaf {
                    epoch: self.epoch,
                    digest: hash_epoch_endpoints_poseidon2(
                        &self.pk.pk_seed_limbs,
                        self.epoch,
                        &nodes,
                    ),
                }
            } else {
                let sig = ParallelSeededSignature {
                    epoch: self.epoch,
                    randomizer: self.randomizer,
                    grind_counter: self.grind_counter,
                    chain_nodes: nodes,
                    merkle_siblings: self.siblings.clone(),
                };
                verify_parallel_seeded_fts(&self.pk, &self.msg, &sig, &CpuReferenceBackend)?;
                ParallelSeededSignResult::Signature(sig)
            });
            self.complete = true;
            self.phase = Phase::Complete;
            Ok(())
        }
    }
    #[cfg(test)]
    pub(crate) fn alter_value_share_for_test(&mut self) -> bool {
        if self.phase != Phase::ValueCommit {
            return false;
        }
        self.payload[0] ^= 1;
        true
    }
    pub fn result(&self) -> Option<&ParallelSeededSignResult> {
        self.result.as_ref()
    }
}

/// Public Merkle layers, from leaves through the root.
pub type ParallelSeededMerkleLayers = Vec<Vec<[u64; 4]>>;

/// Assemble a public tree from individually authenticated leaf results in epoch order.
pub fn assemble_parallel_seeded_public_key(
    params: ParallelSeededParams,
    key_seed: [u8; 32],
    leaves: &[[u64; 4]],
) -> Result<(ParallelSeededPublicKey, ParallelSeededMerkleLayers), ParallelSeededError> {
    params.validate()?;
    if leaves.len() != 1usize << params.tree_height {
        return Err(ParallelSeededError::InvalidAuthenticationPath);
    }
    let pk_seed_limbs =
        poseidon2_hash_limbs(0x5345_4544_3536_5633, &pack_bytes32_to_limbs56(&key_seed));
    let mut layers = vec![leaves.to_vec()];
    for level in 0..params.tree_height {
        let children = layers
            .last()
            .ok_or(ParallelSeededError::InvalidAuthenticationPath)?;
        let mut parents = vec![[0; 4]; children.len() / 2];
        CpuReferenceBackend
            .try_merkle_layer_poseidon2(children, &pk_seed_limbs, level as u32, &mut parents)
            .map_err(|_| ParallelSeededError::InvalidAuthenticationPath)?;
        layers.push(parents);
    }
    let pk = ParallelSeededPublicKey {
        params,
        pk_seed_bytes: key_seed,
        pk_seed_limbs,
        merkle_root: layers[params.tree_height][0],
    };
    Ok((pk, layers))
}

#[cfg(test)]
mod release_barrier_tests {
    use super::*;
    #[test]
    fn last_power_fault_never_reaches_output_commitment() {
        let accel = CpuReferenceBackend;
        let mut setup = ParallelSeededThresholdSetup::trusted_dealer_setup_for_testing(
            ParallelSeededParams {
                tree_height: 1,
                winternitz_w: 2,
                num_chains: 2,
                target_sum: 1,
            },
            2,
            [11; 32],
            [12; 32],
            &accel,
        )
        .unwrap();
        let mut burn = InMemoryBurnLog::default();
        let siblings = [setup.public_tree_layers[0][1]];
        let roster: Vec<_> = setup.shares.iter().map(|s| s.party_id).collect();
        let mut sessions: Vec<_> = setup
            .shares
            .iter_mut()
            .map(|s| {
                ParallelSeededSignSession::begin(
                    s,
                    &ParallelSeededSignRequest {
                        pk: &setup.pk,
                        epoch: 0,
                        msg: b"fault",
                        session_id: [13; 32],
                        roster: &roster,
                        siblings: &siblings,
                    },
                    &mut burn,
                )
                .unwrap()
            })
            .collect();
        let mut injected = false;
        let mut rejected = false;
        for _ in 0..110 {
            assert!(
                sessions
                    .iter()
                    .all(|s| s.phase != Phase::ValueCommit && s.phase != Phase::ValueOpen)
            );
            if !injected && sessions[0].phase == Phase::PowerCommit && sessions[0].spn_round == 47 {
                sessions[0].payload[0] ^= 1;
                injected = true;
            }
            let messages: Vec<_> = sessions.iter().map(|s| s.outbound().unwrap()).collect();
            for session in &mut sessions {
                if let Err(error) = session.advance(&messages) {
                    assert_eq!(error, ParallelSeededError::BdozMacCheckFailed);
                    assert!(session.result().is_none());
                    rejected = true;
                }
            }
            if rejected {
                break;
            }
        }
        assert!(injected && rejected);
        drop(sessions);
        assert!(setup.shares.iter().all(|s| s.sk_seed_lanes != [0; 2]));
    }
}
