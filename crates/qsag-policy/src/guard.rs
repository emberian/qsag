use super::*;
use qsag_verified::{
    ConsumingOpeningGuard2Lane, OpeningReleasePermit, StatefulVelocityGuard, VelocitySpendRequest,
};

/// Authority-approved transition of one provisioned policy's velocity window.
/// The previous epoch is MAC-bound so an authorization cannot be reused after
/// another transition. Issuers must enforce their window/time policy before minting.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WindowAdvanceAuthorization {
    pub new_window_epoch: u64,
    pub mac: [u8; 32],
}

impl WindowAdvanceAuthorization {
    pub fn new(
        authority_key: &[u8; 32],
        policy_id: &[u8; 32],
        prev_epoch: u64,
        new_window_epoch: u64,
    ) -> Self {
        Self {
            new_window_epoch,
            mac: cshake256_framed_32(
                b"QSAG.POLICY.WINDOW_ADVANCE/v1",
                &[
                    authority_key,
                    policy_id,
                    &prev_epoch.to_be_bytes(),
                    &new_window_epoch.to_be_bytes(),
                ],
            ),
        }
    }
}

pub(crate) struct WindowAuthority {
    pub(crate) policy_id: [u8; 32],
    pub(crate) key: [u8; 32],
}
impl Drop for WindowAuthority {
    fn drop(&mut self) {
        wipe(&mut self.key);
    }
}

/// Per-signer Eurocrypt-2011 pairwise BDOZ GF($2^{128}$) policy guard secret share:
/// - Private MAC key seed $\alpha_i \in \mathbb{F}_{2^{128}}^2$ deriving independent per-`(peer, slot)`
///   MAC keys $\alpha_{i \leftarrow j, s}$ so aborting one session never leaks future-slot keys,
/// - Private pairwise PRG zero-share seeds $k_{\min(i,j),\max(i,j)}$ ONLY for peers $j \neq i$,
/// - Preprocessed pairwise BDOZ correlations $(r_{i, s}, M_{i \to j, s}, K_{i \leftarrow j, s})$
///   with monotonic single-use slot latch (`Cell<usize>`),
/// - Durable authoritative velocity ledger: `current_window_id`, `accumulated_window_spend`,
///   and the replay sets `burned_intent_nonces` and `burned_sessions`. Each set is a sorted
///   `Vec` of at most `replay_capacity` entries that never evicts: a full set refuses new
///   intents (`ReplayWindowExhausted`). Entries leave only when the window advances or when
///   `compact_monotone_replay_floor` raises the watermark that burns everything at or below it,
/// - `<REDACTED>` `fmt::Debug` and `write_volatile` `Drop`.
pub struct PolicySignerGuardShare {
    pub party_id: u16,
    pub(crate) bdoz_alpha_share: [u128; 2],
    pub(crate) local_salt_seed: [u8; 32],
    pub(crate) pairwise_zero_seeds: Vec<(u16, [u8; 32])>,
    pub(crate) preproc_r: Vec<[u128; 2]>,
    pub(crate) preproc_outgoing_macs: Vec<(u16, Vec<[u128; 2]>)>,
    pub(crate) preproc_incoming_keys: Vec<(u16, Vec<[u128; 2]>)>,
    pub(crate) consumed_peer_slots: Vec<(u16, Vec<u64>)>,
    pub(crate) next_slot: Cell<usize>,
    pub(crate) poisoned: bool,
    pub(crate) enrolled_party_id: u16,
    pub(crate) active_phase: Option<(usize, u8)>,
    pub(crate) current_window_id: u64,
    pub(crate) accumulated_window_spend: u128,
    pub(crate) replay_capacity: usize,
    pub(crate) burned_intent_nonces: Vec<[u8; 32]>,
    pub(crate) min_nonce_watermark: Option<[u8; 32]>,
    pub(crate) burned_sessions: Vec<[u8; 32]>,
    pub(crate) min_session_watermark: Option<[u8; 32]>,
    pub(crate) require_authenticated_initiator: bool,
    pub(crate) window_authority: Option<WindowAuthority>,
    pub(crate) durable_key_id: [u8; 32],
    pub(crate) durable_generation: Cell<u64>,
    /// Extracted velocity guard retained across approvals, rotations and restores. It is
    /// pinned to a cap on first use; `velocity_generation` is its monotone request nonce.
    pub(crate) verified_velocity: Option<StatefulVelocityGuard>,
    pub(crate) velocity_generation: u64,
}

/// A verified guard for `window` and `cap` holding `spent`, with request nonce `generation`
/// (at least 1 once anything was spent). `None` if `spent` exceeds `cap`.
pub(crate) fn rebuild_verified_velocity(
    window: u64,
    cap: u128,
    pin: [u8; 32],
    generation: u64,
    spent: u128,
) -> Option<(StatefulVelocityGuard, u64)> {
    let guard = StatefulVelocityGuard::new_window(window, cap, pin, pin);
    if spent == 0 && generation == 0 {
        return Some((guard, 0));
    }
    let nonce = generation.max(1);
    let (guard, result) = guard.authorize_spend(VelocitySpendRequest {
        window_id: window,
        nonce,
        amount_units: spent,
        policy_pin: pin,
        authority_pin: pin,
    });
    result.ok().map(|_| (guard, nonce))
}

/// An independent guard in the state of `guard`, reached through the verified transitions
/// alone. `StatefulVelocityGuard` is affine, so this is how a spend is decided without
/// advancing the retained guard. `None` if `guard` is in a state those transitions cannot
/// reach.
pub(crate) fn replay_verified_velocity(
    guard: &StatefulVelocityGuard,
) -> Option<StatefulVelocityGuard> {
    let fresh = StatefulVelocityGuard::new_window(
        guard.window_id(),
        guard.cap_units(),
        guard.policy_pin(),
        guard.authority_pin(),
    );
    if guard.last_nonce() == 0 {
        return (guard.spent_units() == 0).then_some(fresh);
    }
    let (replayed, result) = fresh.authorize_spend(VelocitySpendRequest {
        window_id: guard.window_id(),
        nonce: guard.last_nonce(),
        amount_units: guard.spent_units(),
        policy_pin: guard.policy_pin(),
        authority_pin: guard.authority_pin(),
    });
    result.ok().map(|_| replayed)
}

/// A spend one signer guard's verified guard accepted, not yet installed. Built only by
/// `PolicySignerGuardShare::prepare_approved_intent` and consumed by
/// `commit_approved_intent`, which cannot fail.
pub(crate) struct PreparedGuardSpend {
    verified: StatefulVelocityGuard,
    generation: u64,
    spend: u128,
    nonce: [u8; 32],
    session_id: [u8; 32],
}

impl fmt::Debug for PolicySignerGuardShare {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PolicySignerGuardShare")
            .field("party_id", &self.party_id)
            .field("current_window_id", &self.current_window_id)
            .field("accumulated_window_spend", &self.accumulated_window_spend)
            .field("bdoz_alpha_share", &"<REDACTED>")
            .field("pairwise_zero_seeds", &"<REDACTED>")
            .finish()
    }
}

pub(crate) fn derive_peer_slot_alpha(
    alpha_root: &[u128; 2],
    peer_id: u16,
    peer_slot: usize,
) -> SecretBuffer<[u128; 2]> {
    let root_bytes = SecretBuffer(policy_pair_bytes(alpha_root));
    let raw = secret_digest(
        b"QSAG.POLICY.PEER_SLOT_ALPHA.V1",
        &[
            &*root_bytes,
            &peer_id.to_be_bytes(),
            &(peer_slot as u64).to_be_bytes(),
        ],
    );
    SecretBuffer(policy_pair(&raw))
}

impl PolicySignerGuardShare {
    /// Set the bounded replay history capacity without discarding any burned identifiers.
    /// Persist a checkpoint after changing this operational limit.
    pub fn set_replay_capacity(&mut self, capacity: usize) -> Result<(), PolicyViolation> {
        if capacity == 0
            || capacity > MAX_POLICY_CAPACITY
            || capacity
                < self
                    .burned_intent_nonces
                    .len()
                    .max(self.burned_sessions.len())
        {
            return Err(PolicyViolation::ReplayWindowExhausted);
        }
        self.replay_capacity = capacity;
        Ok(())
    }

    /// Trusted provisioning, before using the guard: pin an application policy ID
    /// and its authority key. The ID must uniquely identify the policy/ledger.
    /// Cannot replace an authority or enable resets after spending has started.
    /// Provision identically before restoring a durable checkpoint.
    pub fn with_window_authority(
        mut self,
        policy_id: [u8; 32],
        mut key: [u8; 32],
    ) -> Result<Self, PolicyViolation> {
        if self.window_authority.is_some()
            || self.next_slot.get() != 0
            || self.current_window_id != 0
            || self.accumulated_window_spend != 0
            || self.velocity_generation != 0
            || self.active_phase.is_some()
            || self.poisoned
        {
            wipe(&mut key);
            return Err(PolicyViolation::IntentBindingMismatch);
        }
        // The verified guard is pinned to the key ID, which changes below.
        self.verified_velocity = None;
        // Durable snapshots cannot be restored under different authority provisioning.
        self.durable_key_id = cshake256_framed_32(
            b"QSAG.POLICY.WINDOW_KEY/v1",
            &[&self.durable_key_id, &policy_id, &key],
        );
        self.window_authority = Some(WindowAuthority { policy_id, key });
        wipe(&mut key);
        Ok(self)
    }

    pub const fn current_window_id(&self) -> u64 {
        self.current_window_id
    }

    pub const fn accumulated_window_spend(&self) -> u128 {
        self.accumulated_window_spend
    }

    pub const fn is_poisoned(&self) -> bool {
        self.poisoned
    }

    /// Every constructor sets the requirement and a checkpoint restore can only keep or
    /// raise it; only this crate's own tests can waive it.
    #[cfg(test)]
    pub(crate) fn set_require_authenticated_initiator(&mut self, required: bool) {
        self.require_authenticated_initiator = required;
    }

    pub fn is_nonce_burned(&self, nonce: &[u8; 32]) -> bool {
        let mut hit = self
            .min_nonce_watermark
            .is_some_and(|floor| *nonce <= floor);
        for b in &self.burned_intent_nonces {
            hit |= ct_eq_bytes(b, nonce);
        }
        hit
    }

    pub fn is_session_burned(&self, session_id: &[u8; 32]) -> bool {
        let mut hit = self
            .min_session_watermark
            .is_some_and(|floor| *session_id <= floor);
        for b in &self.burned_sessions {
            hit |= ct_eq_bytes(b, session_id);
        }
        hit
    }

    /// Roll the guard into a strictly newer velocity window (`next_window_id > current_window_id`),
    /// resetting spend and replay sets. Every intent binds its window ID; old-window
    /// intents remain invalid after rotation. Each window admits the configured number of retained intents.
    pub fn advance_velocity_window(
        &mut self,
        authorization: &WindowAdvanceAuthorization,
    ) -> Result<(), PolicyViolation> {
        let next_window_id = authorization.new_window_epoch;
        if self.poisoned {
            return Err(PolicyViolation::GuardPoisoned);
        }
        if self.active_phase.is_some() || self.party_id != self.enrolled_party_id {
            self.poison();
            return Err(PolicyViolation::IntentBindingMismatch);
        }
        if next_window_id <= self.current_window_id {
            return Err(PolicyViolation::WindowIdMismatch);
        }
        let authority = self
            .window_authority
            .as_ref()
            .ok_or(PolicyViolation::IntentBindingMismatch)?;
        let expected = WindowAdvanceAuthorization::new(
            &authority.key,
            &authority.policy_id,
            self.current_window_id,
            next_window_id,
        );
        if !ct_eq_bytes(&expected.mac, &authorization.mac) {
            return Err(PolicyViolation::IntentBindingMismatch);
        }
        if let Some(guard) = self.verified_velocity.take() {
            let (guard, result) =
                guard.rotate_window(next_window_id, self.durable_key_id, self.durable_key_id);
            self.verified_velocity = Some(guard);
            if result.is_err() {
                self.poison();
                return Err(PolicyViolation::LedgerPersistenceFailed);
            }
        }
        self.current_window_id = next_window_id;
        self.burned_intent_nonces.clear();
        self.burned_sessions.clear();
        self.min_nonce_watermark = None;
        self.min_session_watermark = None;
        self.accumulated_window_spend = 0;
        Ok(())
    }

    /// Authenticate `intent.initiator_party == self.party_id` toward every approver in
    /// `intent.approver_parties` using pairwise shared guard keys, updating `intent.initiator_macs`
    /// and `intent.message_digest` and returning the updated canonical signing bytes.
    pub fn authenticate_initiated_intent(
        &self,
        policy: &TransactionPolicy,
        intent: &mut TransactionIntent,
    ) -> Result<Vec<u8>, PolicyViolation> {
        if self.poisoned {
            return Err(PolicyViolation::GuardPoisoned);
        }
        if self.party_id != self.enrolled_party_id || intent.initiator_party != self.party_id {
            return Err(PolicyViolation::UnauthenticatedInitiator);
        }
        let policy_digest = policy.canonical_digest();
        let auth_digest = intent.initiator_auth_digest(&policy_digest);
        let mut approvers = intent.approver_parties.clone();
        approvers.sort_unstable();
        approvers.dedup();
        let mut macs = Vec::with_capacity(approvers.len());
        for approver in approvers {
            macs.push(InitiatorPeerMac {
                approver_party: approver,
                mac_tag: self.initiator_tag(self.party_id, approver, &auth_digest)?,
            });
        }
        intent.initiator_macs = macs;
        let signing_bytes = intent.to_canonical_signing_bytes(&policy_digest);
        intent.message_digest = cshake256_framed_32(b"QSAG.POLICY.MSG.V1", &[&signing_bytes]);
        Ok(signing_bytes)
    }

    /// The tag `initiator` attaches for `approver` over `auth_digest`. This guard is one of
    /// the two: a self-approval is keyed by the local salt, a pair by its shared zero seed.
    fn initiator_tag(
        &self,
        initiator: u16,
        approver: u16,
        auth_digest: &[u8; 32],
    ) -> Result<[u8; 32], PolicyViolation> {
        if initiator == approver {
            return Ok(cshake256_framed_32(
                b"QSAG.POLICY.INITIATOR_SELF_MAC.V1",
                &[
                    &self.local_salt_seed,
                    &self.party_id.to_be_bytes(),
                    auth_digest,
                ],
            ));
        }
        let peer = if initiator == self.party_id {
            approver
        } else {
            initiator
        };
        let (_, z_seed) = self
            .pairwise_zero_seeds
            .iter()
            .find(|(p, _)| *p == peer)
            .ok_or(PolicyViolation::UnauthenticatedInitiator)?;
        Ok(cshake256_framed_32(
            b"QSAG.POLICY.INITIATOR_AUTH_MAC.V1",
            &[
                z_seed,
                &initiator.to_be_bytes(),
                &approver.to_be_bytes(),
                auth_digest,
            ],
        ))
    }

    pub(crate) fn verify_initiator_authentication(
        &self,
        policy: &TransactionPolicy,
        intent: &TransactionIntent,
        force_required: bool,
    ) -> Result<(), PolicyViolation> {
        let must_verify = force_required
            || self.require_authenticated_initiator
            || !intent.initiator_macs.is_empty();
        if !must_verify {
            return Ok(());
        }
        let policy_digest = policy.canonical_digest();
        let auth_digest = intent.initiator_auth_digest(&policy_digest);
        if intent.initiator_party == self.party_id && policy.forbid_initiator_self_approval {
            return Err(PolicyViolation::InitiatorSelfApprovalForbidden);
        }
        let expected_tag = SecretBuffer(self.initiator_tag(
            intent.initiator_party,
            self.party_id,
            &auth_digest,
        )?);
        let mut matched = false;
        let mut count_for_self = 0usize;
        for m in &intent.initiator_macs {
            if m.approver_party == self.party_id {
                count_for_self += 1;
                matched |= ct_eq_bytes(&m.mac_tag, &*expected_tag);
            }
        }
        if count_for_self != 1 || !matched {
            return Err(PolicyViolation::UnauthenticatedInitiator);
        }
        Ok(())
    }

    pub(crate) fn check_window_nonce_and_projected_spend(
        &self,
        velocity_window_cap: u128,
        intent: &TransactionIntent,
        session_id: &[u8; 32],
        external_floor: u128,
    ) -> Result<u128, PolicyViolation> {
        if intent.window_id != self.current_window_id {
            return Err(PolicyViolation::WindowIdMismatch);
        }
        if self.is_nonce_burned(&intent.nonce) || self.is_session_burned(session_id) {
            return Err(PolicyViolation::DuplicateIntentNonce);
        }
        if self.burned_intent_nonces.len() >= self.replay_capacity
            || self.burned_sessions.len() >= self.replay_capacity
        {
            return Err(PolicyViolation::ReplayWindowExhausted);
        }
        let effective_prior = self
            .accumulated_window_spend
            .max(intent.rolling_window_spent)
            .max(external_floor);
        // The retained verified guard is the authority on this window's spend.
        if let Some(guard) = &self.verified_velocity
            && (guard.window_id() != self.current_window_id
                || guard.spent_units() != self.accumulated_window_spend)
        {
            return Err(PolicyViolation::LedgerPersistenceFailed);
        }
        qsag_verified::policy_and_addr::checked_velocity_spend(
            effective_prior,
            intent.amount_units,
            velocity_window_cap,
        )
        .ok_or(PolicyViolation::VelocityCapOverflowOrExceeded)
    }

    /// Decide an approved spend without changing this guard. The verified transition runs
    /// on a guard replayed from the retained one (or built for `velocity_window_cap` on
    /// first use, after a restore without a pinned cap, or after a policy cap change, which
    /// replays the recorded spend and so refuses a spend already above the cap). Everything
    /// that can refuse the spend is decided here; [`Self::commit_approved_intent`] cannot fail.
    pub(crate) fn prepare_approved_intent(
        &self,
        velocity_window_cap: u128,
        projected_spend: u128,
        nonce: [u8; 32],
        session_id: [u8; 32],
    ) -> Result<PreparedGuardSpend, PolicyViolation> {
        if self.is_nonce_burned(&nonce) || self.is_session_burned(&session_id) {
            return Err(PolicyViolation::DuplicateIntentNonce);
        }
        if self.burned_intent_nonces.len() >= self.replay_capacity
            || self.burned_sessions.len() >= self.replay_capacity
        {
            return Err(PolicyViolation::ReplayWindowExhausted);
        }
        let amount = projected_spend
            .checked_sub(self.accumulated_window_spend)
            .ok_or(PolicyViolation::VelocityCapOverflowOrExceeded)?;
        let (pinned, pinned_generation) = match &self.verified_velocity {
            Some(retained)
                if retained.cap_units() == velocity_window_cap
                    && retained.window_id() == self.current_window_id
                    && retained.spent_units() == self.accumulated_window_spend =>
            {
                (
                    replay_verified_velocity(retained)
                        .ok_or(PolicyViolation::LedgerPersistenceFailed)?,
                    self.velocity_generation,
                )
            }
            _ => rebuild_verified_velocity(
                self.current_window_id,
                velocity_window_cap,
                self.durable_key_id,
                self.velocity_generation,
                self.accumulated_window_spend,
            )
            .ok_or(PolicyViolation::VelocityCapOverflowOrExceeded)?,
        };
        let generation = pinned_generation
            .checked_add(1)
            .ok_or(PolicyViolation::LedgerPersistenceFailed)?;
        let (verified, result) = pinned.authorize_spend(qsag_verified::VelocitySpendRequest {
            window_id: self.current_window_id,
            nonce: generation,
            amount_units: amount,
            policy_pin: self.durable_key_id,
            authority_pin: self.durable_key_id,
        });
        if result.is_err() {
            return Err(PolicyViolation::VelocityCapOverflowOrExceeded);
        }
        Ok(PreparedGuardSpend {
            verified,
            generation,
            spend: projected_spend,
            nonce,
            session_id,
        })
    }

    /// Install a spend [`Self::prepare_approved_intent`] decided on this guard, with no
    /// guard mutation in between.
    pub(crate) fn commit_approved_intent(&mut self, prepared: PreparedGuardSpend) {
        let PreparedGuardSpend {
            verified,
            generation,
            spend,
            nonce,
            session_id,
        } = prepared;
        self.verified_velocity = Some(verified);
        self.velocity_generation = generation;
        self.accumulated_window_spend = spend;
        // Every identifier above the monotone floor stays in its sorted set: nothing is
        // evicted, and the floor itself is untouched.
        for (values, value) in [
            (&mut self.burned_intent_nonces, nonce),
            (&mut self.burned_sessions, session_id),
        ] {
            let index = values.binary_search(&value).unwrap_or_else(|i| i);
            values.insert(index, value);
        }
    }

    /// Commit an approved spend through the verified guard. A refusal leaves this guard,
    /// its ledger and its retained verified guard exactly as they were.
    pub(crate) fn record_approved_intent(
        &mut self,
        velocity_window_cap: u128,
        projected_spend: u128,
        nonce: [u8; 32],
        session_id: [u8; 32],
    ) -> Result<(), PolicyViolation> {
        let prepared =
            self.prepare_approved_intent(velocity_window_cap, projected_spend, nonce, session_id)?;
        self.commit_approved_intent(prepared);
        Ok(())
    }

    /// Ratchet the monotone replay watermarks (`nonce_floor`, `session_floor`) forward,
    /// permanently burning every nonce `<= nonce_floor` and session `<= session_floor`
    /// while reclaiming explicit replay-set entries at or below those floors.
    ///
    /// Random nonces strictly above `nonce_floor` remain explicitly retained and are NEVER
    /// evicted. Attempting to regress either watermark fails with `IntentBindingMismatch`.
    pub fn compact_monotone_replay_floor(
        &mut self,
        nonce_floor: [u8; 32],
        session_floor: [u8; 32],
    ) -> Result<(), PolicyViolation> {
        if self.poisoned {
            return Err(PolicyViolation::GuardPoisoned);
        }
        if self.active_phase.is_some() || self.party_id != self.enrolled_party_id {
            self.poison();
            return Err(PolicyViolation::IntentBindingMismatch);
        }
        if self
            .min_nonce_watermark
            .is_some_and(|prev| nonce_floor < prev)
            || self
                .min_session_watermark
                .is_some_and(|prev| session_floor < prev)
        {
            return Err(PolicyViolation::IntentBindingMismatch);
        }
        self.burned_intent_nonces.retain(|n| *n > nonce_floor);
        self.burned_sessions.retain(|s| *s > session_floor);
        self.min_nonce_watermark = Some(nonce_floor);
        self.min_session_watermark = Some(session_floor);
        Ok(())
    }

    pub(crate) fn incoming_slot_alpha(
        &self,
        peer_id: u16,
        peer_slot: usize,
    ) -> SecretBuffer<[u128; 2]> {
        derive_peer_slot_alpha(&self.bdoz_alpha_share, peer_id, peer_slot)
    }

    pub(crate) fn is_peer_slot_consumed(&self, peer_id: u16, peer_slot: usize) -> bool {
        if peer_slot >= self.preproc_r.len() {
            return true;
        }
        self.consumed_peer_slots
            .iter()
            .find(|(p, _)| *p == peer_id)
            .is_none_or(|(_, words)| {
                words
                    .get(peer_slot / 64)
                    .is_none_or(|mask| ((mask >> (peer_slot % 64)) & 1) != 0)
            })
    }

    pub(crate) fn retire_own_slot(&mut self, slot: usize) {
        if let Some(r) = self.preproc_r.get_mut(slot) {
            wipe(r);
        }
        for (_, vec_m) in &mut self.preproc_outgoing_macs {
            if let Some(m) = vec_m.get_mut(slot) {
                wipe(m);
            }
        }
    }

    pub(crate) fn retire_peer_slot(&mut self, peer_id: u16, peer_slot: usize) {
        // Bits past the pool size must stay clear: the checkpoint codec rejects them.
        if peer_slot >= self.preproc_r.len() {
            return;
        }
        if let Some((_, words)) = self
            .consumed_peer_slots
            .iter_mut()
            .find(|(p, _)| *p == peer_id)
            && let Some(mask) = words.get_mut(peer_slot / 64)
        {
            *mask |= 1u64 << (peer_slot % 64);
        }
        for (p, vec_k) in &mut self.preproc_incoming_keys {
            if *p == peer_id
                && let Some(k) = vec_k.get_mut(peer_slot)
            {
                wipe(k);
            }
        }
    }

    /// Abort ONLY the single session slot `slot` (and any opened peer slots) on peer/network faults,
    /// leaving persistent guard keys, remaining slots, and the durable spend/nonce ledger intact.
    pub(crate) fn abort_session_slot(&mut self, slot: usize, peer_slots: &[(u16, usize)]) {
        self.active_phase = None;
        self.retire_own_slot(slot);
        for &(peer_id, peer_slot) in peer_slots {
            self.retire_peer_slot(peer_id, peer_slot);
        }
    }

    pub(crate) fn poison(&mut self) {
        self.poisoned = true;
        self.active_phase = None;
        wipe(&mut self.bdoz_alpha_share);
        wipe(&mut self.local_salt_seed);
        for (_, seed) in &mut self.pairwise_zero_seeds {
            wipe(seed);
        }
        for r in &mut self.preproc_r {
            wipe(r);
        }
        for (_, vec_m) in &mut self.preproc_outgoing_macs {
            for m in vec_m {
                wipe(m);
            }
        }
        for (_, vec_k) in &mut self.preproc_incoming_keys {
            for k in vec_k {
                wipe(k);
            }
        }
    }
}

impl Drop for PolicySignerGuardShare {
    fn drop(&mut self) {
        self.poison();
    }
}

/// Unforgeable linear capability token (`!Clone`, `!Copy`, private constructor) minted ONLY when
/// `TransactionPolicy::evaluate` AND the committed pairwise BDOZ 2-lane GF($2^{128}$) MAC barrier succeed!
#[derive(Debug)]
pub struct AuthorizedSignReleaseToken {
    session_id: [u8; 32],
    pub(crate) policy_digest: [u8; 32],
    intent_digest: [u8; 32],
    pub(crate) intent: TransactionIntent,
    /// `Some(id)` on a per-party token from [`Self::into_quorum_party_tokens`];
    /// `None` on the quorum token the barrier minted.
    party: Option<u16>,
}

/// Run one committed sigma opening round through the extracted single-use guard. Each item
/// is a frozen commitment, the commitment recomputed from the opening, and the opened lanes.
/// The permit exists only if every opening matched and the lanes XOR to zero for exactly
/// this session, round and binding.
pub(crate) fn release_sigma_round(
    session_id: &[u8; 32],
    round_id: u64,
    binding: &[u8; 32],
    openings: &[([u8; 32], [u8; 32], [u128; 2])],
) -> Result<OpeningReleasePermit, PolicyViolation> {
    let expected =
        u64::try_from(openings.len()).map_err(|_| PolicyViolation::IntentBindingMismatch)?;
    let mut guard = ConsumingOpeningGuard2Lane::new(*session_id, round_id, *binding, expected);
    for (commitment, recomputed, lanes) in openings {
        guard = guard.absorb_opening(commitment, recomputed, *lanes);
    }
    let (_spent, permit) = guard.verify_once(session_id, round_id, binding);
    permit.ok_or(PolicyViolation::BarrierBdozMacFailed)
}

impl AuthorizedSignReleaseToken {
    /// The only constructor. It consumes the permit of this session's sigma opening.
    pub(crate) fn mint(
        permit: OpeningReleasePermit,
        session_id: [u8; 32],
        policy_digest: [u8; 32],
        intent_digest: [u8; 32],
        intent: TransactionIntent,
    ) -> Result<Self, PolicyViolation> {
        // Both barriers already compare the intent's quorum with their sorted guard
        // set. The split hands out one token per entry, so the invariant is restated
        // at the only place a token is made.
        if intent.quorum_ids.is_empty()
            || !intent.quorum_ids.windows(2).all(|w| w[0] < w[1])
            || !ct_eq_bytes(&permit.session_id(), &session_id)
        {
            return Err(PolicyViolation::BarrierBdozMacFailed);
        }
        Ok(Self {
            session_id,
            policy_digest,
            intent_digest,
            intent,
            party: None,
        })
    }

    /// True when this token releases exactly `(key_id, msg, ctx, quorum)`. It does not
    /// say which quorum member may spend the token: a per-party signer checks
    /// [`Self::matches_signing_party`] instead.
    pub fn matches_signing(
        &self,
        key_id: &[u8; 32],
        msg: &[u8],
        ctx: &[u8],
        quorum: &[u16],
    ) -> bool {
        let mut ids = quorum.to_vec();
        ids.sort_unstable();
        msg == self.intent.to_canonical_signing_bytes(&self.policy_digest)
            && ids.windows(2).all(|w| w[0] != w[1])
            && ids == self.intent.quorum_ids
            && ct_eq_bytes(key_id, &self.intent.signing_key_id)
            && ct_eq_bytes(
                &cshake256_framed_32(b"QSAG.POLICY.CTX.V1", &[ctx]),
                &self.intent.signing_context_digest,
            )
    }

    pub const fn session_id(&self) -> &[u8; 32] {
        &self.session_id
    }
    pub const fn policy_digest(&self) -> &[u8; 32] {
        &self.policy_digest
    }
    pub const fn intent_digest(&self) -> &[u8; 32] {
        &self.intent_digest
    }
    pub fn quorum_ids(&self) -> &[u16] {
        &self.intent.quorum_ids
    }
    /// The quorum member this token was split off for, or `None` for an unsplit
    /// quorum token.
    pub const fn party_id(&self) -> Option<u16> {
        self.party
    }
    /// [`Self::matches_signing`] for the holder of a per-party token: additionally
    /// requires that this token was split off for `party_id`. One custodian holding
    /// two of a quorum's tokens can therefore spend only its own, and an unsplit
    /// quorum token satisfies no party.
    pub fn matches_signing_party(
        &self,
        party_id: u16,
        key_id: &[u8; 32],
        msg: &[u8],
        ctx: &[u8],
        quorum: &[u16],
    ) -> bool {
        self.party == Some(party_id) && self.matches_signing(key_id, msg, ctx, quorum)
    }
    /// Split one quorum release into one move-only token per approved party, consuming
    /// `self`. Token `i` is bound to `quorum_ids()[i]` (ascending party order) and
    /// reports it from [`Self::party_id`]. A per-party token does not fan out again:
    /// splitting it returns just that token.
    pub fn into_quorum_party_tokens(self) -> Vec<Self> {
        if self.party.is_some() {
            return alloc::vec![self];
        }
        self.intent
            .quorum_ids
            .iter()
            .map(|&party| Self {
                session_id: self.session_id,
                policy_digest: self.policy_digest,
                intent_digest: self.intent_digest,
                intent: self.intent.clone(),
                party: Some(party),
            })
            .collect()
    }
}

/// Trusted recovery/test setup: the caller knows every guard secret.
/// Provision `n` [`PolicySignerGuardShare`]s with Eurocrypt-2011 pairwise BDOZ correlations and
/// private pairwise PRG zero-share seeds (`0` shared global mask seeds; offline entropy zeroized!).
#[cfg(any(test, feature = "test-dealer"))]
pub fn trusted_dealer_setup_for_testing(
    guard_entropy: [u8; 32],
    party_ids: &[u16],
) -> Vec<PolicySignerGuardShare> {
    let mut ent = guard_entropy;
    let n = party_ids.len();

    // Derive each party's independent 2-lane GF(2^128) BDOZ MAC key seed `\alpha_j` and preproc masks `r_{i, s}`.
    let mut alphas: Vec<[u128; 2]> = Vec::with_capacity(n);
    let mut all_r: Vec<Vec<[u128; 2]>> = Vec::with_capacity(n);
    for &pid in party_ids {
        let p_be = pid.to_be_bytes();
        let raw = secret_digest(b"QSAG.POLICY.ALPHA_SH.V2", &[&ent, &p_be]);
        alphas.push(policy_pair(&raw));

        let mut r_slots = Vec::with_capacity(BDOZ_PREPROC_SLOTS);
        for s in 0..BDOZ_PREPROC_SLOTS {
            let s_be = (s as u32).to_be_bytes();
            let r_raw = secret_digest(b"QSAG.POLICY.PREPROC_R.V2", &[&ent, &p_be, &s_be]);
            r_slots.push(policy_pair(&r_raw));
        }
        all_r.push(r_slots);
    }

    let mut out = Vec::with_capacity(n);
    for (i_idx, &pid_i) in party_ids.iter().enumerate() {
        let pi_be = pid_i.to_be_bytes();
        let local_salt_seed = cshake256_framed_32(b"QSAG.POLICY.LOCAL_SALT.V2", &[&ent, &pi_be]);

        let mut pairwise_zero_seeds = Vec::with_capacity(n.saturating_sub(1));
        let mut preproc_outgoing_macs = Vec::with_capacity(n.saturating_sub(1));
        let mut preproc_incoming_keys = Vec::with_capacity(n.saturating_sub(1));
        let mut consumed_peer_slots = Vec::with_capacity(n.saturating_sub(1));

        for (j_idx, &pid_j) in party_ids.iter().enumerate() {
            if i_idx == j_idx {
                continue;
            }
            let lo = pid_i.min(pid_j).to_be_bytes();
            let hi = pid_i.max(pid_j).to_be_bytes();
            let z_seed = cshake256_framed_32(b"QSAG.POLICY.PAIR_ZSEED.V2", &[&ent, &lo, &hi]);
            pairwise_zero_seeds.push((pid_j, z_seed));
            consumed_peer_slots.push((pid_j, alloc::vec![0u64; BDOZ_PREPROC_SLOTS.div_ceil(64)]));

            let pj_be = pid_j.to_be_bytes();
            // Outgoing tags `M_{i -> j, s} = K_{j <- i, s} ^ (\alpha_{j <- i, s} * r_{i, s})`
            let mut m_vec = Vec::with_capacity(BDOZ_PREPROC_SLOTS);
            // Incoming keys `K_{i <- j, s}` (uniformly random, independent of `r_{j, s}`)
            let mut k_vec = Vec::with_capacity(BDOZ_PREPROC_SLOTS);

            for (s, &r_is) in all_r[i_idx].iter().enumerate().take(BDOZ_PREPROC_SLOTS) {
                let s_be = (s as u32).to_be_bytes();
                let alpha_j_slot = derive_peer_slot_alpha(&alphas[j_idx], pid_i, s);
                // Key held by `j` on `i`'s wire `r_{i, s}`:
                let k_j_from_i_raw =
                    secret_digest(b"QSAG.POLICY.BDOZ_KEY.V2", &[&ent, &pj_be, &pi_be, &s_be]);
                let k_j_from_i = SecretBuffer(policy_pair(&k_j_from_i_raw));
                let m_i_to_j = [
                    k_j_from_i[0] ^ gf2_128_mul(alpha_j_slot[0], r_is[0]),
                    k_j_from_i[1] ^ gf2_128_mul(alpha_j_slot[1], r_is[1]),
                ];
                m_vec.push(m_i_to_j);

                // Key held by `i` on `j`'s wire `r_{j, s}`:
                let k_i_from_j_raw =
                    secret_digest(b"QSAG.POLICY.BDOZ_KEY.V2", &[&ent, &pi_be, &pj_be, &s_be]);
                k_vec.push(policy_pair(&k_i_from_j_raw));
            }
            preproc_outgoing_macs.push((pid_j, m_vec));
            preproc_incoming_keys.push((pid_j, k_vec));
        }

        out.push(PolicySignerGuardShare {
            party_id: pid_i,
            bdoz_alpha_share: alphas[i_idx],
            window_authority: None,
            durable_key_id: cshake256_framed_32(b"QSAG.POLICY.DURABLE_KEY.V2", &[&local_salt_seed]),
            durable_generation: Cell::new(0),
            verified_velocity: None,
            velocity_generation: 0,
            local_salt_seed,
            pairwise_zero_seeds,
            preproc_r: all_r[i_idx].clone(),
            preproc_outgoing_macs,
            preproc_incoming_keys,
            consumed_peer_slots,
            next_slot: Cell::new(0),
            poisoned: false,
            enrolled_party_id: pid_i,
            active_phase: None,
            current_window_id: 0,
            accumulated_window_spend: 0,
            replay_capacity: MAX_BURNED_INTENT_NONCES,
            burned_intent_nonces: Vec::new(),
            min_nonce_watermark: None,
            burned_sessions: Vec::new(),
            min_session_watermark: None,
            require_authenticated_initiator: true,
        });
    }

    // Zeroize all offline preprocessing material before returning!
    for a in &mut alphas {
        wipe(a);
    }
    for vec_r in &mut all_r {
        for r in vec_r {
            wipe(r);
        }
    }
    wipe(&mut ent);
    out
}

/// Compatibility name for the trusted dealer helper. Never use for production provisioning.
#[cfg(any(test, feature = "test-dealer"))]
pub fn setup_policy_guard_shares(
    guard_entropy: [u8; 32],
    party_ids: &[u16],
) -> Vec<PolicySignerGuardShare> {
    trusted_dealer_setup_for_testing(guard_entropy, party_ids)
}

pub(crate) fn compute_folded_policy_wire<B: AcceleratorBackend>(
    policy_digest: &[u8; 32],
    intent_digest: &[u8; 32],
    session_id: &[u8; 32],
    initiator_party: u16,
    window_id: u64,
    intent_nonce: &[u8; 32],
    accel: &B,
) -> Result<(u128, u128), PolicyViolation> {
    let meta = cshake256_framed_32(
        b"QSAG.POLICY.WIRE_META.V1",
        &[
            &initiator_party.to_be_bytes(),
            &window_id.to_be_bytes(),
            intent_nonce,
        ],
    );
    let lanes = |digest: &[u8; 32]| {
        let [lo, hi] = policy_pair(digest);
        (lo, hi)
    };
    let x_vec = [
        lanes(policy_digest),
        lanes(intent_digest),
        lanes(&meta),
        (1u128, 1u128),
    ];
    let w_raw = cshake256_framed_32(
        b"QSAG.POLICY.BARRIER_W.V3",
        &[
            session_id,
            policy_digest,
            intent_digest,
            &initiator_party.to_be_bytes(),
            &window_id.to_be_bytes(),
        ],
    );
    let [w0, w1] = policy_pair(&w_raw);
    let weights = [
        (w0, w1),
        (w1 ^ 0x55, w0 ^ 0xAA),
        (w0 ^ 0xCC, w1 ^ 0x33),
        (w0 ^ w1 ^ 1, w0 ^ 3),
    ];
    accel
        .bdoz_gf2_128_batch_dot(&x_vec, &weights)
        .map_err(|_| PolicyViolation::BarrierBdozMacFailed)
}

impl PolicySignerGuardShare {
    pub(crate) fn pairwise_zero_share(
        &self,
        quorum_ids: &[u16],
        session_id: &[u8; 32],
        q_digest: &[u8; 32],
    ) -> SecretBuffer<[u128; 2]> {
        let mut z = SecretBuffer([0u128; 2]);
        for &peer in quorum_ids {
            if peer == self.party_id {
                continue;
            }
            if let Some((_, seed)) = self.pairwise_zero_seeds.iter().find(|(p, _)| *p == peer) {
                let prf = secret_digest(
                    b"QSAG.POLICY.PAIR_ZERO_PRF.V2",
                    &[seed, session_id, q_digest],
                );
                let share = SecretBuffer(policy_pair(&prf));
                z[0] ^= share[0];
                z[1] ^= share[1];
            }
        }
        z
    }

    pub(crate) fn outgoing_mac(
        &self,
        peer_id: u16,
        slot: usize,
    ) -> Result<[u128; 2], PolicyViolation> {
        let (_, v) = self
            .preproc_outgoing_macs
            .iter()
            .find(|(p, _)| *p == peer_id)
            .ok_or(PolicyViolation::BarrierBdozMacFailed)?;
        v.get(slot)
            .copied()
            .ok_or(PolicyViolation::BarrierPreprocExhausted)
    }

    pub(crate) fn incoming_key(
        &self,
        peer_id: u16,
        peer_slot: usize,
    ) -> Result<[u128; 2], PolicyViolation> {
        let (_, v) = self
            .preproc_incoming_keys
            .iter()
            .find(|(p, _)| *p == peer_id)
            .ok_or(PolicyViolation::BarrierBdozMacFailed)?;
        if peer_slot >= v.len() {
            return Err(PolicyViolation::BarrierPreprocExhausted);
        }
        if self.is_peer_slot_consumed(peer_id, peer_slot) {
            return Err(PolicyViolation::IntentBindingMismatch);
        }
        Ok(v[peer_slot])
    }

    /// Whether every quorum this policy can approve shares a party with `quorum_ids`, so
    /// that party's own ledger sees the whole window: the quorum is the full committee, or
    /// it contains the fixed `hardware_guardian_party`. Any other quorum can be disjoint
    /// from another approving quorum and is accepted only with a [`SharedWindowSpendLedger`].
    /// The rule does not depend on `velocity_window_cap`: the common ledger also carries the
    /// committee-wide nonce and session replay sets and the overflow bound of the window sum.
    pub(crate) fn has_global_velocity_intersection(
        &self,
        policy: &TransactionPolicy,
        quorum_ids: &[u16],
    ) -> bool {
        let full_committee = quorum_ids.len() == 1 + self.pairwise_zero_seeds.len();
        let fixed_guardian = policy
            .hardware_guardian_party
            .is_some_and(|hw| quorum_ids.contains(&hw));
        full_committee || fixed_guardian
    }
}
