use super::*;
use qsag_verified::{StatefulVelocityGuard, VelocitySpendRequest};

/// Committee-wide cumulative velocity-spend and replay ledger for guardian-less multi-quorum
/// barriers (`evaluate_policy_committed_barrier_with_ledger`).
///
/// When non-intersecting signer subsets (such as `{1, 2}` and `{3, 4}` in a 2-of-4 committee
/// without a fixed accounting `hardware_guardian_party`) can approve spends within the same
/// velocity window, per-party guard ledgers alone cannot observe disjoint quorums. Passing a
/// shared ledger enforces global cumulative window spend and nonce/session uniqueness across
/// every quorum switch.
pub struct SharedWindowSpendLedger {
    pub(crate) policy_digest: [u8; 32],
    pub(crate) verified_velocity: Option<StatefulVelocityGuard>,
    pub(crate) generation: u64,
    pub(crate) failed: bool,
    pub(crate) current_window_id: u64,
    pub(crate) accumulated_window_spend: u128,
    pub(crate) replay_capacity: usize,
    pub(crate) burned_intent_nonces: Vec<[u8; 32]>,
    pub(crate) min_nonce_watermark: Option<[u8; 32]>,
    pub(crate) burned_sessions: Vec<[u8; 32]>,
    pub(crate) min_session_watermark: Option<[u8; 32]>,
    pub(crate) window_authority: Option<WindowAuthority>,
}

impl SharedWindowSpendLedger {
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

    pub fn new(policy: &TransactionPolicy, initial_window_id: u64) -> Self {
        Self {
            policy_digest: policy.canonical_digest(),
            verified_velocity: Some(StatefulVelocityGuard::new_window(
                initial_window_id,
                policy.velocity_window_cap,
                policy.canonical_digest(),
                policy.canonical_digest(),
            )),
            generation: 0,
            failed: false,
            current_window_id: initial_window_id,
            accumulated_window_spend: 0,
            replay_capacity: MAX_BURNED_INTENT_NONCES,
            burned_intent_nonces: Vec::new(),
            min_nonce_watermark: None,
            burned_sessions: Vec::new(),
            min_session_watermark: None,
            window_authority: None,
        }
    }

    pub fn with_window_authority(
        mut self,
        policy_id: [u8; 32],
        key: [u8; 32],
    ) -> Result<Self, PolicyViolation> {
        let key = SecretBuffer(key);
        if self.window_authority.is_some() {
            return Err(PolicyViolation::IntentBindingMismatch);
        }
        self.window_authority = Some(WindowAuthority {
            policy_id,
            key: *key,
        });
        Ok(self)
    }

    pub const fn current_window_id(&self) -> u64 {
        self.current_window_id
    }

    pub const fn accumulated_window_spend(&self) -> u128 {
        self.accumulated_window_spend
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

    pub fn advance_velocity_window(
        &mut self,
        authorization: &WindowAdvanceAuthorization,
    ) -> Result<(), PolicyViolation> {
        if self.failed {
            return Err(PolicyViolation::LedgerPersistenceFailed);
        }
        let next_window_id = authorization.new_window_epoch;
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
        self.generation = self
            .generation
            .checked_add(1)
            .ok_or(PolicyViolation::LedgerPersistenceFailed)?;
        let guard = self
            .verified_velocity
            .take()
            .ok_or(PolicyViolation::LedgerPersistenceFailed)?;
        let (guard, result) =
            guard.rotate_window(next_window_id, self.policy_digest, self.policy_digest);
        self.verified_velocity = Some(guard);
        if result.is_err() {
            self.failed = true;
            return Err(PolicyViolation::LedgerPersistenceFailed);
        }
        self.current_window_id = next_window_id;
        self.burned_intent_nonces.clear();
        self.burned_sessions.clear();
        self.min_nonce_watermark = None;
        self.min_session_watermark = None;
        self.accumulated_window_spend = 0;
        Ok(())
    }

    pub(crate) fn check_projected_spend(
        &self,
        policy: &TransactionPolicy,
        intent: &TransactionIntent,
        session_id: &[u8; 32],
    ) -> Result<u128, PolicyViolation> {
        if self.failed || self.generation == u64::MAX {
            return Err(PolicyViolation::LedgerPersistenceFailed);
        }
        if !ct_eq_bytes(&policy.canonical_digest(), &self.policy_digest) {
            return Err(PolicyViolation::IntentBindingMismatch);
        }
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
            .max(intent.rolling_window_spent);
        let guard = self
            .verified_velocity
            .as_ref()
            .ok_or(PolicyViolation::LedgerPersistenceFailed)?;
        if guard.window_id() != self.current_window_id
            || guard.spent_units() != self.accumulated_window_spend
            || guard.cap_units() != policy.velocity_window_cap
        {
            return Err(PolicyViolation::LedgerPersistenceFailed);
        }
        effective_prior
            .checked_add(intent.amount_units)
            .filter(|spent| *spent <= guard.cap_units())
            .ok_or(PolicyViolation::VelocityCapOverflowOrExceeded)
    }

    pub(crate) fn record_approved_intent(
        &mut self,
        projected_spend: u128,
        nonce: [u8; 32],
        session_id: [u8; 32],
    ) -> Result<(), PolicyViolation> {
        if self.is_nonce_burned(&nonce) || self.is_session_burned(&session_id) {
            return Err(PolicyViolation::DuplicateIntentNonce);
        }
        if self.burned_intent_nonces.len() >= self.replay_capacity
            || self.burned_sessions.len() >= self.replay_capacity
        {
            return Err(PolicyViolation::ReplayWindowExhausted);
        }
        let generation = self
            .generation
            .checked_add(1)
            .ok_or(PolicyViolation::LedgerPersistenceFailed)?;
        let amount = projected_spend
            .checked_sub(self.accumulated_window_spend)
            .ok_or(PolicyViolation::LedgerPersistenceFailed)?;
        let guard = self
            .verified_velocity
            .take()
            .ok_or(PolicyViolation::LedgerPersistenceFailed)?;
        let (guard, result) = guard.authorize_spend(VelocitySpendRequest {
            window_id: self.current_window_id,
            nonce: generation,
            amount_units: amount,
            policy_pin: self.policy_digest,
            authority_pin: self.policy_digest,
        });
        self.verified_velocity = Some(guard);
        if result.is_err() {
            self.failed = true;
            return Err(PolicyViolation::VelocityCapOverflowOrExceeded);
        }
        self.generation = generation;
        self.accumulated_window_spend = projected_spend;
        for (values, value) in [
            (&mut self.burned_intent_nonces, nonce),
            (&mut self.burned_sessions, session_id),
        ] {
            let index = values.binary_search(&value).unwrap_or_else(|i| i);
            values.insert(index, value);
        }
        Ok(())
    }

    /// Ratchet the shared ledger's monotone replay watermarks (`nonce_floor`, `session_floor`),
    /// permanently burning all values at or below the floors while reclaiming set slots.
    pub fn compact_monotone_replay_floor(
        &mut self,
        nonce_floor: [u8; 32],
        session_floor: [u8; 32],
    ) -> Result<(), PolicyViolation> {
        if self.failed {
            return Err(PolicyViolation::LedgerPersistenceFailed);
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
        let next_gen = self
            .generation
            .checked_add(1)
            .ok_or(PolicyViolation::LedgerPersistenceFailed)?;
        self.burned_intent_nonces.retain(|n| *n > nonce_floor);
        self.burned_sessions.retain(|s| *s > session_floor);
        self.min_nonce_watermark = Some(nonce_floor);
        self.min_session_watermark = Some(session_floor);
        self.generation = next_gen;
        Ok(())
    }
}

/// Bounded TTL-expiring staging pool for pre-quorum pending proposals (`[CUST-06]`).
///
/// Isolates unfinalized / pending transaction proposals completely from the committed
/// `burned_intent_nonces` replay set on [`PolicySignerGuardShare`] and [`SharedWindowSpendLedger`]:
/// 1. Unauthenticated proposals are rejected at admission (`verify_initiator_authentication`)
///    before allocating even a staging slot.
/// 2. Abandoned pending proposals expire deterministically after `ttl_secs` without ever
///    polluting or exhausting the committed replay sets.
/// 3. Already-burned committed nonces or sessions (including those below `min_nonce_watermark`)
///    are rejected immediately.
#[derive(Clone, Debug)]
pub struct PendingIntentStagingPool {
    max_pending: usize,
    entries: Vec<StagedPendingIntent>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct StagedPendingIntent {
    nonce: [u8; 32],
    session_id: [u8; 32],
    initiator_party: u16,
    expires_at_secs: u64,
}

impl Default for PendingIntentStagingPool {
    fn default() -> Self {
        Self::new(MAX_BURNED_INTENT_NONCES)
    }
}

impl PendingIntentStagingPool {
    pub const fn new(max_pending: usize) -> Self {
        Self {
            max_pending,
            entries: Vec::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Purge all staged proposals whose TTL has elapsed (`expires_at_secs <= now_secs`).
    pub fn evict_expired(&mut self, now_secs: u64) -> usize {
        let before = self.entries.len();
        self.entries.retain(|e| e.expires_at_secs > now_secs);
        before - self.entries.len()
    }

    /// Admit an authenticated pending proposal into the TTL-bounded staging pool without
    /// touching `verifier_guard`'s committed replay ledger.
    pub fn stage_authenticated_intent(
        &mut self,
        policy: &TransactionPolicy,
        verifier_guard: &PolicySignerGuardShare,
        intent: &TransactionIntent,
        now_secs: u64,
        ttl_secs: u64,
    ) -> Result<(), PolicyViolation> {
        if ttl_secs == 0 {
            return Err(PolicyViolation::TimestampOutsideWindow);
        }
        policy.evaluate(intent)?;
        verifier_guard.verify_initiator_authentication(policy, intent, true)?;
        if intent.window_id != verifier_guard.current_window_id() {
            return Err(PolicyViolation::WindowIdMismatch);
        }
        if verifier_guard.is_nonce_burned(&intent.nonce)
            || verifier_guard.is_session_burned(&intent.session_id)
        {
            return Err(PolicyViolation::DuplicateIntentNonce);
        }
        self.evict_expired(now_secs);
        for existing in &self.entries {
            if ct_eq_bytes(&existing.nonce, &intent.nonce)
                || ct_eq_bytes(&existing.session_id, &intent.session_id)
            {
                return Err(PolicyViolation::DuplicateIntentNonce);
            }
        }
        if self.entries.len() >= self.max_pending {
            return Err(PolicyViolation::ReplayWindowExhausted);
        }
        let expires_at_secs = now_secs
            .checked_add(ttl_secs)
            .ok_or(PolicyViolation::TimestampOutsideWindow)?;
        self.entries.push(StagedPendingIntent {
            nonce: intent.nonce,
            session_id: intent.session_id,
            initiator_party: intent.initiator_party,
            expires_at_secs,
        });
        Ok(())
    }

    /// Remove a proposal from the pending pool once committed (or explicitly cancelled).
    pub fn complete_intent(&mut self, nonce: &[u8; 32], session_id: &[u8; 32]) -> bool {
        let before = self.entries.len();
        self.entries
            .retain(|e| !ct_eq_bytes(&e.nonce, nonce) && !ct_eq_bytes(&e.session_id, session_id));
        self.entries.len() != before
    }
}
