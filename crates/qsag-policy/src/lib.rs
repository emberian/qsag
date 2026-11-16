#![cfg_attr(not(test), deny(clippy::unwrap_used, clippy::expect_used))]
#![no_std]
#![forbid(unsafe_code)]
//! Authenticated transaction-predicate guard (`qsag-policy`) evaluating recipient allowlists,
//! per-tx & rolling velocity caps, anti-self-approval, and quorum-tier rules inside committed
//! Eurocrypt-2011 pairwise 2-lane BDOZ GF($2^{128}$) MAC barriers before releasing any MPC share.

extern crate alloc;
#[cfg(any(test, feature = "std"))]
extern crate std;

pub mod biscuit;
pub mod durable;
pub mod macaroon;
pub use biscuit::{
    MAX_AUTHORITY_TREE_HEIGHT, MAX_BISCUIT_HOPS, PQ_BISCUIT_HOP_CRYPTO_BYTES, PqBiscuit,
    PqBiscuitAuthorityKey, PqBiscuitAuthorityPublicKey, PqBiscuitHopBlock, PqBiscuitSeal,
    PqBiscuitStepKey, capability_request_digest,
};
pub use durable::PolicyGuardError;
#[cfg(feature = "std")]
pub use durable::{FsPolicyDurableLedger, FsPolicyGenerationFence};
pub use macaroon::{
    CapabilityError, CapabilityRequest, Caveat, Discharge, MacaroonVerifier, SpongeMacaroon,
};
pub use qsag_addr::policy_signing_key_id;

use alloc::vec::Vec;
use core::cell::Cell;
use core::fmt;

use qsag_accel::AcceleratorBackend;
use qsag_accel::ct::ct_eq_bytes;

use qsag_accel::gf2_128::gf2_128_mul;
use qsag_accel::keccak::cshake256_framed_32;
use qsag_addr::{QsagAddress, WitnessSuiteTag};
use qsag_asm::wipe::{SecretBuffer, SecretBytes, SecretVec, wipe};

/// Default number of single-use preprocessed pairwise BDOZ MAC tuples per signer guard.
pub const BDOZ_PREPROC_SLOTS: usize = 64;

/// Default capacity of the durable per-window burned intent-nonce and session-ID sets.
/// Reconfigure per guard or ledger with `set_replay_capacity`, up to [`MAX_POLICY_CAPACITY`].
pub const MAX_BURNED_INTENT_NONCES: usize = 65_536;

/// Resource limits are local configuration, never silent replay eviction.
pub const MAX_POLICY_CAPACITY: usize = 1_048_576;

/// Pairwise cryptographic authenticator binding `initiator_party` to an approver's guard share.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InitiatorPeerMac {
    pub approver_party: u16,
    pub mac_tag: [u8; 32],
}

/// Amount-escalating quorum tier rule. A policy lists its tiers in the order
/// [`TransactionPolicy::validate_quorum_tiers`] accepts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct QuorumTierRule {
    /// Inclusive upper bound on `amount_units` covered by this tier.
    pub max_amount_units: u128,
    /// Minimum distinct non-initiator approvers required in this tier.
    pub min_approvers: u16,
    /// If `true`, `hardware_guardian_party` must be present in `approver_parties`.
    pub require_hardware_guardian: bool,
}

/// Deterministic custody policy specification pinned into MPC signing barriers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TransactionPolicy {
    pub chain_id: u64,
    pub pinned_suite: WitnessSuiteTag,
    /// Explicitly allowlisted recipient `Bech32m` `QsagAddress` commitments.
    pub recipient_allowlist: Vec<[u8; 32]>,
    /// Maximum value transferable in a single transaction.
    pub max_single_tx_amount: u128,
    /// Maximum cumulative spend (`rolling_window_spent + amount_units`) inside the velocity window.
    pub velocity_window_cap: u128,
    pub valid_not_before_secs: u64,
    pub valid_not_after_secs: u64,
    /// Forbid the transaction initiator from counting toward approval quorum!
    pub forbid_initiator_self_approval: bool,
    pub hardware_guardian_party: Option<u16>,
    pub quorum_tiers: Vec<QuorumTierRule>,
}

/// Canonical transaction intent evaluated by every MPC signer prior to releasing any partial signature.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TransactionIntent {
    pub chain_id: u64,
    pub suite: WitnessSuiteTag,
    pub recipient: QsagAddress,
    pub amount_units: u128,
    pub rolling_window_spent: u128,
    pub window_id: u64,
    pub nonce: [u8; 32],
    pub timestamp_secs: u64,
    pub initiator_party: u16,
    pub initiator_macs: Vec<InitiatorPeerMac>,
    pub approver_parties: Vec<u16>,
    pub payload_digest: [u8; 32],
    /// Enrolled guard authority public-key digest.
    pub guard_authority_pk: [u8; 32],
    /// Application rolling-window state commitment, including its window identity.
    pub rolling_window_accumulator: [u8; 32],
    pub signing_key_id: [u8; 32],
    pub policy_revision: u64,
    pub message_digest: [u8; 32],
    pub signing_context_digest: [u8; 32],
    pub session_id: [u8; 32],
    pub quorum_ids: Vec<u16>,
}

/// Exact policy refusal or MAC-barrier abort reason.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PolicyViolation {
    ChainIdMismatch,
    SuiteTagMismatch,
    TimestampOutsideWindow,
    WindowIdMismatch,
    DuplicateIntentNonce,
    ReplayWindowExhausted,
    UnauthenticatedInitiator,
    RecipientNotAllowlisted,
    SingleTxCapExceeded,
    VelocityCapOverflowOrExceeded,
    InitiatorSelfApprovalForbidden,
    DuplicateApproverInQuorum,
    NoMatchingQuorumTier,
    /// `quorum_tiers` fails [`TransactionPolicy::validate_quorum_tiers`].
    InvalidQuorumTierOrder,
    InsufficientTierApprovers {
        have: u16,
        need: u16,
    },
    MissingHardwareGuardian,
    EmptySignerBarrierSet,
    IntentBindingMismatch,
    GuardPoisoned,
    BarrierPreprocExhausted,
    LedgerPersistenceFailed,
    BarrierCommitmentMismatch {
        party_id: u16,
    },
    BarrierBdozMacFailed,
    CapabilityDenied(CapabilityError),
}

impl TransactionPolicy {
    pub fn canonical_digest(&self) -> [u8; 32] {
        let cid = self.chain_id.to_be_bytes();
        let suite = (self.pinned_suite as u16).to_be_bytes();
        let single_cap = self.max_single_tx_amount.to_be_bytes();
        let vel_cap = self.velocity_window_cap.to_be_bytes();
        let t_lo = self.valid_not_before_secs.to_be_bytes();
        let t_hi = self.valid_not_after_secs.to_be_bytes();
        let flags = [
            self.forbid_initiator_self_approval as u8,
            self.hardware_guardian_party.is_some() as u8,
        ];
        let hg = self.hardware_guardian_party.unwrap_or(0).to_be_bytes();

        let mut allow_flat = Vec::with_capacity(self.recipient_allowlist.len() * 32);
        for item in &self.recipient_allowlist {
            allow_flat.extend_from_slice(item);
        }
        let mut tiers_flat = Vec::with_capacity(self.quorum_tiers.len() * 19);
        for t in &self.quorum_tiers {
            tiers_flat.extend_from_slice(&t.max_amount_units.to_be_bytes());
            tiers_flat.extend_from_slice(&t.min_approvers.to_be_bytes());
            tiers_flat.push(t.require_hardware_guardian as u8);
        }

        cshake256_framed_32(
            b"QSAG.POLICY.SPEC.V1",
            &[
                &cid,
                &suite,
                &single_cap,
                &vel_cap,
                &t_lo,
                &t_hi,
                &flags,
                &hg,
                &allow_flat,
                &tiers_flat,
            ],
        )
    }

    /// Check the order of `quorum_tiers`. [`Self::evaluate`] selects the first tier whose
    /// `max_amount_units` covers the amount, so a list is in order only if every adjacent
    /// pair `(lower, higher)` satisfies:
    ///
    /// * `lower.max_amount_units < higher.max_amount_units`: `higher` is the first match
    ///   for the amounts above `lower`'s bound, so no tier is unreachable;
    /// * `lower.min_approvers <= higher.min_approvers`, and a hardware guardian required
    ///   by `lower` is required by `higher`: a larger amount never selects a weaker quorum
    ///   than a smaller one.
    ///
    /// The empty list is in order; it covers no amount. `evaluate` refuses every intent
    /// under a policy that fails this check.
    pub fn validate_quorum_tiers(&self) -> Result<(), PolicyViolation> {
        for pair in self.quorum_tiers.windows(2) {
            let (lower, higher) = (&pair[0], &pair[1]);
            if lower.max_amount_units >= higher.max_amount_units
                || lower.min_approvers > higher.min_approvers
                || (lower.require_hardware_guardian && !higher.require_hardware_guardian)
            {
                return Err(PolicyViolation::InvalidQuorumTierOrder);
            }
        }
        Ok(())
    }

    /// Deterministically evaluate `intent` against `self` in constant-time allowlist scan mode.
    pub fn evaluate(&self, intent: &TransactionIntent) -> Result<(), PolicyViolation> {
        self.validate_quorum_tiers()?;
        if intent.chain_id != self.chain_id {
            return Err(PolicyViolation::ChainIdMismatch);
        }
        if intent.suite != self.pinned_suite || intent.recipient.suite_tag != self.pinned_suite {
            return Err(PolicyViolation::SuiteTagMismatch);
        }
        if intent.timestamp_secs < self.valid_not_before_secs
            || intent.timestamp_secs > self.valid_not_after_secs
        {
            return Err(PolicyViolation::TimestampOutsideWindow);
        }

        // Branchless constant-time scan across the entire `recipient_allowlist`!
        let mut allow_hit = false;
        for allowed_comm in &self.recipient_allowlist {
            allow_hit |= ct_eq_bytes(allowed_comm, &intent.recipient.commitment_256);
        }
        if !allow_hit {
            return Err(PolicyViolation::RecipientNotAllowlisted);
        }

        if intent.amount_units > self.max_single_tx_amount {
            return Err(PolicyViolation::SingleTxCapExceeded);
        }
        qsag_verified::policy_and_addr::checked_velocity_spend(
            intent.rolling_window_spent,
            intent.amount_units,
            self.velocity_window_cap,
        )
        .ok_or(PolicyViolation::VelocityCapOverflowOrExceeded)?;

        // Validate distinctness of approvers + anti-self-approval rule!
        for (i, &p_i) in intent.approver_parties.iter().enumerate() {
            if self.forbid_initiator_self_approval && p_i == intent.initiator_party {
                return Err(PolicyViolation::InitiatorSelfApprovalForbidden);
            }
            for &p_j in &intent.approver_parties[i + 1..] {
                if p_i == p_j {
                    return Err(PolicyViolation::DuplicateApproverInQuorum);
                }
            }
        }

        // The first tier covering the amount; `validate_quorum_tiers` makes it the only
        // candidate and the weakest quorum any amount this large can select.
        let matched_tier = self
            .quorum_tiers
            .iter()
            .find(|t| intent.amount_units <= t.max_amount_units)
            .ok_or(PolicyViolation::NoMatchingQuorumTier)?;

        let have = intent.approver_parties.len() as u16;
        if have < matched_tier.min_approvers {
            return Err(PolicyViolation::InsufficientTierApprovers {
                have,
                need: matched_tier.min_approvers,
            });
        }

        if matched_tier.require_hardware_guardian {
            let guardian = self
                .hardware_guardian_party
                .ok_or(PolicyViolation::MissingHardwareGuardian)?;
            if !intent.approver_parties.contains(&guardian) {
                return Err(PolicyViolation::MissingHardwareGuardian);
            }
        }

        Ok(())
    }
}

impl TransactionIntent {
    fn sorted_approver_bytes(&self) -> Vec<u8> {
        let mut sorted = self.approver_parties.clone();
        sorted.sort_unstable();
        policy_ids_bytes(&sorted)
    }

    /// The signing payload is this canonical envelope, never arbitrary transaction
    /// bytes paired with self-declared policy metadata. `payload_digest` commits
    /// to application data; transaction executors must interpret these same fields.
    pub fn to_canonical_signing_bytes(&self, policy_digest: &[u8; 32]) -> Vec<u8> {
        let mut copy = self.clone();
        copy.message_digest = [0; 32];
        let mut out = b"QSAG.POLICY.SIGNED_INTENT.V2".to_vec();
        out.extend_from_slice(policy_digest);
        out.extend_from_slice(&copy.canonical_digest());
        out
    }
    pub fn builder(
        chain_id: u64,
        suite: WitnessSuiteTag,
        recipient: QsagAddress,
        amount_units: u128,
    ) -> TransactionIntentBuilder {
        TransactionIntentBuilder(TransactionIntent {
            chain_id,
            suite,
            recipient,
            amount_units,
            rolling_window_spent: 0,
            window_id: 0,
            nonce: [0; 32],
            timestamp_secs: 0,
            initiator_party: 0,
            initiator_macs: Vec::new(),
            approver_parties: Vec::new(),
            payload_digest: [0; 32],
            guard_authority_pk: [0; 32],
            rolling_window_accumulator: [0; 32],
            signing_key_id: [0; 32],
            policy_revision: 0,
            message_digest: [0; 32],
            signing_context_digest: [0; 32],
            session_id: [0; 32],
            quorum_ids: Vec::new(),
        })
    }

    /// Canonical preimage authenticated by `initiator_party` across every approver guard share.
    /// Excludes `initiator_macs` and `message_digest` so pairwise MAC tags can be attached cleanly.
    pub fn initiator_auth_digest(&self, policy_digest: &[u8; 32]) -> [u8; 32] {
        let cid = self.chain_id.to_be_bytes();
        let suite = (self.suite as u16).to_be_bytes();
        let amt = self.amount_units.to_be_bytes();
        let spent = self.rolling_window_spent.to_be_bytes();
        let wid = self.window_id.to_be_bytes();
        let ts = self.timestamp_secs.to_be_bytes();
        let init = self.initiator_party.to_be_bytes();
        let appr = self.sorted_approver_bytes();
        let quorum_bytes = policy_ids_bytes(&self.quorum_ids);
        cshake256_framed_32(
            b"QSAG.POLICY.INITIATOR_AUTH_PREIMAGE.V1",
            &[
                policy_digest,
                &cid,
                &suite,
                self.recipient.hrp.as_bytes(),
                &[self.recipient.version as u8],
                &(self.recipient.suite_tag as u16).to_be_bytes(),
                &[self.recipient.kind as u8],
                &self.recipient.commitment_256,
                &amt,
                &spent,
                &wid,
                &self.nonce,
                &ts,
                &init,
                &appr,
                &self.payload_digest,
                &self.guard_authority_pk,
                &self.rolling_window_accumulator,
                &self.signing_key_id,
                &self.policy_revision.to_be_bytes(),
                &self.signing_context_digest,
                &self.session_id,
                &quorum_bytes,
            ],
        )
    }

    pub fn canonical_digest(&self) -> [u8; 32] {
        let cid = self.chain_id.to_be_bytes();
        let suite = (self.suite as u16).to_be_bytes();
        let amt = self.amount_units.to_be_bytes();
        let spent = self.rolling_window_spent.to_be_bytes();
        let wid = self.window_id.to_be_bytes();
        let ts = self.timestamp_secs.to_be_bytes();
        let init = self.initiator_party.to_be_bytes();
        let appr = self.sorted_approver_bytes();
        let mut sorted_macs = self.initiator_macs.clone();
        sorted_macs.sort_by_key(|m| m.approver_party);
        let mut init_mac_bytes = Vec::with_capacity(sorted_macs.len() * 34);
        for m in sorted_macs {
            init_mac_bytes.extend_from_slice(&m.approver_party.to_be_bytes());
            init_mac_bytes.extend_from_slice(&m.mac_tag);
        }
        cshake256_framed_32(
            b"QSAG.POLICY.INTENT.V2",
            &[
                &cid,
                &suite,
                self.recipient.hrp.as_bytes(),
                &[self.recipient.version as u8],
                &(self.recipient.suite_tag as u16).to_be_bytes(),
                &[self.recipient.kind as u8],
                &self.recipient.commitment_256,
                &amt,
                &spent,
                &wid,
                &self.nonce,
                &ts,
                &init,
                &init_mac_bytes,
                &appr,
                &self.payload_digest,
                &self.guard_authority_pk,
                &self.rolling_window_accumulator,
                &self.signing_key_id,
                &self.policy_revision.to_be_bytes(),
                &self.message_digest,
                &self.signing_context_digest,
                &self.session_id,
                &policy_ids_bytes(&self.quorum_ids),
            ],
        )
    }
}

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

struct WindowAuthority {
    policy_id: [u8; 32],
    key: [u8; 32],
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
/// - Durable authoritative velocity ledger (`current_window_id`, `accumulated_window_spend`,
///   bounded `burned_intent_nonces` & `burned_sessions` rings),
/// - `<REDACTED>` `fmt::Debug` and `write_volatile` `Drop`.
pub struct PolicySignerGuardShare {
    pub party_id: u16,
    bdoz_alpha_share: [u128; 2],
    local_salt_seed: [u8; 32],
    pairwise_zero_seeds: Vec<(u16, [u8; 32])>,
    preproc_r: Vec<[u128; 2]>,
    preproc_outgoing_macs: Vec<(u16, Vec<[u128; 2]>)>,
    preproc_incoming_keys: Vec<(u16, Vec<[u128; 2]>)>,
    consumed_peer_slots: Vec<(u16, Vec<u64>)>,
    next_slot: Cell<usize>,
    poisoned: bool,
    enrolled_party_id: u16,
    active_phase: Option<(usize, u8)>,
    current_window_id: u64,
    accumulated_window_spend: u128,
    replay_capacity: usize,
    burned_intent_nonces: Vec<[u8; 32]>,
    min_nonce_watermark: Option<[u8; 32]>,
    burned_sessions: Vec<[u8; 32]>,
    min_session_watermark: Option<[u8; 32]>,
    require_authenticated_initiator: bool,
    window_authority: Option<WindowAuthority>,
    durable_key_id: [u8; 32],
    durable_generation: Cell<u64>,
    /// Extracted velocity guard retained across approvals, rotations and restores. It is
    /// pinned to a cap on first use; `velocity_generation` is its monotone request nonce.
    verified_velocity: Option<qsag_verified::StatefulVelocityGuard>,
    velocity_generation: u64,
}

/// A verified guard for `window` and `cap` holding `spent`, with request nonce `generation`
/// (at least 1 once anything was spent). `None` if `spent` exceeds `cap`.
fn rebuild_verified_velocity(
    window: u64,
    cap: u128,
    pin: [u8; 32],
    generation: u64,
    spent: u128,
) -> Option<(qsag_verified::StatefulVelocityGuard, u64)> {
    let guard = qsag_verified::StatefulVelocityGuard::new_window(window, cap, pin, pin);
    if spent == 0 && generation == 0 {
        return Some((guard, 0));
    }
    let nonce = generation.max(1);
    let (guard, result) = guard.authorize_spend(qsag_verified::VelocitySpendRequest {
        window_id: window,
        nonce,
        amount_units: spent,
        policy_pin: pin,
        authority_pin: pin,
    });
    result.ok().map(|_| (guard, nonce))
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

fn derive_peer_slot_alpha(
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

    fn verify_initiator_authentication(
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

    fn check_window_nonce_and_projected_spend(
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

    /// Bring the retained verified guard to `cap` in the current window. A guard that has
    /// to be built (first use, restore without a pinned cap, policy cap change) replays the
    /// recorded spend through the verified transition, so it is refused if it exceeds `cap`.
    fn pin_verified_velocity(&mut self, cap: u128) -> Result<(), PolicyViolation> {
        if let Some(guard) = &self.verified_velocity
            && guard.cap_units() == cap
            && guard.window_id() == self.current_window_id
            && guard.spent_units() == self.accumulated_window_spend
        {
            return Ok(());
        }
        let (guard, generation) = rebuild_verified_velocity(
            self.current_window_id,
            cap,
            self.durable_key_id,
            self.velocity_generation,
            self.accumulated_window_spend,
        )
        .ok_or(PolicyViolation::VelocityCapOverflowOrExceeded)?;
        self.verified_velocity = Some(guard);
        self.velocity_generation = generation;
        Ok(())
    }

    /// Commit an approved spend through the retained verified guard. A refusal leaves the
    /// ledger and the guard unchanged.
    fn record_approved_intent(
        &mut self,
        velocity_window_cap: u128,
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
        let amount = projected_spend
            .checked_sub(self.accumulated_window_spend)
            .ok_or(PolicyViolation::VelocityCapOverflowOrExceeded)?;
        self.pin_verified_velocity(velocity_window_cap)?;
        let generation = self
            .velocity_generation
            .checked_add(1)
            .ok_or(PolicyViolation::LedgerPersistenceFailed)?;
        let guard = self
            .verified_velocity
            .take()
            .ok_or(PolicyViolation::LedgerPersistenceFailed)?;
        let (guard, result) = guard.authorize_spend(qsag_verified::VelocitySpendRequest {
            window_id: self.current_window_id,
            nonce: generation,
            amount_units: amount,
            policy_pin: self.durable_key_id,
            authority_pin: self.durable_key_id,
        });
        self.verified_velocity = Some(guard);
        if result.is_err() {
            return Err(PolicyViolation::VelocityCapOverflowOrExceeded);
        }
        self.velocity_generation = generation;
        self.accumulated_window_spend = projected_spend;
        // Retain every nonce above `min_*_watermark` in this authenticated window without
        // clearing any established monotone replay floor!
        for (values, value) in [
            (&mut self.burned_intent_nonces, nonce),
            (&mut self.burned_sessions, session_id),
        ] {
            let index = values.binary_search(&value).unwrap_or_else(|i| i);
            values.insert(index, value);
        }
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

    fn incoming_slot_alpha(&self, peer_id: u16, peer_slot: usize) -> SecretBuffer<[u128; 2]> {
        derive_peer_slot_alpha(&self.bdoz_alpha_share, peer_id, peer_slot)
    }

    fn is_peer_slot_consumed(&self, peer_id: u16, peer_slot: usize) -> bool {
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

    fn retire_own_slot(&mut self, slot: usize) {
        if let Some(r) = self.preproc_r.get_mut(slot) {
            wipe(r);
        }
        for (_, vec_m) in &mut self.preproc_outgoing_macs {
            if let Some(m) = vec_m.get_mut(slot) {
                wipe(m);
            }
        }
    }

    fn retire_peer_slot(&mut self, peer_id: u16, peer_slot: usize) {
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
    fn abort_session_slot(&mut self, slot: usize, peer_slots: &[(u16, usize)]) {
        self.active_phase = None;
        self.retire_own_slot(slot);
        for &(peer_id, peer_slot) in peer_slots {
            self.retire_peer_slot(peer_id, peer_slot);
        }
    }

    fn poison(&mut self) {
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
    policy_digest: [u8; 32],
    intent_digest: [u8; 32],
    intent: TransactionIntent,
    // A per-party token must never fan out again.
    quorum_split: bool,
}

/// Run one committed sigma opening round through the extracted single-use guard. Each item
/// is a frozen commitment, the commitment recomputed from the opening, and the opened lanes.
/// The permit exists only if every opening matched and the lanes XOR to zero for exactly
/// this session, round and binding.
fn release_sigma_round(
    session_id: &[u8; 32],
    round_id: u64,
    binding: &[u8; 32],
    openings: &[([u8; 32], [u8; 32], [u128; 2])],
) -> Result<qsag_verified::OpeningReleasePermit, PolicyViolation> {
    let expected =
        u64::try_from(openings.len()).map_err(|_| PolicyViolation::IntentBindingMismatch)?;
    let mut guard =
        qsag_verified::ConsumingOpeningGuard2Lane::new(*session_id, round_id, *binding, expected);
    for (commitment, recomputed, lanes) in openings {
        guard = guard.absorb_opening(commitment, recomputed, *lanes);
    }
    let (_spent, permit) = guard.verify_once(session_id, round_id, binding);
    permit.ok_or(PolicyViolation::BarrierBdozMacFailed)
}

impl AuthorizedSignReleaseToken {
    /// The only constructor. It consumes the permit of this session's sigma opening.
    fn mint(
        permit: qsag_verified::OpeningReleasePermit,
        session_id: [u8; 32],
        policy_digest: [u8; 32],
        intent_digest: [u8; 32],
        intent: TransactionIntent,
    ) -> Result<Self, PolicyViolation> {
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
            quorum_split: false,
        })
    }

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
    /// Split one in-process quorum release token into exactly one linear per-signer token
    /// for each approved party in `self.intent.quorum_ids`, consuming `self`.
    /// Calling this on an already split token returns only that token.
    pub fn into_quorum_party_tokens(self) -> Vec<Self> {
        let count = self.intent.quorum_ids.len();
        if count == 0 || !self.intent.quorum_ids.windows(2).all(|w| w[0] < w[1]) {
            return Vec::new();
        }
        if self.quorum_split {
            return alloc::vec![self];
        }
        let Self {
            session_id,
            policy_digest,
            intent_digest,
            intent,
            quorum_split: _,
        } = self;
        let mut out = Vec::with_capacity(count);
        for _ in 1..count {
            out.push(Self {
                session_id,
                policy_digest,
                intent_digest,
                intent: intent.clone(),
                quorum_split: true,
            });
        }
        out.push(Self {
            session_id,
            policy_digest,
            intent_digest,
            intent,
            quorum_split: true,
        });
        out
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

fn compute_folded_policy_wire<B: AcceleratorBackend>(
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
    fn pairwise_zero_share(
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

    fn outgoing_mac(&self, peer_id: u16, slot: usize) -> Result<[u128; 2], PolicyViolation> {
        let (_, v) = self
            .preproc_outgoing_macs
            .iter()
            .find(|(p, _)| *p == peer_id)
            .ok_or(PolicyViolation::BarrierBdozMacFailed)?;
        v.get(slot)
            .copied()
            .ok_or(PolicyViolation::BarrierPreprocExhausted)
    }

    fn incoming_key(&self, peer_id: u16, peer_slot: usize) -> Result<[u128; 2], PolicyViolation> {
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

    fn has_global_velocity_intersection(
        &self,
        policy: &TransactionPolicy,
        quorum_ids: &[u16],
    ) -> bool {
        if policy.velocity_window_cap == u128::MAX {
            return true;
        }
        let full_committee = quorum_ids.len() == 1 + self.pairwise_zero_seeds.len();
        let fixed_guardian = policy
            .hardware_guardian_party
            .is_some_and(|hw| quorum_ids.contains(&hw));
        full_committee || fixed_guardian
    }
}

/// Committee-wide cumulative velocity-spend and replay ledger for guardian-less multi-quorum
/// barriers (`evaluate_policy_committed_barrier_with_ledger`).
///
/// When non-intersecting signer subsets (such as `{1, 2}` and `{3, 4}` in a 2-of-4 committee
/// without a fixed accounting `hardware_guardian_party`) can approve spends within the same
/// velocity window, per-party guard ledgers alone cannot observe disjoint quorums. Passing a
/// shared ledger enforces global cumulative window spend and nonce/session uniqueness across
/// every quorum switch.
pub struct SharedWindowSpendLedger {
    policy_digest: [u8; 32],
    verified_velocity: Option<qsag_verified::StatefulVelocityGuard>,
    generation: u64,
    failed: bool,
    current_window_id: u64,
    accumulated_window_spend: u128,
    replay_capacity: usize,
    burned_intent_nonces: Vec<[u8; 32]>,
    min_nonce_watermark: Option<[u8; 32]>,
    burned_sessions: Vec<[u8; 32]>,
    min_session_watermark: Option<[u8; 32]>,
    window_authority: Option<WindowAuthority>,
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
            verified_velocity: Some(qsag_verified::StatefulVelocityGuard::new_window(
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

    fn check_projected_spend(
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

    fn record_approved_intent(
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
        let (guard, result) = guard.authorize_spend(qsag_verified::VelocitySpendRequest {
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
struct StagedPendingIntent {
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

/// Evaluate `policy` across `quorum_guards` where each signer $i$ independently evaluates its own
/// local `per_party_intents[i]` inside the **commit-then-open Eurocrypt-2011 pairwise BDOZ**
/// barrier (`0` central MAC key reconstruction, private pairwise zero-shares!). The rounds
/// are those of the per-party phase states, run by [`barrier_rounds_in_process`].
#[allow(clippy::too_many_arguments)]
fn evaluate_per_party_intents_barrier_inner<B: AcceleratorBackend>(
    policy: &TransactionPolicy,
    per_party_intents: &[TransactionIntent],
    session_id: [u8; 32],
    current_timestamp: u64,
    quorum_guards: &mut [PolicySignerGuardShare],
    mut shared_ledger: Option<&mut SharedWindowSpendLedger>,
    force_authenticated_initiator: bool,
    #[cfg(test)] injected_delta_fault: Option<(usize, (u128, u128))>,
    accel: &B,
) -> Result<AuthorizedSignReleaseToken, PolicyViolation> {
    let m = quorum_guards.len();
    if m < 2 || per_party_intents.len() != m {
        return Err(PolicyViolation::EmptySignerBarrierSet);
    }

    let mut quorum_ids: Vec<u16> = quorum_guards.iter().map(|g| g.party_id).collect();
    quorum_ids.sort_unstable();
    if quorum_ids.windows(2).any(|w| w[0] == w[1]) {
        return Err(PolicyViolation::DuplicateApproverInQuorum);
    }
    let mut projected_spends = Vec::with_capacity(m);
    for (guard, intent) in quorum_guards.iter().zip(per_party_intents) {
        policy.evaluate(intent)?;
        if current_timestamp < policy.valid_not_before_secs
            || current_timestamp > policy.valid_not_after_secs
            || current_timestamp != intent.timestamp_secs
        {
            return Err(PolicyViolation::TimestampOutsideWindow);
        }
        if guard.poisoned {
            return Err(PolicyViolation::GuardPoisoned);
        }
        if guard.active_phase.is_some() || guard.party_id != guard.enrolled_party_id {
            return Err(PolicyViolation::BarrierBdozMacFailed);
        }
        let mut approvers = intent.approver_parties.clone();
        approvers.sort_unstable();
        if approvers != quorum_ids
            || intent.quorum_ids != quorum_ids
            || intent.session_id != session_id
        {
            return Err(PolicyViolation::IntentBindingMismatch);
        }
        if shared_ledger.is_none() && !guard.has_global_velocity_intersection(policy, &quorum_ids) {
            return Err(PolicyViolation::MissingHardwareGuardian);
        }
        guard.verify_initiator_authentication(policy, intent, force_authenticated_initiator)?;
        let external_floor = if let Some(ledger) = shared_ledger.as_deref() {
            let _ = ledger.check_projected_spend(policy, intent, &session_id)?;
            ledger
                .accumulated_window_spend()
                .max(intent.rolling_window_spent)
        } else {
            intent.rolling_window_spent
        };
        let projected = guard.check_window_nonce_and_projected_spend(
            policy.velocity_window_cap,
            intent,
            &session_id,
            external_floor,
        )?;
        projected_spends.push(projected);
    }
    let policy_digest = policy.canonical_digest();

    // Verify all guards have an available preprocessing slot before advancing any slot latch.
    for g in quorum_guards.iter() {
        let slot = g.next_slot.get();
        if slot >= g.preproc_r.len() {
            return Err(PolicyViolation::BarrierPreprocExhausted);
        }
        for &peer in &quorum_ids {
            if peer != g.party_id {
                g.outgoing_mac(peer, slot)?;
            }
        }
    }

    // Latch one preprocessing slot per guard. From here every exit retires these slots.
    let sessions: Vec<PartyPolicyDeltaCommitMsg> = quorum_guards
        .iter()
        .zip(per_party_intents)
        .map(|(g, intent)| {
            let slot = g.next_slot.get();
            g.next_slot.set(slot + 1);
            PartyPolicyDeltaCommitMsg {
                party_id: g.party_id,
                slot,
                session_id,
                initiator_party: intent.initiator_party,
                window_id: intent.window_id,
                quorum_ids: quorum_ids.clone(),
                policy_digest,
                intent_digest: intent.canonical_digest(),
                commitment: [0; 32],
            }
        })
        .collect();
    let online_res = barrier_rounds_in_process(
        &sessions,
        quorum_guards,
        per_party_intents,
        #[cfg(test)]
        injected_delta_fault,
        accel,
    );

    let peer_slots_of = |party_id: u16| -> Vec<(u16, usize)> {
        sessions
            .iter()
            .filter(|peer| peer.party_id != party_id)
            .map(|peer| (peer.party_id, peer.slot))
            .collect()
    };
    let abort_all = |quorum_guards: &mut [PolicySignerGuardShare]| {
        for (g_abort, own) in quorum_guards.iter_mut().zip(&sessions) {
            g_abort.abort_session_slot(own.slot, &peer_slots_of(g_abort.party_id));
        }
    };
    let (permit, _sigma_commits) = match online_res {
        Ok(rounds) => rounds,
        Err(err) => {
            abort_all(quorum_guards);
            return Err(err);
        }
    };

    let global_projected = projected_spends.iter().copied().max().unwrap_or(0);
    if let Some(ledger) = shared_ledger.as_deref_mut()
        && let Err(err) =
            ledger.record_approved_intent(global_projected, per_party_intents[0].nonce, session_id)
    {
        // The openings of this session exist: its own and peer slots are spent either way.
        abort_all(quorum_guards);
        return Err(err);
    }

    // Atomically advance accumulated window spend, burn intent nonces + session ID, and retire slots.
    let mut record_failure = None;
    for (idx, g) in quorum_guards.iter_mut().enumerate() {
        let peer_slots = peer_slots_of(g.party_id);
        let recorded_spend = if shared_ledger.is_some() {
            projected_spends[idx].max(global_projected)
        } else {
            projected_spends[idx]
        };
        let recorded = g.record_approved_intent(
            policy.velocity_window_cap,
            recorded_spend,
            per_party_intents[idx].nonce,
            session_id,
        );
        g.abort_session_slot(sessions[idx].slot, &peer_slots);
        if let Err(err) = recorded {
            // The verified guard refused a spend the barrier approved: nothing is released.
            g.poison();
            record_failure = Some(err);
            break;
        }
    }
    if let Some(err) = record_failure {
        abort_all(quorum_guards);
        return Err(err);
    }

    AuthorizedSignReleaseToken::mint(
        permit,
        session_id,
        policy_digest,
        sessions[0].intent_digest,
        per_party_intents[0].clone(),
    )
}

/// The four barrier rounds for guards that share one process, after the caller latched
/// the slot named in each guard's entry of `sessions` (commitment still unset). Every
/// value is derived by the functions the per-party phase states use (`masked_policy_wire`,
/// `delta_commitment`, `committed_sigma`, `release_committed_sigmas`); only the message
/// passing is elided. Returns the release permit of the sigma opening and the frozen
/// sigma commitments, sorted by party.
fn barrier_rounds_in_process<B: AcceleratorBackend>(
    sessions: &[PartyPolicyDeltaCommitMsg],
    quorum_guards: &[PolicySignerGuardShare],
    per_party_intents: &[TransactionIntent],
    #[cfg(test)] injected_delta_fault: Option<(usize, (u128, u128))>,
    accel: &B,
) -> Result<
    (
        qsag_verified::OpeningReleasePermit,
        Vec<PartyPolicySigmaCommitMsg>,
    ),
    PolicyViolation,
> {
    let m = sessions.len();

    // Round 1: every guard commits to its masked wire.
    let mut own_commits: Vec<PartyPolicyDeltaCommitMsg> = Vec::with_capacity(m);
    let mut folded = Vec::with_capacity(m);
    let mut delta_opens = Vec::with_capacity(m);
    for ((g, intent), session) in quorum_guards.iter().zip(per_party_intents).zip(sessions) {
        let mut own = session.clone();
        let MaskedWire {
            folded: folded_x,
            delta,
            salt,
        } = g.masked_policy_wire(&own, &intent.nonce, accel)?;
        #[cfg(test)]
        let delta = match injected_delta_fault {
            Some((fault_index, fault)) if fault_index == own_commits.len() => {
                [delta[0] ^ fault.0, delta[1] ^ fault.1]
            }
            _ => delta,
        };
        own.commitment = delta_commitment(&own, &salt, &delta);
        delta_opens.push(PartyPolicyDeltaOpenMsg {
            party_id: g.party_id,
            salt_i: salt,
            delta_i: delta,
        });
        folded.push(folded_x);
        own_commits.push(own);
    }

    // Rounds 2 and 3: with the whole delta commitment vector frozen, every guard checks
    // the openings and commits to its sigma share. No sigma is opened before all exist.
    let mut delta_commits = own_commits.clone();
    delta_commits.sort_by_key(|c| c.party_id);
    delta_opens.sort_by_key(|o| o.party_id);
    let mut sigma_commits = Vec::with_capacity(m);
    /// Party, sigma commitment salt and sigma lanes.
    type SigmaOpening = (u16, [u8; 32], [u128; 2]);
    let mut deferred_openings: SecretVec<SigmaOpening> = SecretVec::with_capacity(m);
    for ((g, own), folded_x) in quorum_guards.iter().zip(&own_commits).zip(&folded) {
        let (msg, sigma, salt) = g.committed_sigma(own, folded_x, &delta_commits, &delta_opens)?;
        sigma_commits.push(msg);
        deferred_openings.push_wiping((g.party_id, *salt, *sigma));
    }
    sigma_commits.sort_by_key(|c| c.party_id);

    // Round 4. Guards that evaluated different intents froze different transcripts.
    let (first_delta, first_sigma) = delta_commits
        .first()
        .zip(sigma_commits.first())
        .ok_or(PolicyViolation::EmptySignerBarrierSet)?;
    let mut one_transcript = true;
    for (d, c) in delta_commits.iter().zip(&sigma_commits) {
        one_transcript &= ct_eq_bytes(&d.intent_digest, &first_delta.intent_digest);
        one_transcript &= ct_eq_bytes(&c.transcript_digest, &first_sigma.transcript_digest);
    }
    if !one_transcript {
        return Err(PolicyViolation::BarrierBdozMacFailed);
    }
    let mut sigma_opens: Vec<PartyPolicySigmaOpenMsg> = deferred_openings
        .iter()
        .map(|(party_id, salt, sigma)| PartyPolicySigmaOpenMsg {
            party_id: *party_id,
            sigma_salt_i: *salt,
            sigma_i: *sigma,
        })
        .collect();
    sigma_opens.sort_by_key(|o| o.party_id);
    let permit = release_committed_sigmas(
        &first_delta.session_id,
        first_delta.slot as u64,
        &sigma_commits,
        &sigma_opens,
    )?;
    Ok((permit, sigma_commits))
}

/// Evaluate `policy` across `guards`; peer/session MAC or commitment faults abort ONLY the
/// consumed session slot on each guard without wiping persistent guard keys or spend ledgers.
pub fn evaluate_per_party_intents_barrier<B: AcceleratorBackend>(
    policy: &TransactionPolicy,
    intents: &[TransactionIntent],
    session_id: [u8; 32],
    current_timestamp: u64,
    guards: &mut [PolicySignerGuardShare],
    #[cfg(test)] fault: Option<(usize, (u128, u128))>,
    accel: &B,
) -> Result<AuthorizedSignReleaseToken, PolicyViolation> {
    evaluate_per_party_intents_barrier_inner(
        policy,
        intents,
        session_id,
        current_timestamp,
        guards,
        None,
        false,
        #[cfg(test)]
        fault,
        accel,
    )
}

/// Evaluate `policy` on `intent` across `quorum_guards` inside a **commit-then-open** pairwise
/// 2-lane BDOZ GF($2^{128}$) MAC barrier (`AcceleratorBackend::bdoz_gf2_128_batch_dot`), returning
/// an unforgeable [`AuthorizedSignReleaseToken`] iff every signer approves and all MACs verify!
pub fn evaluate_policy_committed_barrier<B: AcceleratorBackend>(
    policy: &TransactionPolicy,
    intent: &TransactionIntent,
    session_id: [u8; 32],
    current_timestamp: u64,
    quorum_guards: &mut [PolicySignerGuardShare],
    accel: &B,
) -> Result<AuthorizedSignReleaseToken, PolicyViolation> {
    if quorum_guards.len() < 2 {
        return Err(PolicyViolation::EmptySignerBarrierSet);
    }
    let intents: Vec<TransactionIntent> =
        (0..quorum_guards.len()).map(|_| intent.clone()).collect();
    evaluate_per_party_intents_barrier(
        policy,
        &intents,
        session_id,
        current_timestamp,
        quorum_guards,
        #[cfg(test)]
        None,
        accel,
    )
}

/// Evaluate `policy` on `intent` across `quorum_guards` using a committee-wide
/// [`SharedWindowSpendLedger`] so non-intersecting quorums in guardian-less multi-quorum setups
/// enforce cumulative window velocity caps without quorum-switching bypass.
/// `persist` must atomically persist the shared and participating guard checkpoints, and
/// fence the shared generation in independent monotonic storage before returning success.
/// Hold exclusive ownership of that storage across recovery and this call. Never provision
/// another ledger for an existing policy: recover the checkpoint instead. Persistence errors
/// disable the live ledger and withhold the token; already consumed slots remain spent.
#[allow(clippy::too_many_arguments)]
pub fn evaluate_policy_committed_barrier_with_ledger<B: AcceleratorBackend>(
    policy: &TransactionPolicy,
    intent: &TransactionIntent,
    session_id: [u8; 32],
    current_timestamp: u64,
    quorum_guards: &mut [PolicySignerGuardShare],
    shared_ledger: &mut SharedWindowSpendLedger,
    persist: impl FnOnce(
        &SharedWindowSpendLedger,
        &[PolicySignerGuardShare],
    ) -> Result<(), PolicyViolation>,
    accel: &B,
) -> Result<AuthorizedSignReleaseToken, PolicyViolation> {
    if quorum_guards.len() < 2 {
        return Err(PolicyViolation::EmptySignerBarrierSet);
    }
    let intents: Vec<TransactionIntent> =
        (0..quorum_guards.len()).map(|_| intent.clone()).collect();
    let token = evaluate_per_party_intents_barrier_inner(
        policy,
        &intents,
        session_id,
        current_timestamp,
        quorum_guards,
        Some(&mut *shared_ledger),
        false,
        #[cfg(test)]
        None,
        accel,
    )?;
    // No token escapes until the common ledger and participating guard snapshots are durable.
    // Keep the handle disabled across errors and unwinding; recovery requires its checkpoint.
    shared_ledger.failed = true;
    persist(shared_ledger, quorum_guards)?;
    shared_ledger.failed = false;
    Ok(token)
}

/// Evaluate `policy` on `intent` across `quorum_guards` while mandating pairwise cryptographic
/// authentication of `intent.initiator_party` (`InitiatorPeerMac`) from the initiator guard share.
pub fn evaluate_policy_committed_barrier_authenticated<B: AcceleratorBackend>(
    policy: &TransactionPolicy,
    intent: &TransactionIntent,
    session_id: [u8; 32],
    current_timestamp: u64,
    quorum_guards: &mut [PolicySignerGuardShare],
    accel: &B,
) -> Result<AuthorizedSignReleaseToken, PolicyViolation> {
    if quorum_guards.len() < 2 {
        return Err(PolicyViolation::EmptySignerBarrierSet);
    }
    let intents: Vec<TransactionIntent> =
        (0..quorum_guards.len()).map(|_| intent.clone()).collect();
    evaluate_per_party_intents_barrier_inner(
        policy,
        &intents,
        session_id,
        current_timestamp,
        quorum_guards,
        None,
        true,
        #[cfg(test)]
        None,
        accel,
    )
}

/// Adapter for a mutually authenticated, malicious-secure, bidirectional 1-of-2 OT channel.
/// Each call sends one pair per choice and receives exactly the chosen peer values.
/// Implementations must bind both authenticated endpoint IDs, the domain and vector length,
/// reject replay, and hide sender alternatives and receiver choices. An ordinary channel
/// cannot implement this contract. Base OT and its security parameters belong to the provider.
/// Calls exchange both directions concurrently, avoiding ordering dependencies between peers.
pub trait PolicyAuthenticatedOt {
    fn exchange(
        &mut self,
        local_party: u16,
        peer: u16,
        domain: [u8; 32],
        alternatives: &[[u128; 2]],
        choices: &[bool],
    ) -> Result<Vec<u128>, PolicyViolation>;
}

/// Production adapter using the interactive KOS check and committed Ring-LWE base OT.
/// The ID ordering avoids crossed blocking sends on synchronous transports.
impl<W: qsag_fts::ot::AuthenticatedOtWire> PolicyAuthenticatedOt
    for qsag_fts::ot::CommittedCorrelatedOt<W>
{
    fn exchange(
        &mut self,
        local_party: u16,
        peer: u16,
        domain: [u8; 32],
        alternatives: &[[u128; 2]],
        choices: &[bool],
    ) -> Result<Vec<u128>, PolicyViolation> {
        if local_party != self.party_id() || alternatives.len() != choices.len() {
            return Err(PolicyViolation::IntentBindingMismatch);
        }
        let failed = |_| PolicyViolation::BarrierBdozMacFailed;
        let mut result = SecretVec::with_capacity(choices.len());
        for (index, (pairs, bits)) in alternatives
            .chunks(65_536)
            .zip(choices.chunks(65_536))
            .enumerate()
        {
            let context = cshake256_framed_32(
                b"QSAG.POLICY.OT.CHUNK.V1",
                &[
                    &domain,
                    &(index as u64).to_be_bytes(),
                    &(choices.len() as u64).to_be_bytes(),
                ],
            );
            let values = if local_party < peer {
                self.send_values(peer, context, pairs).map_err(failed)?;
                self.receive_values(peer, context, bits).map_err(failed)?
            } else {
                let values = self.receive_values(peer, context, bits).map_err(failed)?;
                self.send_values(peer, context, pairs).map_err(failed)?;
                values
            };
            let values = SecretVec::new(values);
            result.extend_wiping(&values);
        }
        Ok(result.into_inner())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PolicyGuardSeedCommitMsg {
    pub sender: u16,
    pub recipient: u16,
    pub setup_digest: [u8; 32],
    pub commitment: [u8; 32],
}

/// Send only over the private authenticated channel to `recipient`, never broadcast.
#[derive(Clone)]
pub struct PolicyGuardSeedOpenMsg {
    pub sender: u16,
    pub recipient: u16,
    pub setup_digest: [u8; 32],
    pub seed: [u8; 32],
}

impl Drop for PolicyGuardSeedOpenMsg {
    fn drop(&mut self) {
        wipe(&mut self.seed);
    }
}

pub struct PolicyGuardDkgRound1 {
    guard: PolicySignerGuardShare,
    ids: Vec<u16>,
    digest: [u8; 32],
    seeds: Vec<PolicyGuardSeedOpenMsg>,
}

pub struct PolicyGuardDkgRound2 {
    first: PolicyGuardDkgRound1,
    peer_commits: Vec<PolicyGuardSeedCommitMsg>,
}

fn policy_seed_commit(o: &PolicyGuardSeedOpenMsg) -> [u8; 32] {
    cshake256_framed_32(
        b"QSAG.POLICY.DKG.SEED_COMMIT.V1",
        &[
            &o.setup_digest,
            &o.sender.to_be_bytes(),
            &o.recipient.to_be_bytes(),
            &o.seed,
        ],
    )
}

impl PolicyGuardDkgRound1 {
    /// Each participant supplies independent private CSPRNG entropy and a fresh setup ID.
    /// No participant provides any other participant's entropy or guard secrets.
    pub fn new(
        party_id: u16,
        party_ids: &[u16],
        setup_id: [u8; 32],
        entropy: [u8; 32],
    ) -> Result<(Self, Vec<PolicyGuardSeedCommitMsg>), PolicyViolation> {
        Self::new_with_capacity(party_id, party_ids, setup_id, entropy, BDOZ_PREPROC_SLOTS)
    }

    /// Provision a caller-sized pool. The capacity is committed into the ceremony transcript.
    pub fn new_with_capacity(
        party_id: u16,
        party_ids: &[u16],
        setup_id: [u8; 32],
        mut entropy: [u8; 32],
        preprocessing_slots: usize,
    ) -> Result<(Self, Vec<PolicyGuardSeedCommitMsg>), PolicyViolation> {
        if preprocessing_slots == 0 || preprocessing_slots > MAX_POLICY_CAPACITY {
            wipe(&mut entropy);
            return Err(PolicyViolation::BarrierPreprocExhausted);
        }
        let mut ids = party_ids.to_vec();
        ids.sort_unstable();
        if ids.len() < 2 || !ids.contains(&party_id) || ids.windows(2).any(|w| w[0] == w[1]) {
            wipe(&mut entropy);
            return Err(PolicyViolation::IntentBindingMismatch);
        }
        let digest = cshake256_framed_32(
            b"QSAG.POLICY.DKG.V1",
            &[
                &setup_id,
                &policy_ids_bytes(&ids),
                &(preprocessing_slots as u64).to_be_bytes(),
            ],
        );
        let mut local = cshake256_framed_32(
            b"QSAG.POLICY.DKG.LOCAL.V1",
            &[&entropy, &digest, &party_id.to_be_bytes()],
        );
        wipe(&mut entropy);
        let mut guard = PolicySignerGuardShare {
            party_id,
            enrolled_party_id: party_id,
            active_phase: None,
            poisoned: false,
            bdoz_alpha_share: policy_pair(&secret_digest(b"QSAG.POLICY.DKG.ALPHA.V1", &[&local])),
            window_authority: None,
            durable_key_id: cshake256_framed_32(b"QSAG.POLICY.DURABLE_KEY.V2", &[&local]),
            durable_generation: Cell::new(0),
            verified_velocity: None,
            velocity_generation: 0,
            local_salt_seed: local,
            pairwise_zero_seeds: Vec::with_capacity(ids.len() - 1),
            preproc_r: Vec::with_capacity(preprocessing_slots),
            preproc_outgoing_macs: Vec::with_capacity(ids.len() - 1),
            preproc_incoming_keys: Vec::with_capacity(ids.len() - 1),
            consumed_peer_slots: Vec::new(),
            next_slot: Cell::new(0),
            current_window_id: 0,
            accumulated_window_spend: 0,
            replay_capacity: MAX_BURNED_INTENT_NONCES,
            burned_intent_nonces: Vec::new(),
            min_nonce_watermark: None,
            burned_sessions: Vec::new(),
            min_session_watermark: None,
            require_authenticated_initiator: true,
        };
        wipe(&mut local);
        for slot in 0..preprocessing_slots {
            guard.preproc_r.push(policy_pair(&secret_digest(
                b"QSAG.POLICY.DKG.R.V1",
                &[&guard.local_salt_seed, &(slot as u64).to_be_bytes()],
            )));
        }
        let mut seeds = Vec::with_capacity(ids.len() - 1);
        let mut commits = Vec::new();
        for &peer in &ids {
            if peer == party_id {
                continue;
            }
            let o = PolicyGuardSeedOpenMsg {
                sender: party_id,
                recipient: peer,
                setup_digest: digest,
                seed: cshake256_framed_32(
                    b"QSAG.POLICY.DKG.SEED.V1",
                    &[&guard.local_salt_seed, &peer.to_be_bytes()],
                ),
            };
            commits.push(PolicyGuardSeedCommitMsg {
                sender: party_id,
                recipient: peer,
                setup_digest: digest,
                commitment: policy_seed_commit(&o),
            });
            seeds.push(o);
        }
        Ok((
            Self {
                guard,
                ids,
                digest,
                seeds,
            },
            commits,
        ))
    }

    /// Accept exactly one authenticated directed commitment from every other participant.
    pub fn round2_open_seeds(
        self,
        peer_commits: &[PolicyGuardSeedCommitMsg],
    ) -> Result<(PolicyGuardDkgRound2, Vec<PolicyGuardSeedOpenMsg>), PolicyViolation> {
        let peers: Vec<_> = self
            .ids
            .iter()
            .copied()
            .filter(|p| *p != self.guard.party_id)
            .collect();
        let mut commits = peer_commits.to_vec();
        commits.sort_by_key(|c| c.sender);
        if commits.len() != peers.len() {
            return Err(PolicyViolation::IntentBindingMismatch);
        }
        for (c, peer) in commits.iter().zip(peers) {
            if c.sender != peer
                || c.recipient != self.guard.party_id
                || !ct_eq_bytes(&c.setup_digest, &self.digest)
            {
                return Err(PolicyViolation::IntentBindingMismatch);
            }
        }
        let opens = self.seeds.clone();
        Ok((
            PolicyGuardDkgRound2 {
                first: self,
                peer_commits: commits,
            },
            opens,
        ))
    }
}

fn policy_ot_pad_stream(
    seed: &[u8; 32],
    domain: &[u8; 32],
    sender: u16,
    receiver: u16,
    start: usize,
) -> qsag_accel::keccak::Shake256 {
    let mut pads = qsag_accel::keccak::init_cshake256(b"", b"QSAG.POLICY.DKG.OT_PAD_STREAM.V2");
    pads.absorb(seed);
    pads.absorb(domain);
    pads.absorb(&sender.to_be_bytes());
    pads.absorb(&receiver.to_be_bytes());
    pads.absorb(&(start as u64).to_be_bytes());
    qsag_accel::keccak::finalize_cshake256(&mut pads, true);
    pads
}

/// Complete pairwise preprocessing without any shared master secret or dealer.
/// OT authenticates each private r bit under the peer's private per-`(peer, slot)` alpha.
/// XOR of the 128 selected values is M; XOR of the sender pads is K, hence M = K + alpha_{peer,slot} * r.
/// The two lanes use separate transfers. Seed openings are private to their endpoints.
/// On every error the owned partial guard and seed material are erased by Drop.
pub fn finalize_distributed_policy_guard<O: PolicyAuthenticatedOt>(
    mut state: PolicyGuardDkgRound2,
    peer_openings: &[PolicyGuardSeedOpenMsg],
    ot: &mut O,
) -> Result<PolicySignerGuardShare, PolicyViolation> {
    let mut opens: Vec<_> = peer_openings.iter().collect();
    opens.sort_by_key(|o| o.sender);
    if opens.len() != state.peer_commits.len() {
        return Err(PolicyViolation::IntentBindingMismatch);
    }
    for (c, o) in state.peer_commits.iter().zip(&opens) {
        if c.sender != o.sender
            || c.recipient != o.recipient
            || !ct_eq_bytes(&c.setup_digest, &o.setup_digest)
            || !ct_eq_bytes(&c.commitment, &policy_seed_commit(o))
        {
            return Err(PolicyViolation::BarrierCommitmentMismatch { party_id: c.sender });
        }
    }
    for o in opens {
        let g = &mut state.first.guard;
        let local = state
            .first
            .seeds
            .iter()
            .find(|s| s.recipient == o.sender)
            .ok_or(PolicyViolation::IntentBindingMismatch)?;
        let (lo_seed, hi_seed) = if g.party_id < o.sender {
            (&local.seed, &o.seed)
        } else {
            (&o.seed, &local.seed)
        };
        let domain = cshake256_framed_32(
            b"QSAG.POLICY.DKG.PAIR.V1",
            &[
                &state.first.digest,
                &g.party_id.min(o.sender).to_be_bytes(),
                &g.party_id.max(o.sender).to_be_bytes(),
            ],
        );
        g.pairwise_zero_seeds.push((
            o.sender,
            cshake256_framed_32(b"QSAG.POLICY.DKG.ZERO.V1", &[&domain, lo_seed, hi_seed]),
        ));
        g.consumed_peer_slots
            .push((o.sender, alloc::vec![0u64; g.preproc_r.len().div_ceil(64)]));
        let mut keys = SecretVec::with_capacity(g.preproc_r.len());
        let mut macs = SecretVec::with_capacity(g.preproc_r.len());
        // Bound scratch buffers independently of the caller's durable pool capacity.
        for start in (0..g.preproc_r.len()).step_by(256) {
            let end = (start + 256).min(g.preproc_r.len());
            let domain = if g.preproc_r.len() <= 256 {
                domain
            } else {
                cshake256_framed_32(
                    b"QSAG.POLICY.DKG.POOL_BATCH.V1",
                    &[
                        &domain,
                        &(start as u64).to_be_bytes(),
                        &(g.preproc_r.len() as u64).to_be_bytes(),
                    ],
                )
            };
            // One private, domain-separated stream per peer and pool batch. The
            // cursor gives distinct pads for every (slot, lane, bit).
            let mut pads =
                policy_ot_pad_stream(&g.local_salt_seed, &domain, g.party_id, o.sender, start);
            let mut alternatives = SecretVec::with_capacity((end - start) * 256);
            let mut choices = SecretVec::with_capacity((end - start) * 256);
            for slot in start..end {
                let slot_alpha = g.incoming_slot_alpha(o.sender, slot);
                let mut key = SecretBuffer([0u128; 2]);
                for (lane, key_lane) in key.iter_mut().enumerate() {
                    for bit in 0..128 {
                        let mut raw = SecretBuffer([0u8; 16]);
                        pads.squeeze(&mut raw[..]);
                        let pad = SecretBuffer(u128::from_le_bytes(*raw));
                        alternatives.push_wiping([
                            *pad,
                            *pad ^ gf2_128_mul(slot_alpha[lane], 1u128 << bit),
                        ]);
                        choices.push_wiping(((g.preproc_r[slot][lane] >> bit) & 1) != 0);
                        *key_lane ^= *pad;
                    }
                }
                keys.push_wiping(*key);
            }
            let selected = SecretVec::new(ot.exchange(
                g.party_id,
                o.sender,
                domain,
                &alternatives,
                &choices,
            )?);
            if selected.len() != (end - start) * 256 {
                return Err(PolicyViolation::BarrierBdozMacFailed);
            }
            for chunk in selected.as_chunks::<256>().0 {
                macs.push_wiping([
                    chunk[..128].iter().fold(0, |a, b| a ^ b),
                    chunk[128..].iter().fold(0, |a, b| a ^ b),
                ]);
            }
        }
        g.preproc_outgoing_macs.push((o.sender, macs.into_inner()));
        g.preproc_incoming_keys.push((o.sender, keys.into_inner()));
    }
    Ok(state.first.guard)
}

/// Public network envelopes require authenticated sender identities and reliable broadcast.
/// In particular, a caller must not accept an envelope merely because its ID is in the quorum.
/// The session ID must be fresh; durable slot storage is required across process restarts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartyPolicyDeltaCommitMsg {
    pub party_id: u16,
    pub slot: usize,
    pub session_id: [u8; 32],
    pub initiator_party: u16,
    pub window_id: u64,
    pub quorum_ids: Vec<u16>,
    pub policy_digest: [u8; 32],
    pub intent_digest: [u8; 32],
    pub commitment: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartyPolicyDeltaOpenMsg {
    pub party_id: u16,
    pub salt_i: [u8; 32],
    pub delta_i: [u128; 2],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartyPolicySigmaCommitMsg {
    pub party_id: u16,
    pub transcript_digest: [u8; 32],
    pub commitment: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartyPolicySigmaOpenMsg {
    pub party_id: u16,
    pub sigma_salt_i: [u8; 32],
    pub sigma_i: [u128; 2],
}

// No Clone or public constructors for any phase state.
struct PartyPolicyContext {
    intent: TransactionIntent,
    velocity_window_cap: u128,
    cumulative_epoch_spent: u128,
    own: PartyPolicyDeltaCommitMsg,
    peer_slots: Vec<(u16, usize)>,
    guard_binding: [u8; 32],
    salt: [u8; 32],
    delta: [u128; 2],
    folded: [u128; 2],
    sigma: [u128; 2],
    sigma_salt: [u8; 32],
}

impl Drop for PartyPolicyContext {
    fn drop(&mut self) {
        wipe(&mut self.guard_binding);
        wipe(&mut self.salt);
        wipe(&mut self.sigma_salt);
        wipe(&mut self.delta);
        wipe(&mut self.folded);
        wipe(&mut self.sigma);
    }
}

/// Owns the pending opening. A session that cannot continue (a peer went silent or the
/// transport failed) is ended with `abort`, which retires its slots and frees the guard for
/// the next session. Merely dropping a state leaves its guard latched: the next session
/// start on that guard is treated as an overlap and poisons it.
#[must_use]
pub struct PartyPolicyRound1State {
    context: PartyPolicyContext,
}
/// All delta commitments are frozen; verify every opening before producing sigma.
#[must_use]
pub struct PartyPolicyRound2State {
    context: PartyPolicyContext,
    commits: Vec<PartyPolicyDeltaCommitMsg>,
}
/// Sigma is committed but remains private until the complete commitment vector is frozen.
#[must_use]
pub struct PartyPolicyRound3State {
    context: PartyPolicyContext,
    own_sigma: PartyPolicySigmaCommitMsg,
}
/// Only this state can verify sigma openings and mint the per-party capability.
#[must_use]
pub struct PartyPolicyFinalizeState {
    context: PartyPolicyContext,
    commits: Vec<PartyPolicySigmaCommitMsg>,
}

fn policy_ids_bytes(ids: &[u16]) -> Vec<u8> {
    ids.iter().flat_map(|id| id.to_be_bytes()).collect()
}

fn policy_pair_bytes(pair: &[u128; 2]) -> [u8; 32] {
    let mut bytes = [0; 32];
    bytes[..16].copy_from_slice(&pair[0].to_le_bytes());
    bytes[16..].copy_from_slice(&pair[1].to_le_bytes());
    bytes
}

fn policy_pair(bytes: &[u8; 32]) -> [u128; 2] {
    [
        u128::from_le_bytes(core::array::from_fn(|i| bytes[i])),
        u128::from_le_bytes(core::array::from_fn(|i| bytes[16 + i])),
    ]
}

/// A digest derived from guard secrets, erased when it leaves scope.
fn secret_digest(domain: &[u8], fields: &[&[u8]]) -> SecretBytes<32> {
    SecretBuffer(cshake256_framed_32(domain, fields))
}

fn delta_commitment(c: &PartyPolicyDeltaCommitMsg, salt: &[u8; 32], delta: &[u128; 2]) -> [u8; 32] {
    cshake256_framed_32(
        b"QSAG.POLICY.DELTA_COMMIT.V2",
        &[
            &c.session_id,
            &c.party_id.to_be_bytes(),
            &c.initiator_party.to_be_bytes(),
            &c.window_id.to_be_bytes(),
            &policy_ids_bytes(&c.quorum_ids),
            &c.intent_digest,
            salt,
            &policy_pair_bytes(delta),
            &c.policy_digest,
            &(c.slot as u64).to_be_bytes(),
        ],
    )
}

fn sigma_commitment(c: &PartyPolicySigmaCommitMsg, salt: &[u8; 32], sigma: &[u128; 2]) -> [u8; 32] {
    cshake256_framed_32(
        b"QSAG.POLICY.SIGMA_COMMIT.V1",
        &[
            &c.transcript_digest,
            &c.party_id.to_be_bytes(),
            salt,
            &policy_pair_bytes(sigma),
        ],
    )
}

/// The values one guard derives in barrier round 1: the folded policy wire, that wire
/// masked with the guard's preprocessed `r` of the session slot, and the salt of the
/// delta commitment.
struct MaskedWire {
    folded: [u128; 2],
    delta: [u128; 2],
    salt: [u8; 32],
}

/// The values one guard derives in barrier round 3: its sigma commitment message, its
/// sigma share and the salt of the commitment.
type CommittedSigma = (
    PartyPolicySigmaCommitMsg,
    SecretBuffer<[u128; 2]>,
    SecretBytes<32>,
);

// The round derivations of the committed barrier. The per-party phase states and the
// in-process barrier both call these and nothing else, so one session produces the same
// commitments, transcript digest and sigma shares on either path.
impl PolicySignerGuardShare {
    /// Round 1 for the session `own` describes.
    fn masked_policy_wire<B: AcceleratorBackend>(
        &self,
        own: &PartyPolicyDeltaCommitMsg,
        intent_nonce: &[u8; 32],
        accel: &B,
    ) -> Result<MaskedWire, PolicyViolation> {
        let r = SecretBuffer(
            *self
                .preproc_r
                .get(own.slot)
                .ok_or(PolicyViolation::BarrierPreprocExhausted)?,
        );
        let x = compute_folded_policy_wire(
            &own.policy_digest,
            &own.intent_digest,
            &own.session_id,
            own.initiator_party,
            own.window_id,
            intent_nonce,
            accel,
        )?;
        let salt = cshake256_framed_32(
            b"QSAG.POLICY.DELTA_SALT.V1",
            &[
                &self.local_salt_seed,
                &own.session_id,
                &(own.slot as u64).to_be_bytes(),
            ],
        );
        Ok(MaskedWire {
            folded: [x.0, x.1],
            delta: [r[0] ^ x.0, r[1] ^ x.1],
            salt,
        })
    }

    /// Round 3 for the session `own` describes: check every delta opening against its
    /// frozen commitment, bind the verified openings into the transcript digest, and
    /// derive this guard's sigma share with its commitment. `commits` and `opens` are
    /// sorted by party and cover `own.quorum_ids`.
    fn committed_sigma(
        &self,
        own: &PartyPolicyDeltaCommitMsg,
        folded: &[u128; 2],
        commits: &[PartyPolicyDeltaCommitMsg],
        opens: &[PartyPolicyDeltaOpenMsg],
    ) -> Result<CommittedSigma, PolicyViolation> {
        if opens.len() != commits.len() {
            return Err(PolicyViolation::IntentBindingMismatch);
        }
        let mut transcript = Vec::new();
        for (c, o) in commits.iter().zip(opens) {
            if c.party_id != o.party_id
                || !ct_eq_bytes(&c.commitment, &delta_commitment(c, &o.salt_i, &o.delta_i))
            {
                return Err(PolicyViolation::BarrierCommitmentMismatch {
                    party_id: c.party_id,
                });
            }
            transcript.extend_from_slice(&c.party_id.to_be_bytes());
            transcript.extend_from_slice(&(c.slot as u64).to_be_bytes());
            transcript.extend_from_slice(&c.commitment);
            transcript.extend_from_slice(&o.salt_i);
            transcript.extend_from_slice(&policy_pair_bytes(&o.delta_i));
        }
        let q_digest = cshake256_framed_32(
            b"QSAG.POLICY.QUORUM_SET.V2",
            &[&policy_ids_bytes(&own.quorum_ids)],
        );
        let digest = cshake256_framed_32(
            b"QSAG.POLICY.VERIFIED_DELTAS.V2",
            &[
                &own.session_id,
                &own.initiator_party.to_be_bytes(),
                &own.window_id.to_be_bytes(),
                &own.policy_digest,
                &own.intent_digest,
                &q_digest,
                &transcript,
            ],
        );
        let mut sigma = self.pairwise_zero_share(&own.quorum_ids, &own.session_id, &q_digest);
        for (c, o) in commits.iter().zip(opens) {
            if c.party_id == own.party_id {
                continue;
            }
            let m = SecretBuffer(self.outgoing_mac(c.party_id, own.slot)?);
            let k = SecretBuffer(self.incoming_key(c.party_id, c.slot)?);
            let peer_alpha = self.incoming_slot_alpha(c.party_id, c.slot);
            let chi = policy_pair(&cshake256_framed_32(
                b"QSAG.POLICY.PAIR_WEIGHT.V3",
                &[
                    &digest,
                    &own.party_id.min(c.party_id).to_be_bytes(),
                    &own.party_id.max(c.party_id).to_be_bytes(),
                ],
            ));
            for lane in 0..2 {
                sigma[lane] ^= gf2_128_mul(
                    chi[lane],
                    m[lane]
                        ^ k[lane]
                        ^ gf2_128_mul(peer_alpha[lane], folded[lane] ^ o.delta_i[lane]),
                );
            }
        }
        let salt = secret_digest(
            b"QSAG.POLICY.SIGMA_SALT.V1",
            &[
                &self.local_salt_seed,
                &digest,
                &(own.slot as u64).to_be_bytes(),
            ],
        );
        let mut msg = PartyPolicySigmaCommitMsg {
            party_id: own.party_id,
            transcript_digest: digest,
            commitment: [0; 32],
        };
        msg.commitment = sigma_commitment(&msg, &salt, &sigma);
        Ok((msg, sigma, salt))
    }
}

/// Round 4 verification: every sigma opening against its frozen commitment, then the
/// zero-sum release decision of the extracted single-use guard, bound to the transcript
/// digest the commitments froze. `commits` and `opens` are sorted by party.
fn release_committed_sigmas(
    session_id: &[u8; 32],
    round_id: u64,
    commits: &[PartyPolicySigmaCommitMsg],
    opens: &[PartyPolicySigmaOpenMsg],
) -> Result<qsag_verified::OpeningReleasePermit, PolicyViolation> {
    if opens.len() != commits.len() {
        return Err(PolicyViolation::IntentBindingMismatch);
    }
    let mut sigma_openings = Vec::with_capacity(opens.len());
    for (c, o) in commits.iter().zip(opens) {
        let recomputed = sigma_commitment(c, &o.sigma_salt_i, &o.sigma_i);
        if c.party_id != o.party_id || !ct_eq_bytes(&c.commitment, &recomputed) {
            return Err(PolicyViolation::BarrierCommitmentMismatch {
                party_id: c.party_id,
            });
        }
        sigma_openings.push((c.commitment, recomputed, o.sigma_i));
    }
    let binding = commits
        .first()
        .map(|c| c.transcript_digest)
        .ok_or(PolicyViolation::IntentBindingMismatch)?;
    release_sigma_round(session_id, round_id, &binding, &sigma_openings)
}

impl PolicySignerGuardShare {
    fn phase_binding(&self, slot: usize) -> [u8; 32] {
        cshake256_framed_32(
            b"QSAG.POLICY.GUARD_BINDING.V1",
            &[
                &self.local_salt_seed,
                &self.enrolled_party_id.to_be_bytes(),
                &(slot as u64).to_be_bytes(),
            ],
        )
    }

    fn check_phase(&mut self, c: &PartyPolicyContext, phase: u8) -> Result<(), PolicyViolation> {
        if self.poisoned {
            return Err(PolicyViolation::GuardPoisoned);
        }
        if self.party_id != self.enrolled_party_id
            || self.party_id != c.own.party_id
            || self.active_phase != Some((c.own.slot, phase))
            || !ct_eq_bytes(&self.phase_binding(c.own.slot), &c.guard_binding)
        {
            self.poison();
            return Err(PolicyViolation::IntentBindingMismatch);
        }
        Ok(())
    }

    fn round1_commit_intent_inner(
        &mut self,
        policy: &TransactionPolicy,
        intent: &TransactionIntent,
        session_id: [u8; 32],
        current_timestamp: u64,
        cumulative_epoch_spent: u128,
        force_authenticated_initiator: bool,
    ) -> Result<(PartyPolicyRound1State, PartyPolicyDeltaCommitMsg), PolicyViolation> {
        if self.poisoned {
            return Err(PolicyViolation::GuardPoisoned);
        }
        if self.active_phase.is_some() || self.party_id != self.enrolled_party_id {
            self.poison();
            return Err(PolicyViolation::IntentBindingMismatch);
        }
        policy.evaluate(intent)?;
        if current_timestamp != intent.timestamp_secs {
            return Err(PolicyViolation::TimestampOutsideWindow);
        }
        if cumulative_epoch_spent != intent.rolling_window_spent {
            return Err(PolicyViolation::VelocityCapOverflowOrExceeded);
        }
        self.verify_initiator_authentication(policy, intent, force_authenticated_initiator)?;
        self.check_window_nonce_and_projected_spend(
            policy.velocity_window_cap,
            intent,
            &session_id,
            cumulative_epoch_spent,
        )?;
        let mut ids = intent.approver_parties.clone();
        ids.sort_unstable();
        if ids.len() < 2
            || ids != intent.quorum_ids
            || !ids.contains(&self.party_id)
            || session_id != intent.session_id
        {
            return Err(PolicyViolation::IntentBindingMismatch);
        }
        if !self.has_global_velocity_intersection(policy, &ids) {
            return Err(PolicyViolation::MissingHardwareGuardian);
        }
        let slot = self.next_slot.get();
        if slot >= self.preproc_r.len() {
            return Err(PolicyViolation::BarrierPreprocExhausted);
        }
        for &peer in &ids {
            if peer != self.party_id {
                self.outgoing_mac(peer, slot)?;
                if !self.pairwise_zero_seeds.iter().any(|(id, _)| *id == peer) {
                    return Err(PolicyViolation::BarrierBdozMacFailed);
                }
            }
        }
        self.next_slot.set(slot + 1);
        self.active_phase = Some((slot, 1));
        let mut own = PartyPolicyDeltaCommitMsg {
            party_id: self.party_id,
            slot,
            session_id,
            initiator_party: intent.initiator_party,
            window_id: intent.window_id,
            quorum_ids: ids,
            policy_digest: policy.canonical_digest(),
            intent_digest: intent.canonical_digest(),
            commitment: [0; 32],
        };
        let MaskedWire {
            folded,
            delta,
            salt,
        } = match self.masked_policy_wire(
            &own,
            &intent.nonce,
            &qsag_accel::CpuReferenceBackend::new(),
        ) {
            Ok(v) => v,
            Err(err) => {
                self.abort_session_slot(slot, &[]);
                return Err(err);
            }
        };
        own.commitment = delta_commitment(&own, &salt, &delta);
        let context = PartyPolicyContext {
            intent: intent.clone(),
            velocity_window_cap: policy.velocity_window_cap,
            cumulative_epoch_spent,
            own: own.clone(),
            peer_slots: Vec::new(),
            guard_binding: self.phase_binding(slot),
            salt,
            delta,
            folded,
            sigma: [0; 2],
            sigma_salt: [0; 32],
        };
        Ok((PartyPolicyRound1State { context }, own))
    }

    /// Clock and epoch spend must come from local authoritative state, never from the requester.
    pub fn round1_commit_intent(
        &mut self,
        policy: &TransactionPolicy,
        intent: &TransactionIntent,
        session_id: [u8; 32],
        current_timestamp: u64,
        cumulative_epoch_spent: u128,
    ) -> Result<(PartyPolicyRound1State, PartyPolicyDeltaCommitMsg), PolicyViolation> {
        self.round1_commit_intent_inner(
            policy,
            intent,
            session_id,
            current_timestamp,
            cumulative_epoch_spent,
            false,
        )
    }

    /// Commit to `intent` while mandating cryptographic authentication of `intent.initiator_party`.
    pub fn round1_commit_intent_authenticated(
        &mut self,
        policy: &TransactionPolicy,
        intent: &TransactionIntent,
        session_id: [u8; 32],
        current_timestamp: u64,
        cumulative_epoch_spent: u128,
    ) -> Result<(PartyPolicyRound1State, PartyPolicyDeltaCommitMsg), PolicyViolation> {
        self.round1_commit_intent_inner(
            policy,
            intent,
            session_id,
            current_timestamp,
            cumulative_epoch_spent,
            true,
        )
    }
}

impl PolicySignerGuardShare {
    /// End the session that `context` owns in `phase` without releasing anything: its own
    /// slot and every peer slot it was shown are retired, the ledger is untouched. A state
    /// presented to a guard that does not own it poisons that guard, as in every phase.
    fn abandon_session(
        &mut self,
        context: &PartyPolicyContext,
        phase: u8,
    ) -> Result<(), PolicyViolation> {
        self.check_phase(context, phase)?;
        self.abort_session_slot(context.own.slot, &context.peer_slots);
        Ok(())
    }
}

macro_rules! policy_phase_abort {
    ($($state:ty => $phase:literal),* $(,)?) => {$(
        impl $state {
            /// Abandon this session on `guard`, retiring its preprocessing slots. The guard
            /// keeps its keys and ledger and can start another session. Persist a checkpoint
            /// afterwards so the retired slots stay retired across a restart.
            pub fn abort(self, guard: &mut PolicySignerGuardShare) -> Result<(), PolicyViolation> {
                guard.abandon_session(&self.context, $phase)
            }
        }
    )*};
}
policy_phase_abort!(
    PartyPolicyRound1State => 1,
    PartyPolicyRound2State => 2,
    PartyPolicyRound3State => 3,
    PartyPolicyFinalizeState => 4,
);

/// Abort ONLY the active session slot (and any opened peer slots) on peer/network protocol errors,
/// preserving the honest party's persistent guard key material and durable spend/nonce ledger.
fn policy_phase_result<T>(
    guard: &mut PolicySignerGuardShare,
    slot: usize,
    peer_slots: &[(u16, usize)],
    result: Result<T, PolicyViolation>,
) -> Result<T, PolicyViolation> {
    if result.is_err() {
        guard.abort_session_slot(slot, peer_slots);
    }
    result
}

impl PartyPolicyRound1State {
    /// Freeze the entire delta commitment vector before releasing this party's opening.
    pub fn round2_open_delta_and_commit_sigma(
        self,
        guard: &mut PolicySignerGuardShare,
        all_r1_commits: &[PartyPolicyDeltaCommitMsg],
    ) -> Result<(PartyPolicyRound2State, PartyPolicyDeltaOpenMsg), PolicyViolation> {
        self.round2_open_delta(guard, all_r1_commits)
    }

    pub fn round2_open_delta(
        mut self,
        guard: &mut PolicySignerGuardShare,
        all_r1_commits: &[PartyPolicyDeltaCommitMsg],
    ) -> Result<(PartyPolicyRound2State, PartyPolicyDeltaOpenMsg), PolicyViolation> {
        guard.check_phase(&self.context, 1)?;
        let own_slot = self.context.own.slot;
        let result = (|| {
            let own = &self.context.own;
            let mut commits = all_r1_commits.to_vec();
            commits.sort_by_key(|c| c.party_id);
            if commits.len() != own.quorum_ids.len() {
                return Err(PolicyViolation::IntentBindingMismatch);
            }
            let mut peer_slots = Vec::with_capacity(commits.len().saturating_sub(1));
            for (c, id) in commits.iter().zip(&own.quorum_ids) {
                if c.party_id != *id
                    || c.session_id != own.session_id
                    || c.initiator_party != own.initiator_party
                    || c.window_id != own.window_id
                    || c.quorum_ids != own.quorum_ids
                    || c.policy_digest != own.policy_digest
                    || c.intent_digest != own.intent_digest
                    || (c.party_id == own.party_id && c != own)
                {
                    return Err(PolicyViolation::IntentBindingMismatch);
                }
                if c.party_id != own.party_id {
                    guard.incoming_key(c.party_id, c.slot)?;
                    peer_slots.push((c.party_id, c.slot));
                }
            }
            let msg = PartyPolicyDeltaOpenMsg {
                party_id: own.party_id,
                salt_i: self.context.salt,
                delta_i: self.context.delta,
            };
            self.context.peer_slots = peer_slots;
            guard.active_phase = Some((own.slot, 2));
            Ok((
                PartyPolicyRound2State {
                    context: self.context,
                    commits,
                },
                msg,
            ))
        })();
        policy_phase_result(guard, own_slot, &[], result)
    }
}

impl PartyPolicyRound2State {
    pub fn round3_commit_sigma(
        mut self,
        guard: &mut PolicySignerGuardShare,
        openings: &[PartyPolicyDeltaOpenMsg],
    ) -> Result<(PartyPolicyRound3State, PartyPolicySigmaCommitMsg), PolicyViolation> {
        guard.check_phase(&self.context, 2)?;
        let own_slot = self.context.own.slot;
        let result = (|| {
            let mut opens = openings.to_vec();
            opens.sort_by_key(|o| o.party_id);
            let (msg, sigma, salt) = guard.committed_sigma(
                &self.context.own,
                &self.context.folded,
                &self.commits,
                &opens,
            )?;
            guard.active_phase = Some((own_slot, 3));
            self.context.sigma = *sigma;
            self.context.sigma_salt = *salt;
            Ok((
                PartyPolicyRound3State {
                    context: self.context,
                    own_sigma: msg.clone(),
                },
                msg,
            ))
        })();
        policy_phase_result(guard, own_slot, &[], result)
    }
}

impl PartyPolicyRound3State {
    pub fn round4_open_sigma(
        self,
        guard: &mut PolicySignerGuardShare,
        commitments: &[PartyPolicySigmaCommitMsg],
    ) -> Result<(PartyPolicyFinalizeState, PartyPolicySigmaOpenMsg), PolicyViolation> {
        guard.check_phase(&self.context, 3)?;
        let own_slot = self.context.own.slot;
        let peer_slots = self.context.peer_slots.clone();
        let result = (|| {
            let mut commits = commitments.to_vec();
            commits.sort_by_key(|c| c.party_id);
            if commits.len() != self.context.own.quorum_ids.len() {
                return Err(PolicyViolation::IntentBindingMismatch);
            }
            for (c, id) in commits.iter().zip(&self.context.own.quorum_ids) {
                if c.party_id != *id
                    || c.transcript_digest != self.own_sigma.transcript_digest
                    || (c.party_id == self.own_sigma.party_id && c != &self.own_sigma)
                {
                    return Err(PolicyViolation::IntentBindingMismatch);
                }
            }
            let msg = PartyPolicySigmaOpenMsg {
                party_id: self.own_sigma.party_id,
                sigma_salt_i: self.context.sigma_salt,
                sigma_i: self.context.sigma,
            };
            guard.active_phase = Some((self.context.own.slot, 4));
            Ok((
                PartyPolicyFinalizeState {
                    context: self.context,
                    commits,
                },
                msg,
            ))
        })();
        policy_phase_result(guard, own_slot, &peer_slots, result)
    }
}

impl PartyPolicyFinalizeState {
    pub fn finalize(
        self,
        guard: &mut PolicySignerGuardShare,
        openings: &[PartyPolicySigmaOpenMsg],
    ) -> Result<AuthorizedSignReleaseToken, PolicyViolation> {
        guard.check_phase(&self.context, 4)?;
        let own_slot = self.context.own.slot;
        let peer_slots = self.context.peer_slots.clone();
        let result = (|| {
            let mut opens = openings.to_vec();
            opens.sort_by_key(|o| o.party_id);
            let permit = release_committed_sigmas(
                &self.context.own.session_id,
                own_slot as u64,
                &self.commits,
                &opens,
            )?;
            let projected_spend = guard.check_window_nonce_and_projected_spend(
                self.context.velocity_window_cap,
                &self.context.intent,
                &self.context.own.session_id,
                self.context.cumulative_epoch_spent,
            )?;
            guard.record_approved_intent(
                self.context.velocity_window_cap,
                projected_spend,
                self.context.intent.nonce,
                self.context.own.session_id,
            )?;
            guard.abort_session_slot(own_slot, &peer_slots);
            AuthorizedSignReleaseToken::mint(
                permit,
                self.context.own.session_id,
                self.context.own.policy_digest,
                self.context.own.intent_digest,
                self.context.intent.clone(),
            )
        })();
        policy_phase_result(guard, own_slot, &peer_slots, result)
    }
}

impl core::fmt::Display for PolicyViolation {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl core::error::Error for PolicyViolation {}

/// What a signing request binds an intent to: the key, the payload and context, the session,
/// the policy revision, the approving quorum, and the enrolled guard authority.
#[derive(Clone, Copy, Debug)]
pub struct SigningPayloadBinding<'b> {
    pub key_id: [u8; 32],
    pub payload: &'b [u8],
    pub ctx: &'b [u8],
    pub session_id: [u8; 32],
    pub policy_revision: u64,
    pub quorum: &'b [u16],
    pub authority_pk: [u8; 32],
}

/// Builds a canonical signed intent and returns the exact bytes to sign.
pub struct TransactionIntentBuilder(TransactionIntent);
impl TransactionIntentBuilder {
    pub fn rolling_window(mut self, spent: u128, accumulator: [u8; 32]) -> Self {
        self.0.rolling_window_spent = spent;
        self.0.rolling_window_accumulator = accumulator;
        self
    }
    pub fn window_id(mut self, window_id: u64) -> Self {
        self.0.window_id = window_id;
        self
    }
    pub fn nonce(mut self, nonce: [u8; 32]) -> Self {
        self.0.nonce = nonce;
        self
    }
    pub fn initiator_macs(mut self, macs: Vec<InitiatorPeerMac>) -> Self {
        self.0.initiator_macs = macs;
        self
    }
    pub fn timestamp_secs(mut self, timestamp: u64) -> Self {
        self.0.timestamp_secs = timestamp;
        self
    }
    pub fn initiator_and_approvers(mut self, initiator: u16, approvers: &[u16]) -> Self {
        self.0.initiator_party = initiator;
        self.0.approver_parties = approvers.to_vec();
        self
    }
    /// Bind the signing request, evaluate `policy` on the completed intent, and return the
    /// intent together with the exact bytes its approvers authorize for signing.
    pub fn bind_signing_payload(
        mut self,
        binding: &SigningPayloadBinding<'_>,
        policy: &TransactionPolicy,
    ) -> Result<(TransactionIntent, Vec<u8>), PolicyViolation> {
        let SigningPayloadBinding {
            key_id,
            payload,
            ctx,
            session_id,
            policy_revision,
            quorum,
            authority_pk,
        } = *binding;
        self.0.signing_key_id = key_id;
        self.0.payload_digest = cshake256_framed_32(b"QSAG.POLICY.PAYLOAD.V2", &[payload]);
        self.0.signing_context_digest = cshake256_framed_32(b"QSAG.POLICY.CTX.V1", &[ctx]);
        self.0.session_id = session_id;
        self.0.policy_revision = policy_revision;
        self.0.guard_authority_pk = authority_pk;
        self.0.quorum_ids = quorum.to_vec();
        self.0.quorum_ids.sort_unstable();
        self.0.quorum_ids.dedup();
        self.0.approver_parties.sort_unstable();
        self.0.approver_parties.dedup();
        if self.0.nonce == [0; 32] {
            self.0.nonce = cshake256_framed_32(
                b"QSAG.POLICY.AUTO_NONCE.V1",
                &[
                    &session_id,
                    &self.0.payload_digest,
                    &key_id,
                    &self.0.window_id.to_be_bytes(),
                ],
            );
        }
        policy.evaluate(&self.0)?;
        let bytes = self
            .0
            .to_canonical_signing_bytes(&policy.canonical_digest());
        self.0.message_digest = cshake256_framed_32(b"QSAG.POLICY.MSG.V1", &[&bytes]);
        Ok((self.0, bytes))
    }
}
impl AuthorizedSignReleaseToken {
    pub fn matches_signing_for_policy(
        &self,
        key_id: &[u8; 32],
        msg: &[u8],
        ctx: &[u8],
        quorum: &[u16],
        expected_policy: &[u8; 32],
        expected_authority: &[u8; 32],
    ) -> bool {
        ct_eq_bytes(expected_policy, &self.policy_digest)
            && ct_eq_bytes(expected_authority, &self.intent.guard_authority_pk)
            && self.matches_signing(key_id, msg, ctx, quorum)
    }
}

/// Capability credential (`SpongeMacaroon` + 3P discharges or ephemeral `Compact1122` `PqBiscuit`)
/// verified by [`PolicyEngine`] against trusted [`TransactionIntent`] facts *before* latching any
/// BDOZ preprocessing slot.
pub enum CapabilityGate<'a> {
    Macaroon {
        verifier: &'a MacaroonVerifier,
        token: &'a SpongeMacaroon,
        discharges: &'a [Discharge<'a>],
    },
    MacaroonRootKey {
        root_key: &'a [u8; 32],
        token: &'a SpongeMacaroon,
        discharges: &'a [Discharge<'a>],
    },
    Biscuit {
        authority_pk: &'a PqBiscuitAuthorityPublicKey,
        dp: &'a qsag_fts::FrontierDpTable,
        token: &'a PqBiscuit,
    },
}

impl CapabilityRequest {
    /// Derive trusted [`CapabilityRequest`] facts directly from `(policy, intent, now, actions)`:
    /// - `audience = policy.canonical_digest()`
    /// - `resource = intent.recipient.commitment_256`
    /// - `amount = intent.amount_units`
    /// - `now = current_timestamp`
    pub fn from_policy_intent(
        policy: &TransactionPolicy,
        intent: &TransactionIntent,
        actions: u64,
        current_timestamp: u64,
    ) -> Self {
        Self {
            audience: policy.canonical_digest(),
            resource: intent.recipient.commitment_256,
            actions,
            amount: intent.amount_units,
            now: current_timestamp,
        }
    }
}

/// Unified custody policy engine combining [`TransactionPolicy`], optional attenuated capability
/// verification ([`SpongeMacaroon`] / [`PqBiscuit`]), and the 4-round Eurocrypt-2011 BDOZ barrier.
pub struct PolicyEngine<'a> {
    pub policy: &'a TransactionPolicy,
    pub required_actions: u64,
}

impl<'a> PolicyEngine<'a> {
    pub const fn new(policy: &'a TransactionPolicy, required_actions: u64) -> Self {
        Self {
            policy,
            required_actions,
        }
    }

    /// Verify `capability` against the trusted `(policy, intent, current_timestamp)` facts.
    pub fn verify_capability(
        &self,
        intent: &TransactionIntent,
        current_timestamp: u64,
        capability: &CapabilityGate<'_>,
    ) -> Result<(), PolicyViolation> {
        let req = CapabilityRequest::from_policy_intent(
            self.policy,
            intent,
            self.required_actions,
            current_timestamp,
        );
        let res = match capability {
            CapabilityGate::Macaroon {
                verifier,
                token,
                discharges,
            } => verifier.verify(token, &req, discharges),
            CapabilityGate::MacaroonRootKey {
                root_key,
                token,
                discharges,
            } => token.verify(root_key, &req, discharges),
            CapabilityGate::Biscuit {
                authority_pk,
                dp,
                token,
            } => token.verify(authority_pk, dp, &req),
        };
        res.map_err(PolicyViolation::CapabilityDenied)
    }

    /// Verify `capability` (if required/present) and then evaluate `policy` across `quorum_guards`
    /// inside the committed 2-lane BDOZ GF($2^{128}$) MAC barrier. Capability refusals occur
    /// strictly *before* latching any BDOZ preprocessing slot.
    pub fn authorize_committed_barrier<B: AcceleratorBackend>(
        &self,
        intent: &TransactionIntent,
        session_id: [u8; 32],
        current_timestamp: u64,
        capability: Option<&CapabilityGate<'_>>,
        quorum_guards: &mut [PolicySignerGuardShare],
        accel: &B,
    ) -> Result<AuthorizedSignReleaseToken, PolicyViolation> {
        if let Some(gate) = capability {
            self.verify_capability(intent, current_timestamp, gate)?;
        }
        evaluate_policy_committed_barrier(
            self.policy,
            intent,
            session_id,
            current_timestamp,
            quorum_guards,
            accel,
        )
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn shared_verified_guard_survives_rotation_and_checkpoint() {
        let (policy, _) = phase_fixture(&[1, 2]);
        let mut ledger = SharedWindowSpendLedger::new(&policy, 0)
            .with_window_authority([42; 32], [43; 32])
            .unwrap();
        ledger.record_approved_intent(7, [1; 32], [2; 32]).unwrap();
        ledger.record_approved_intent(11, [3; 32], [4; 32]).unwrap();
        assert_eq!(ledger.verified_velocity.as_ref().unwrap().last_nonce(), 2);
        let auth = WindowAdvanceAuthorization::new(&[43; 32], &[42; 32], 0, 1);
        ledger.advance_velocity_window(&auth).unwrap();
        let guard = ledger.verified_velocity.as_ref().unwrap();
        assert_eq!(guard.window_id(), 1);
        assert_eq!(guard.spent_units(), 0);
        assert_eq!(guard.last_nonce(), 2);
        ledger.record_approved_intent(5, [5; 32], [6; 32]).unwrap();
        assert_eq!(ledger.verified_velocity.as_ref().unwrap().last_nonce(), 4);
        let bytes = ledger.export_durable_checkpoint(&[7; 32]);
        let mut restored = SharedWindowSpendLedger::new(&policy, 0)
            .with_window_authority([42; 32], [43; 32])
            .unwrap();
        restored
            .restore_from_durable_checkpoint(&bytes, &[7; 32], 4)
            .unwrap();
        restored
            .record_approved_intent(9, [8; 32], [9; 32])
            .unwrap();
        let guard = restored.verified_velocity.as_ref().unwrap();
        assert_eq!(guard.spent_units(), 9);
        assert_eq!(guard.last_nonce(), 5);
        assert!(!restored.is_nonce_burned(&[1; 32]));
        assert!(!restored.is_session_burned(&[2; 32]));
    }

    pub(super) fn raw_test_guards(entropy: [u8; 32], ids: &[u16]) -> Vec<PolicySignerGuardShare> {
        let mut guards: Vec<_> = super::trusted_dealer_setup_for_testing(entropy, ids)
            .into_iter()
            .map(|g| g.with_window_authority([42; 32], [43; 32]).unwrap())
            .collect();
        for guard in &mut guards {
            guard.set_require_authenticated_initiator(false);
        }
        guards
    }
    #[test]
    fn window_authority_is_required_and_bound_to_checkpoint() {
        let mut bare = super::trusted_dealer_setup_for_testing([9; 32], &[1, 2]).remove(0);
        let auth = WindowAdvanceAuthorization::new(&[43; 32], &[42; 32], 0, 1);
        assert!(bare.advance_velocity_window(&auth).is_err());
        let guard = bare.with_window_authority([42; 32], [43; 32]).unwrap();
        let snapshot = guard.export_durable_checkpoint(&[7; 32], 1);
        let mut other = super::trusted_dealer_setup_for_testing([9; 32], &[1, 2])
            .remove(0)
            .with_window_authority([41; 32], [43; 32])
            .unwrap();
        assert!(
            other
                .restore_from_durable_checkpoint(&snapshot, &[7; 32], 1)
                .is_err()
        );
        assert!(guard.with_window_authority([41; 32], [43; 32]).is_err());
    }

    #[test]
    fn window_authorization_rejects_forgery_replay_and_wrong_policy() {
        let mut guards = raw_test_guards([9; 32], &[1, 2]);
        let guard = &mut guards[0];
        guard.accumulated_window_spend = 99;
        for auth in [
            WindowAdvanceAuthorization::new(&[44; 32], &[42; 32], 0, 1),
            WindowAdvanceAuthorization::new(&[43; 32], &[41; 32], 0, 1),
            WindowAdvanceAuthorization::new(&[43; 32], &[42; 32], 1, 2),
            WindowAdvanceAuthorization::new(&[43; 32], &[42; 32], 0, 0),
        ] {
            assert!(guard.advance_velocity_window(&auth).is_err());
            assert_eq!(guard.current_window_id(), 0);
            assert_eq!(guard.accumulated_window_spend(), 99);
        }
        let valid = WindowAdvanceAuthorization::new(&[43; 32], &[42; 32], 0, 1);
        guard.advance_velocity_window(&valid).unwrap();
        assert_eq!(guard.accumulated_window_spend(), 0);
        assert!(guard.advance_velocity_window(&valid).is_err());
    }

    #[test]
    fn signer_verified_guard_survives_approvals_rotation_and_checkpoint() {
        use PolicyViolation::VelocityCapOverflowOrExceeded as OverCap;
        let mut guards = raw_test_guards([9; 32], &[1, 2]);
        let guard = &mut guards[0];
        assert!(guard.verified_velocity.is_none());
        guard
            .record_approved_intent(50, 7, [1; 32], [2; 32])
            .unwrap();
        guard
            .record_approved_intent(50, 30, [3; 32], [4; 32])
            .unwrap();
        let v = guard.verified_velocity.as_ref().unwrap();
        assert_eq!(
            (v.cap_units(), v.spent_units(), v.last_nonce()),
            (50, 30, 2)
        );
        // Over the pinned cap: refused, nothing recorded or burned.
        assert_eq!(
            guard.record_approved_intent(50, 51, [5; 32], [6; 32]),
            Err(OverCap)
        );
        assert_eq!(guard.accumulated_window_spend(), 30);
        assert!(!guard.is_nonce_burned(&[5; 32]));
        // A cap below what is already spent cannot be pinned; the old guard stays.
        assert_eq!(
            guard.record_approved_intent(20, 30, [5; 32], [6; 32]),
            Err(OverCap)
        );
        assert_eq!(guard.verified_velocity.as_ref().unwrap().cap_units(), 50);
        // Rotation keeps the guard and its request nonce and resets the spend.
        guard
            .advance_velocity_window(&WindowAdvanceAuthorization::new(&[43; 32], &[42; 32], 0, 1))
            .unwrap();
        let v = guard.verified_velocity.as_ref().unwrap();
        assert_eq!((v.window_id(), v.spent_units(), v.last_nonce()), (1, 0, 2));
        guard
            .record_approved_intent(50, 9, [7; 32], [8; 32])
            .unwrap();
        // A freshly provisioned guard recovers the verified state from the checkpoint.
        let bytes = guard.export_durable_checkpoint(&[7; 32], 5);
        let mut fresh = raw_test_guards([9; 32], &[1, 2]);
        fresh[0]
            .restore_from_durable_checkpoint(&bytes, &[7; 32], 5)
            .unwrap();
        let v = fresh[0].verified_velocity.as_ref().unwrap();
        assert_eq!(
            (
                v.window_id(),
                v.cap_units(),
                v.spent_units(),
                v.last_nonce()
            ),
            (1, 50, 9, 3)
        );
        assert_eq!(
            fresh[0].record_approved_intent(50, 51, [9; 32], [10; 32]),
            Err(OverCap)
        );
        fresh[0]
            .record_approved_intent(50, 50, [9; 32], [10; 32])
            .unwrap();
        assert_eq!(fresh[0].verified_velocity.as_ref().unwrap().last_nonce(), 4);
    }

    #[test]
    fn provisioned_guards_require_initiator_authentication_and_cannot_be_downgraded() {
        let accel = CpuReferenceBackend::new();
        let (policy, intent) = phase_fixture(&[1, 4]);
        let provision = || -> Vec<PolicySignerGuardShare> {
            super::trusted_dealer_setup_for_testing([8; 32], &[1, 4])
                .into_iter()
                .map(|g| g.with_window_authority([42; 32], [43; 32]).unwrap())
                .collect()
        };
        let mut guards = provision();
        assert!(guards.iter().all(|g| g.require_authenticated_initiator));

        // The intent carries no initiator MAC. The entry points that do not force
        // authentication refuse it all the same.
        assert_eq!(
            evaluate_policy_committed_barrier(
                &policy,
                &intent,
                intent.session_id,
                intent.timestamp_secs,
                &mut guards,
                &accel,
            )
            .unwrap_err(),
            PolicyViolation::UnauthenticatedInitiator
        );
        assert_eq!(
            guards[0]
                .round1_commit_intent(
                    &policy,
                    &intent,
                    intent.session_id,
                    intent.timestamp_secs,
                    intent.rolling_window_spent,
                )
                .err(),
            Some(PolicyViolation::UnauthenticatedInitiator)
        );

        // A checkpoint of the same guard with the requirement waived is a rollback; one
        // with the requirement set restores.
        let waived = raw_test_guards([8; 32], &[1, 4]);
        assert!(!waived[0].require_authenticated_initiator);
        let downgrade = waived[0].export_durable_checkpoint(&[7; 32], 1);
        assert!(matches!(
            guards[0].restore_from_durable_checkpoint(&downgrade, &[7; 32], 1),
            Err(PolicyGuardError::Rollback)
        ));
        assert!(guards[0].require_authenticated_initiator);
        let twin = provision();
        let same = twin[0].export_durable_checkpoint(&[7; 32], 1);
        guards[0]
            .restore_from_durable_checkpoint(&same, &[7; 32], 1)
            .unwrap();
        assert!(guards[0].require_authenticated_initiator);
    }

    #[test]
    fn quorum_tier_order_is_validated_before_any_tier_is_selected() {
        let (mut policy, intent) = phase_fixture(&[1, 4]);
        let tier = |max_amount_units, min_approvers, require_hardware_guardian| QuorumTierRule {
            max_amount_units,
            min_approvers,
            require_hardware_guardian,
        };
        // The intent (amount 10, approvers {1, 4}, guardian 4) satisfies the first tier of
        // every list below, so each refusal comes from the order check alone.
        let mut verdict = |tiers: Vec<QuorumTierRule>| {
            policy.quorum_tiers = tiers;
            (policy.validate_quorum_tiers(), policy.evaluate(&intent))
        };
        let refused = (
            Err(PolicyViolation::InvalidQuorumTierOrder),
            Err(PolicyViolation::InvalidQuorumTierOrder),
        );

        assert_eq!(
            verdict(vec![
                tier(50, 2, false),
                tier(100, 2, false),
                tier(1_000, 3, true)
            ]),
            (Ok(()), Ok(()))
        );
        // A later tier whose bound an earlier tier already covers is unreachable.
        assert_eq!(
            verdict(vec![tier(100, 2, false), tier(100, 3, true)]),
            refused
        );
        assert_eq!(
            verdict(vec![tier(100, 2, false), tier(50, 3, true)]),
            refused
        );
        assert_eq!(
            verdict(vec![
                tier(50, 2, false),
                tier(1_000, 2, false),
                tier(100, 3, true)
            ]),
            refused
        );
        // A larger amount selecting a weaker quorum than a smaller one.
        assert_eq!(
            verdict(vec![tier(50, 2, false), tier(100, 1, false)]),
            refused
        );
        assert_eq!(
            verdict(vec![tier(50, 2, true), tier(100, 2, false)]),
            refused
        );
        assert_eq!(
            verdict(vec![
                tier(50, 2, true),
                tier(100, 3, true),
                tier(1_000, 3, false)
            ]),
            refused
        );
        // No tier: in order, and no amount is covered.
        assert_eq!(
            verdict(Vec::new()),
            (Ok(()), Err(PolicyViolation::NoMatchingQuorumTier))
        );
    }

    #[test]
    fn in_process_barrier_and_party_phases_derive_identical_rounds() {
        let (policy, intent) = phase_fixture(&[1, 4]);
        // The dealer is deterministic: both guard sets hold the same secrets.
        let mut phase_guards = raw_test_guards([0x5A; 32], &[1, 4]);
        let batch_guards = raw_test_guards([0x5A; 32], &[1, 4]);

        let (states, delta_commits) = start_phases(&mut phase_guards, &policy, &intent);
        let (states, delta_opens): (Vec<_>, Vec<_>) = states
            .into_iter()
            .zip(&mut phase_guards)
            .map(|(s, g)| s.round2_open_delta(g, &delta_commits).unwrap())
            .unzip();
        let (_states, sigma_commits): (Vec<_>, Vec<_>) = states
            .into_iter()
            .zip(&mut phase_guards)
            .map(|(s, g)| s.round3_commit_sigma(g, &delta_opens).unwrap())
            .unzip();

        // The same session on the in-process path: same slots, commitments not yet set.
        let sessions: Vec<PartyPolicyDeltaCommitMsg> = delta_commits
            .iter()
            .map(|c| PartyPolicyDeltaCommitMsg {
                commitment: [0; 32],
                ..c.clone()
            })
            .collect();
        for g in &batch_guards {
            g.next_slot.set(1);
        }
        let (_permit, batch_sigma_commits) = barrier_rounds_in_process(
            &sessions,
            &batch_guards,
            &[intent.clone(), intent.clone()],
            None,
            &CpuReferenceBackend::new(),
        )
        .unwrap();
        // A sigma commitment covers the transcript digest (every delta commitment, salt
        // and opening), the sigma share and its salt.
        assert_eq!(batch_sigma_commits, sigma_commits);
    }
    #[test]
    fn replay_capacity_exceeds_legacy_limit_and_is_durable() {
        let mut guards = raw_test_guards([9; 32], &[1, 2]);
        let guard = &mut guards[0];
        guard.set_replay_capacity(600).unwrap();
        for i in 0u64..600 {
            let mut nonce = [0; 32];
            nonce[..8].copy_from_slice(&i.to_be_bytes());
            guard
                .record_approved_intent(u128::MAX, i as u128, nonce, nonce)
                .unwrap();
        }
        let snapshot = guard.export_durable_checkpoint(&[7; 32], 600);
        let mut restored = raw_test_guards([9; 32], &[1, 2]);
        restored[0]
            .restore_from_durable_checkpoint(&snapshot, &[7; 32], 600)
            .unwrap();
        assert_eq!(restored[0].replay_capacity, 600);
        assert_eq!(
            restored[0].export_durable_checkpoint(&[7; 32], 600),
            snapshot
        );
        assert_eq!(
            restored[0].record_approved_intent(u128::MAX, 601, [255; 32], [255; 32]),
            Err(PolicyViolation::ReplayWindowExhausted)
        );
        assert!(restored[0].set_replay_capacity(599).is_err());
        restored[0].set_replay_capacity(601).unwrap();
        restored[0]
            .record_approved_intent(u128::MAX, 601, [255; 32], [255; 32])
            .unwrap();
    }

    #[test]
    fn bounded_replay_window_retains_random_nonces_until_authenticated_rotation() {
        let mut guards = raw_test_guards([9; 32], &[1, 2]);
        let guard = &mut guards[0];
        guard.set_replay_capacity(256).unwrap();
        let nonces: Vec<_> = (0u32..256)
            .map(|i| cshake256_framed_32(b"nonce test", &[&i.to_be_bytes()]))
            .collect();
        for (i, nonce) in nonces.iter().enumerate() {
            assert!(!guard.is_nonce_burned(nonce));
            guard
                .record_approved_intent(u128::MAX, i as u128, *nonce, *nonce)
                .unwrap();
        }
        for nonce in &nonces {
            assert!(guard.is_nonce_burned(nonce));
        }
        assert_eq!(
            guard.record_approved_intent(u128::MAX, 256, [0; 32], [0; 32]),
            Err(PolicyViolation::ReplayWindowExhausted)
        );
        let checkpoint = guard.export_durable_checkpoint(&[7; 32], 256);
        guard
            .restore_from_durable_checkpoint(&checkpoint, &[7; 32], 256)
            .unwrap();
        guard
            .advance_velocity_window(&WindowAdvanceAuthorization::new(&[43; 32], &[42; 32], 0, 1))
            .unwrap();
        assert!(!guard.is_nonce_burned(&[0; 32]));
        guard
            .record_approved_intent(u128::MAX, 1, [0; 32], [0; 32])
            .unwrap();
    }

    use alloc::format;
    use alloc::vec;
    use qsag_accel::CpuReferenceBackend;
    use qsag_addr::KeyIdentityKind;

    use super::*;

    pub(super) fn phase_fixture(ids: &[u16]) -> (TransactionPolicy, TransactionIntent) {
        let recipient = QsagAddress::from_pubkey_cshake256(
            "qsp",
            WitnessSuiteTag::MlDsa65,
            KeyIdentityKind::SingleOrThreshold,
            b"phase-recipient",
        )
        .unwrap();
        let policy = TransactionPolicy {
            chain_id: 1,
            pinned_suite: WitnessSuiteTag::MlDsa65,
            recipient_allowlist: vec![recipient.commitment_256],
            max_single_tx_amount: 100,
            velocity_window_cap: 200,
            valid_not_before_secs: 1,
            valid_not_after_secs: 100,
            forbid_initiator_self_approval: true,
            hardware_guardian_party: Some(*ids.last().unwrap()),
            quorum_tiers: vec![QuorumTierRule {
                max_amount_units: 100,
                min_approvers: 2,
                require_hardware_guardian: true,
            }],
        };
        let intent = TransactionIntent {
            chain_id: 1,
            suite: WitnessSuiteTag::MlDsa65,
            recipient,
            amount_units: 10,
            rolling_window_spent: 20,
            window_id: 0,
            nonce: [7; 32],
            timestamp_secs: 50,
            initiator_party: 0,
            initiator_macs: Vec::new(),
            approver_parties: ids.to_vec(),
            payload_digest: [1; 32],
            guard_authority_pk: [0; 32],
            rolling_window_accumulator: [0; 32],
            signing_key_id: [2; 32],
            policy_revision: 1,
            message_digest: cshake256_framed_32(b"QSAG.POLICY.MSG.V1", &[b"message"]),
            signing_context_digest: cshake256_framed_32(b"QSAG.POLICY.CTX.V1", &[b"context"]),
            session_id: [3; 32],
            quorum_ids: ids.to_vec(),
        };
        (policy, intent)
    }

    fn start_phases(
        guards: &mut [PolicySignerGuardShare],
        policy: &TransactionPolicy,
        intent: &TransactionIntent,
    ) -> (Vec<PartyPolicyRound1State>, Vec<PartyPolicyDeltaCommitMsg>) {
        guards
            .iter_mut()
            .map(|g| {
                g.round1_commit_intent(
                    policy,
                    intent,
                    intent.session_id,
                    intent.timestamp_secs,
                    intent.rolling_window_spent,
                )
                .unwrap()
            })
            .unzip()
    }

    fn delta_phases(
        guards: &mut [PolicySignerGuardShare],
        policy: &TransactionPolicy,
        intent: &TransactionIntent,
    ) -> (Vec<PartyPolicyRound2State>, Vec<PartyPolicyDeltaOpenMsg>) {
        let (states, commits) = start_phases(guards, policy, intent);
        states
            .into_iter()
            .zip(guards)
            .map(|(s, g)| s.round2_open_delta_and_commit_sigma(g, &commits).unwrap())
            .unzip()
    }

    fn sigma_phases(
        guards: &mut [PolicySignerGuardShare],
        policy: &TransactionPolicy,
        intent: &TransactionIntent,
    ) -> (Vec<PartyPolicyRound3State>, Vec<PartyPolicySigmaCommitMsg>) {
        let (states, opens) = delta_phases(guards, policy, intent);
        states
            .into_iter()
            .zip(guards)
            .map(|(s, g)| s.round3_commit_sigma(g, &opens).unwrap())
            .unzip()
    }

    fn assert_erased(g: &PolicySignerGuardShare) {
        assert!(g.poisoned);
        assert_eq!(g.bdoz_alpha_share, [0; 2]);
        assert_eq!(g.local_salt_seed, [0; 32]);
        assert!(g.preproc_r.iter().all(|r| *r == [0; 2]));
        assert!(g.pairwise_zero_seeds.iter().all(|(_, s)| *s == [0; 32]));
        assert!(
            g.preproc_outgoing_macs
                .iter()
                .chain(&g.preproc_incoming_keys)
                .all(|(_, values)| values.iter().all(|v| *v == [0; 2]))
        );
    }

    fn assert_slot_aborted_not_bricked(g: &PolicySignerGuardShare, slot: usize) {
        assert!(!g.poisoned);
        assert_eq!(g.active_phase, None);
        assert_ne!(g.bdoz_alpha_share, [0; 2]);
        assert_ne!(g.local_salt_seed, [0; 32]);
        assert_eq!(g.preproc_r[slot], [0; 2]);
        assert!(
            g.preproc_outgoing_macs
                .iter()
                .all(|(_, values)| values[slot] == [0; 2])
        );
        if slot + 1 < BDOZ_PREPROC_SLOTS {
            assert_ne!(g.preproc_r[slot + 1], [0; 2]);
        }
    }

    fn run_phases(
        guards: &mut [PolicySignerGuardShare],
        policy: &TransactionPolicy,
        intent: &TransactionIntent,
    ) {
        let (states, mut commits) = sigma_phases(guards, policy, intent);
        // Arrival ordering has no effect on canonical transcript ordering.
        commits.reverse();
        let (states, mut opens): (Vec<_>, Vec<_>) = states
            .into_iter()
            .zip(guards.iter_mut())
            .map(|(s, g)| s.round4_open_sigma(g, &commits).unwrap())
            .unzip();
        opens.reverse();
        for (s, g) in states.into_iter().zip(guards) {
            let token = s.finalize(g, &opens).unwrap();
            assert_eq!(token.intent_digest(), &intent.canonical_digest());
            assert!(token.matches_signing(
                &intent.signing_key_id,
                &intent.to_canonical_signing_bytes(&policy.canonical_digest()),
                b"context",
                &intent.quorum_ids
            ));
            assert_eq!(g.active_phase, None);
        }
    }

    #[test]
    fn party_phases_release_once_and_advance_slots() {
        let (policy, intent) = phase_fixture(&[1, 2, 4]);
        let mut guards = raw_test_guards([11; 32], &[1, 2, 4]);
        run_phases(&mut guards, &policy, &intent);
        assert!(guards.iter().all(|g| g.accumulated_window_spend() == 30));
        let mut next = intent.clone();
        next.session_id = [4; 32];
        next.nonce = [8; 32];
        next.rolling_window_spent = 30;
        run_phases(&mut guards, &policy, &next);
        assert!(guards.iter().all(|g| g.next_slot.get() == 2));
        assert!(guards.iter().all(|g| g.accumulated_window_spend() == 40));
    }

    #[test]
    fn party_phases_reject_clock_spend_and_guardian_spoofing() {
        let (policy, intent) = phase_fixture(&[1, 4]);
        let mut guards = raw_test_guards([12; 32], &[1, 4]);
        assert!(matches!(
            guards[0].round1_commit_intent(&policy, &intent, intent.session_id, 51, 20),
            Err(PolicyViolation::TimestampOutsideWindow)
        ));
        assert!(matches!(
            guards[0].round1_commit_intent(&policy, &intent, intent.session_id, 50, 19),
            Err(PolicyViolation::VelocityCapOverflowOrExceeded)
        ));
        assert_eq!(guards[0].next_slot.get(), 0);
        guards[0].party_id = 4;
        assert!(
            guards[0]
                .round1_commit_intent(&policy, &intent, intent.session_id, 50, 20)
                .is_err()
        );
        assert_erased(&guards[0]);
        let mut guards = raw_test_guards([12; 32], &[1, 4]);
        let (mut states, mut commits) = start_phases(&mut guards, &policy, &intent);
        let honest_commits = commits.clone();
        commits[1] = commits[0].clone();
        commits[1].party_id = 4;
        let (state, _) = states
            .remove(0)
            .round2_open_delta(&mut guards[0], &commits)
            .unwrap();
        let (_, guardian_open) = states
            .remove(0)
            .round2_open_delta(&mut guards[1], &honest_commits)
            .unwrap();
        let own_open = PartyPolicyDeltaOpenMsg {
            party_id: 1,
            salt_i: state.context.salt,
            delta_i: state.context.delta,
        };
        assert!(
            state
                .round3_commit_sigma(&mut guards[0], &[own_open, guardian_open])
                .is_err()
        );
        assert_slot_aborted_not_bricked(&guards[0], 0);
    }

    #[test]
    fn party_phases_reject_even_quorum_conflicting_intents() {
        let (policy, intent) = phase_fixture(&[1, 2, 3, 4]);
        let mut guards = raw_test_guards([13; 32], &[1, 2, 3, 4]);
        let mut states = Vec::new();
        let mut commits = Vec::new();
        for (i, g) in guards.iter_mut().enumerate() {
            let mut local = intent.clone();
            if i % 2 == 1 {
                local.amount_units += 1;
            }
            let (s, c) = g
                .round1_commit_intent(&policy, &local, local.session_id, 50, 20)
                .unwrap();
            states.push(s);
            commits.push(c);
        }
        for (s, g) in states.into_iter().zip(&mut guards) {
            assert!(s.round2_open_delta(g, &commits).is_err());
            assert_slot_aborted_not_bricked(g, 0);
        }
    }

    #[test]
    fn party_phases_reject_overlap_wrong_guard_and_equivocation() {
        let (policy, intent) = phase_fixture(&[1, 4]);
        let mut guards = raw_test_guards([14; 32], &[1, 4]);
        let (mut states, commits) = start_phases(&mut guards, &policy, &intent);
        assert!(
            states
                .remove(0)
                .round2_open_delta(&mut guards[1], &commits)
                .is_err()
        );
        assert_erased(&guards[1]);
        assert!(
            guards[0]
                .round1_commit_intent(&policy, &intent, intent.session_id, 50, 20)
                .is_err()
        );
        assert_erased(&guards[0]);
        let mut guards = raw_test_guards([14; 32], &[1, 4]);
        let (mut states, mut commits) = start_phases(&mut guards, &policy, &intent);
        commits[0].commitment[0] ^= 1;
        assert!(
            states
                .remove(0)
                .round2_open_delta(&mut guards[0], &commits)
                .is_err()
        );
        assert_slot_aborted_not_bricked(&guards[0], 0);
        let mut guards = raw_test_guards([14; 32], &[1, 4]);
        let (mut states, mut opens) = delta_phases(&mut guards, &policy, &intent);
        opens[1].delta_i[0] ^= 1;
        assert!(
            states
                .remove(0)
                .round3_commit_sigma(&mut guards[0], &opens)
                .is_err()
        );
        assert_slot_aborted_not_bricked(&guards[0], 0);
        let mut guards = raw_test_guards([14; 32], &[1, 4]);
        let (mut states, mut commits) = start_phases(&mut guards, &policy, &intent);
        commits.pop();
        assert!(
            states
                .remove(0)
                .round2_open_delta(&mut guards[0], &commits)
                .is_err()
        );
        assert_slot_aborted_not_bricked(&guards[0], 0);
    }

    #[test]
    fn abandoned_session_is_aborted_in_any_phase_without_bricking_the_guard() {
        let (policy, intent) = phase_fixture(&[1, 2, 4]);
        let mut guards = raw_test_guards([15; 32], &[1, 2, 4]);
        let mut session = 0u8;
        let mut next_intent = |spent: u128| {
            session += 1;
            let mut next = intent.clone();
            next.session_id = [0x40 + session; 32];
            next.nonce = [0x80 + session; 32];
            next.rolling_window_spent = spent;
            next
        };
        // Phase 1: a peer never answers the commitments.
        let attempt = next_intent(20);
        let (states, _) = start_phases(&mut guards, &policy, &attempt);
        for (state, guard) in states.into_iter().zip(&mut guards) {
            state.abort(guard).unwrap();
            assert_slot_aborted_not_bricked(guard, 0);
        }
        // Phase 2: deltas are open; the peer slots that were named are retired with ours.
        let attempt = next_intent(20);
        let (states, _) = delta_phases(&mut guards, &policy, &attempt);
        for (state, guard) in states.into_iter().zip(&mut guards) {
            state.abort(guard).unwrap();
            assert_slot_aborted_not_bricked(guard, 1);
        }
        for guard in &guards {
            for (peer, _) in &guard.pairwise_zero_seeds {
                assert!(!guard.is_peer_slot_consumed(*peer, 0));
                assert!(guard.is_peer_slot_consumed(*peer, 1));
                assert!(guard.incoming_key(*peer, 1).is_err());
            }
        }
        // Phase 3 and phase 4: sigma is committed, then opened.
        let attempt = next_intent(20);
        let (states, commits) = sigma_phases(&mut guards, &policy, &attempt);
        let (finals, _): (Vec<_>, Vec<_>) = states
            .into_iter()
            .zip(guards.iter_mut())
            .map(|(s, g)| s.round4_open_sigma(g, &commits).unwrap())
            .unzip();
        for (state, guard) in finals.into_iter().zip(&mut guards) {
            state.abort(guard).unwrap();
            assert_slot_aborted_not_bricked(guard, 2);
        }
        let attempt = next_intent(20);
        let (states, _) = sigma_phases(&mut guards, &policy, &attempt);
        for (state, guard) in states.into_iter().zip(&mut guards) {
            state.abort(guard).unwrap();
            assert_slot_aborted_not_bricked(guard, 3);
        }
        // Nothing was spent or burned, and the guards complete a later session.
        assert!(guards.iter().all(|g| g.accumulated_window_spend() == 0));
        assert!(guards.iter().all(|g| !g.is_session_burned(&[0x41; 32])));
        run_phases(&mut guards, &policy, &next_intent(20));
        assert!(guards.iter().all(|g| g.next_slot.get() == 5));
        assert!(guards.iter().all(|g| g.accumulated_window_spend() == 30));
        // A state handed to the wrong guard still poisons that guard.
        let attempt = next_intent(30);
        let (mut states, _) = start_phases(&mut guards, &policy, &attempt);
        assert!(states.remove(0).abort(&mut guards[1]).is_err());
        assert_erased(&guards[1]);
    }

    #[test]
    fn slot_capacity_boundaries_fail_closed_and_capacity_is_transcript_bound() {
        for capacity in [1usize, 63, 64, 65, 255, 256, 257] {
            let mut guards = raw_test_guards([0x71; 32], &[1, 2]);
            let guard = &mut guards[0];
            // Bookkeeping only: the preprocessing values themselves are not exercised.
            guard.preproc_r.resize(capacity, [1; 2]);
            for (_, words) in &mut guard.consumed_peer_slots {
                *words = vec![0; capacity.div_ceil(64)];
            }
            for (_, values) in guard
                .preproc_outgoing_macs
                .iter_mut()
                .chain(&mut guard.preproc_incoming_keys)
            {
                values.resize(capacity, [1; 2]);
            }
            let last = capacity - 1;
            assert!(!guard.is_peer_slot_consumed(2, last));
            assert!(guard.incoming_key(2, last).is_ok());
            for beyond in [
                capacity,
                capacity + 1,
                capacity.next_multiple_of(64),
                usize::MAX,
            ] {
                assert!(guard.is_peer_slot_consumed(2, beyond));
                assert_eq!(
                    guard.incoming_key(2, beyond),
                    Err(PolicyViolation::BarrierPreprocExhausted)
                );
                assert_eq!(
                    guard.outgoing_mac(2, beyond),
                    Err(PolicyViolation::BarrierPreprocExhausted)
                );
                // Retiring an out-of-range slot neither panics nor marks a real one.
                guard.retire_peer_slot(2, beyond);
            }
            assert!(
                guard
                    .consumed_peer_slots
                    .iter()
                    .all(|(_, words)| words.iter().all(|w| *w == 0))
            );
            guard.retire_peer_slot(2, last);
            assert!(guard.is_peer_slot_consumed(2, last));
            assert_eq!(
                guard.incoming_key(2, last),
                Err(PolicyViolation::IntentBindingMismatch)
            );
            let marked: u32 = guard.consumed_peer_slots[0]
                .1
                .iter()
                .map(|w| w.count_ones())
                .sum();
            assert_eq!(marked, 1);
            if last > 0 {
                assert!(!guard.is_peer_slot_consumed(2, last - 1));
            }
            // An unknown peer has no usable slot at all.
            assert!(guard.is_peer_slot_consumed(9, 0));
            // The local cursor stops exactly at capacity.
            guard.next_slot.set(capacity);
            let (policy, intent) = phase_fixture(&[1, 2]);
            assert_eq!(
                guard
                    .round1_commit_intent(&policy, &intent, intent.session_id, 50, 20)
                    .err(),
                Some(PolicyViolation::BarrierPreprocExhausted)
            );
            assert!(!guard.is_poisoned());
        }
        for capacity in [0, MAX_POLICY_CAPACITY + 1] {
            assert_eq!(
                PolicyGuardDkgRound1::new_with_capacity(1, &[1, 2], [9; 32], [1; 32], capacity)
                    .err(),
                Some(PolicyViolation::BarrierPreprocExhausted)
            );
        }
        // Two parties that disagree on the pool size cannot complete the ceremony.
        let (small, small_commits) =
            PolicyGuardDkgRound1::new_with_capacity(1, &[1, 2], [9; 32], [1; 32], 64).unwrap();
        let (_, large_commits) =
            PolicyGuardDkgRound1::new_with_capacity(2, &[1, 2], [9; 32], [2; 32], 65).unwrap();
        assert_ne!(small_commits[0].setup_digest, large_commits[0].setup_digest);
        assert_eq!(
            small.round2_open_seeds(&large_commits).err(),
            Some(PolicyViolation::IntentBindingMismatch)
        );
    }

    #[test]
    fn party_phases_reject_stale_openings_and_sigma_commit_equivocation() {
        let (policy, intent) = phase_fixture(&[1, 4]);
        let mut previous = raw_test_guards([19; 32], &[1, 4]);
        let (_, stale_opens) = delta_phases(&mut previous, &policy, &intent);
        let mut next_intent = intent.clone();
        next_intent.session_id = [22; 32];
        next_intent.nonce = [23; 32];
        let mut guards = raw_test_guards([19; 32], &[1, 4]);
        let (mut states, _) = delta_phases(&mut guards, &policy, &next_intent);
        assert!(
            states
                .remove(0)
                .round3_commit_sigma(&mut guards[0], &stale_opens)
                .is_err()
        );
        assert_slot_aborted_not_bricked(&guards[0], 0);
        for mode in 0..3 {
            let mut guards = raw_test_guards([19; 32], &[1, 4]);
            let (mut states, mut commits) = sigma_phases(&mut guards, &policy, &intent);
            match mode {
                0 => {
                    commits.pop();
                }
                1 => {
                    commits[0].commitment[0] ^= 1;
                }
                _ => {
                    commits[1].transcript_digest[0] ^= 1;
                }
            }
            assert!(
                states
                    .remove(0)
                    .round4_open_sigma(&mut guards[0], &commits)
                    .is_err()
            );
            assert_slot_aborted_not_bricked(&guards[0], 0);
        }
        let mut guards = raw_test_guards([19; 32], &[1, 4]);
        let (mut states, commits) = start_phases(&mut guards, &policy, &intent);
        // A corrupted local phase latch must fail closed, even with an otherwise valid transcript.
        guards[0].active_phase = Some((0, 3));
        assert!(
            states
                .remove(0)
                .round2_open_delta(&mut guards[0], &commits)
                .is_err()
        );
        assert_erased(&guards[0]);
    }

    #[test]
    fn party_phases_reject_sigma_opening_and_nonzero_sum() {
        let (policy, intent) = phase_fixture(&[1, 4]);
        for coherent in [false, true] {
            let mut guards = raw_test_guards([15; 32], &[1, 4]);
            let (mut states, mut commits) = sigma_phases(&mut guards, &policy, &intent);
            if coherent {
                states[1].context.sigma[0] ^= 1;
                commits[1].commitment = sigma_commitment(
                    &commits[1],
                    &states[1].context.sigma_salt,
                    &states[1].context.sigma,
                );
                states[1].own_sigma = commits[1].clone();
            }
            let (mut finals, mut opens): (Vec<_>, Vec<_>) = states
                .into_iter()
                .zip(&mut guards)
                .map(|(s, g)| s.round4_open_sigma(g, &commits).unwrap())
                .unzip();
            if !coherent {
                opens[1].sigma_i[0] ^= 1;
            }
            let result = finals.remove(0).finalize(&mut guards[0], &opens);
            if coherent {
                assert!(matches!(result, Err(PolicyViolation::BarrierBdozMacFailed)));
            } else {
                assert!(matches!(
                    result,
                    Err(PolicyViolation::BarrierCommitmentMismatch { .. })
                ));
            }
            assert_slot_aborted_not_bricked(&guards[0], 0);
        }
    }

    // Ideal OT functionality for algebra tests only; production uses a secure OT provider.
    #[derive(Default)]
    struct IdealPolicyOt {
        peers: Vec<(u16, [u128; 2], [u8; 32])>,
        slot_cursors: Vec<(u16, u16, usize)>,
    }
    impl Drop for IdealPolicyOt {
        fn drop(&mut self) {
            for (_, alpha, seed) in &mut self.peers {
                wipe(alpha);
                wipe(seed);
            }
        }
    }
    impl PolicyAuthenticatedOt for IdealPolicyOt {
        fn exchange(
            &mut self,
            local_party: u16,
            peer: u16,
            domain: [u8; 32],
            alternatives: &[[u128; 2]],
            choices: &[bool],
        ) -> Result<Vec<u128>, PolicyViolation> {
            assert!(alternatives.len().is_multiple_of(256));
            assert_eq!(choices.len(), alternatives.len());
            let (_, local_alpha, _) = self
                .peers
                .iter()
                .find(|(id, _, _)| *id == local_party)
                .unwrap();
            let (_, alpha, seed) = self.peers.iter().find(|(id, _, _)| *id == peer).unwrap();
            let cursor = match self
                .slot_cursors
                .iter()
                .position(|(a, b, _)| *a == local_party && *b == peer)
            {
                Some(index) => index,
                None => {
                    self.slot_cursors.push((local_party, peer, 0));
                    self.slot_cursors.len() - 1
                }
            };
            let start = self.slot_cursors[cursor].2;
            self.slot_cursors[cursor].2 += alternatives.len() / 256;
            let mut pads = policy_ot_pad_stream(seed, &domain, peer, local_party, start);
            let mut selected = Vec::new();
            for (i, choice) in choices.iter().enumerate() {
                let slot = start + i / 256;
                let lane = i % 256 / 128;
                let bit = i % 128;
                let local_slot_alpha = derive_peer_slot_alpha(local_alpha, peer, slot);
                let peer_slot_alpha = derive_peer_slot_alpha(alpha, local_party, slot);
                assert_eq!(
                    alternatives[i][0] ^ alternatives[i][1],
                    gf2_128_mul(local_slot_alpha[lane], 1u128 << bit)
                );
                let mut raw = SecretBuffer([0u8; 16]);
                pads.squeeze(&mut raw[..]);
                let pad = u128::from_le_bytes(*raw);
                selected.push(
                    pad ^ if *choice {
                        gf2_128_mul(peer_slot_alpha[lane], 1u128 << bit)
                    } else {
                        0
                    },
                );
            }
            Ok(selected)
        }
    }

    #[test]
    fn distributed_setup_and_all_party_phases() {
        let all_ids = [0, 1, 2, 4];
        let mut first = Vec::new();
        let mut commits = Vec::new();
        let mut ot = IdealPolicyOt::default();
        for id in all_ids {
            let (state, messages) = PolicyGuardDkgRound1::new_with_capacity(
                id,
                &all_ids,
                [20; 32],
                [id as u8; 32],
                300,
            )
            .unwrap();
            ot.peers.push((
                id,
                state.guard.bdoz_alpha_share,
                state.guard.local_salt_seed,
            ));
            first.push(state);
            commits.extend(messages);
        }
        let mut second = Vec::new();
        let mut opens = Vec::new();
        for (state, id) in first.into_iter().zip(all_ids) {
            let incoming: Vec<_> = commits
                .iter()
                .filter(|c| c.recipient == id)
                .cloned()
                .collect();
            let (state, messages) = state.round2_open_seeds(&incoming).unwrap();
            second.push(state);
            opens.extend(messages);
        }
        let mut guards = Vec::new();
        for (state, id) in second.into_iter().zip(all_ids) {
            let incoming: Vec<_> = opens
                .iter()
                .filter(|o| o.recipient == id)
                .cloned()
                .collect();
            guards.push(finalize_distributed_policy_guard(state, &incoming, &mut ot).unwrap());
        }
        for g in &guards {
            for peer in &guards {
                if g.party_id == peer.party_id {
                    continue;
                }
                for slot in 0..300 {
                    let m = g.outgoing_mac(peer.party_id, slot).unwrap();
                    let k = peer.incoming_key(g.party_id, slot).unwrap();
                    let peer_alpha = peer.incoming_slot_alpha(g.party_id, slot);
                    for lane in 0..2 {
                        assert_eq!(
                            m[lane],
                            k[lane] ^ gf2_128_mul(peer_alpha[lane], g.preproc_r[slot][lane])
                        );
                    }
                }
            }
        }
        let (policy, mut intent) = phase_fixture(&[1, 2, 4]);
        // Production DKG guards mandate cryptographic initiator authentication!
        assert!(matches!(
            guards[1].round1_commit_intent(
                &policy,
                &intent,
                intent.session_id,
                intent.timestamp_secs,
                intent.rolling_window_spent,
            ),
            Err(PolicyViolation::UnauthenticatedInitiator)
        ));
        guards[0]
            .authenticate_initiated_intent(&policy, &mut intent)
            .unwrap();
        run_phases(&mut guards[1..], &policy, &intent);
    }

    #[test]
    fn distributed_setup_rejects_seed_equivocation_and_sender_spoofing() {
        for spoof in [false, true] {
            let (a, ca) = PolicyGuardDkgRound1::new(1, &[1, 4], [21; 32], [1; 32]).unwrap();
            let (b, mut cb) = PolicyGuardDkgRound1::new(4, &[1, 4], [21; 32], [4; 32]).unwrap();
            if spoof {
                cb[0].sender = 1;
                assert!(a.round2_open_seeds(&cb).is_err());
            } else {
                let (a, _) = a.round2_open_seeds(&cb).unwrap();
                let (_, mut ob) = b.round2_open_seeds(&ca).unwrap();
                ob[0].seed[0] ^= 1;
                let mut ot = IdealPolicyOt::default();
                assert!(matches!(
                    finalize_distributed_policy_guard(a, &ob, &mut ot),
                    Err(PolicyViolation::BarrierCommitmentMismatch { party_id: 4 })
                ));
            }
        }
    }

    #[test]
    fn test_policy_allowlist_velocity_quorum_tiers_anti_self_approval_and_bdoz_soundness() {
        let accel = CpuReferenceBackend::new();
        let allowed_dest = QsagAddress::from_pubkey_cshake256(
            "qsp",
            WitnessSuiteTag::MlDsa65,
            KeyIdentityKind::SingleOrThreshold,
            b"TREASURY_COLD_PK_1",
        )
        .unwrap();
        let unallowed_dest = QsagAddress::from_pubkey_cshake256(
            "qsp",
            WitnessSuiteTag::MlDsa65,
            KeyIdentityKind::SingleOrThreshold,
            b"ATTACKER_DRAIN_PK",
        )
        .unwrap();

        let policy = TransactionPolicy {
            chain_id: 1,
            pinned_suite: WitnessSuiteTag::MlDsa65,
            recipient_allowlist: vec![allowed_dest.commitment_256],
            max_single_tx_amount: 500_000,
            velocity_window_cap: 1_000_000,
            valid_not_before_secs: 1_700_000_000,
            valid_not_after_secs: 1_800_000_000,
            forbid_initiator_self_approval: true,
            hardware_guardian_party: Some(4),
            quorum_tiers: vec![
                QuorumTierRule {
                    max_amount_units: 10_000,
                    min_approvers: 2,
                    require_hardware_guardian: false,
                },
                QuorumTierRule {
                    max_amount_units: 500_000,
                    min_approvers: 3,
                    require_hardware_guardian: true,
                },
            ],
        };

        // Provision a 4-party committee `[1, 2, 3, 4]` and test subset quorum `[1, 2, 4]`!
        let all_guards = raw_test_guards([0x77u8; 32], &[1, 2, 3, 4]);
        assert!(format!("{:?}", all_guards[0]).contains("<REDACTED>"));
        let mut guards = raw_test_guards([0x77u8; 32], &[1, 2, 4]);

        let good_intent = TransactionIntent {
            chain_id: 1,
            suite: WitnessSuiteTag::MlDsa65,
            recipient: allowed_dest,
            amount_units: 250_000,
            rolling_window_spent: 600_000,
            window_id: 0,
            nonce: [0x55; 32],
            timestamp_secs: 1_750_000_000,
            initiator_party: 0,
            initiator_macs: Vec::new(),
            approver_parties: vec![1, 2, 4],
            payload_digest: [0xAB; 32],
            guard_authority_pk: [0; 32],
            rolling_window_accumulator: [0; 32],
            signing_key_id: [0; 32],
            policy_revision: 1,
            message_digest: cshake256_framed_32(b"QSAG.POLICY.MSG.V1", &[b"approved"]),
            signing_context_digest: cshake256_framed_32(b"QSAG.POLICY.CTX.V1", &[b"context"]),
            session_id: [0x12; 32],
            quorum_ids: vec![1, 2, 4],
        };

        let token = evaluate_policy_committed_barrier(
            &policy,
            &good_intent,
            [0x12; 32],
            good_intent.timestamp_secs,
            &mut guards,
            &accel,
        )
        .unwrap();
        assert!(
            guards
                .iter()
                .all(|g| g.accumulated_window_spend() == 850_000)
        );
        assert_eq!(token.intent_digest(), &good_intent.canonical_digest());
        assert!(!token.matches_signing(&[0; 32], b"approved", b"context", &[4, 1, 2]));
        assert!(token.matches_signing(
            &[0; 32],
            &good_intent.to_canonical_signing_bytes(&policy.canonical_digest()),
            b"context",
            &[4, 1, 2]
        ));
        for index in 0..4 {
            let mut changed = good_intent.clone();
            match index {
                0 => changed.amount_units += 1,
                1 => changed.recipient.commitment_256[0] ^= 1,
                2 => changed.guard_authority_pk[0] ^= 1,
                _ => changed.rolling_window_accumulator[0] ^= 1,
            }
            assert!(!token.matches_signing(
                &[0; 32],
                &changed.to_canonical_signing_bytes(&policy.canonical_digest()),
                b"context",
                &[1, 2, 4]
            ));
        }
        assert!(!token.matches_signing_for_policy(
            &[0; 32],
            &good_intent.to_canonical_signing_bytes(&policy.canonical_digest()),
            b"context",
            &[1, 2, 4],
            &[99; 32],
            &[0; 32]
        ));
        assert!(!token.matches_signing(&[0; 32], b"other", b"context", &[1, 2, 4]));
        assert!(!token.matches_signing(&[0; 32], b"approved", b"other", &[1, 2, 4]));
        assert!(!token.matches_signing(&[0; 32], b"approved", b"context", &[1, 2, 3]));
        let mut colluding = raw_test_guards([0x44; 32], &[1, 2]);
        assert_eq!(
            evaluate_policy_committed_barrier(
                &policy,
                &good_intent,
                [0x12; 32],
                good_intent.timestamp_secs,
                &mut colluding,
                &accel
            )
            .unwrap_err(),
            PolicyViolation::IntentBindingMismatch
        );
        let mut even = raw_test_guards([0x45; 32], &[1, 2, 3, 4]);
        let mut even_intent = good_intent.clone();
        even_intent.approver_parties = vec![1, 2, 3, 4];
        even_intent.quorum_ids = vec![1, 2, 3, 4];
        let mut conflicting = vec![even_intent; 4];
        conflicting[1].amount_units -= 1;
        assert_eq!(
            evaluate_per_party_intents_barrier(
                &policy,
                &conflicting,
                [0x12; 32],
                good_intent.timestamp_secs,
                &mut even,
                None,
                &accel
            )
            .unwrap_err(),
            PolicyViolation::BarrierBdozMacFailed
        );
        for g in &even {
            assert_slot_aborted_not_bricked(g, 0);
        }

        // Negative BDOZ Soundness Test A: 1-bit wire fault (`delta_0 ^= 1`) MUST be caught (`1 - 2^-128`)!
        let mut fault_guards = raw_test_guards([0x77; 32], &[1, 2, 4]);
        let intents3 = vec![
            good_intent.clone(),
            good_intent.clone(),
            good_intent.clone(),
        ];
        assert_eq!(
            evaluate_per_party_intents_barrier(
                &policy,
                &intents3,
                [0x12; 32],
                good_intent.timestamp_secs,
                &mut fault_guards,
                Some((0, (1u128, 0u128))),
                &accel,
            )
            .unwrap_err(),
            PolicyViolation::BarrierBdozMacFailed
        );
        for g in &fault_guards {
            assert_slot_aborted_not_bricked(g, 0);
        }

        let mut guards = raw_test_guards([0x77; 32], &[1, 2, 4]);
        // Negative BDOZ Soundness Test B: Insider signer 2 approves a DIFFERENT valid amount (`200_000`
        // vs `250_000`) -> pairwise BDOZ catches intent equivocation (`1 - 2^-256`)!
        let mut equiv_intents = vec![
            good_intent.clone(),
            good_intent.clone(),
            good_intent.clone(),
        ];
        equiv_intents[2].amount_units = 200_000;
        assert_eq!(
            evaluate_per_party_intents_barrier(
                &policy,
                &equiv_intents,
                [0x12; 32],
                good_intent.timestamp_secs,
                &mut guards,
                None,
                &accel,
            )
            .unwrap_err(),
            PolicyViolation::BarrierBdozMacFailed
        );

        let mut guards = raw_test_guards([0x77; 32], &[1, 2, 4]);
        // 1. Unallowlisted recipient -> refused!
        let mut bad_dest = good_intent.clone();
        bad_dest.recipient = unallowed_dest;
        bad_dest.session_id = [0x13; 32];
        assert_eq!(
            evaluate_policy_committed_barrier(
                &policy,
                &bad_dest,
                [0x13; 32],
                bad_dest.timestamp_secs,
                &mut guards,
                &accel
            )
            .unwrap_err(),
            PolicyViolation::RecipientNotAllowlisted
        );

        // 2. Velocity cap exceeded (`600_000 + 450_000 > 1_000_000`) -> refused!
        let mut bad_vel = good_intent.clone();
        bad_vel.amount_units = 450_000;
        bad_vel.session_id = [0x14; 32];
        assert_eq!(
            evaluate_policy_committed_barrier(
                &policy,
                &bad_vel,
                [0x14; 32],
                bad_vel.timestamp_secs,
                &mut guards,
                &accel
            )
            .unwrap_err(),
            PolicyViolation::VelocityCapOverflowOrExceeded
        );

        // 3. Initiator self-approval (`initiator == 1` inside `[1, 2, 4]`) -> refused!
        let mut self_app = good_intent.clone();
        self_app.initiator_party = 1;
        self_app.session_id = [0x15; 32];
        assert_eq!(
            evaluate_policy_committed_barrier(
                &policy,
                &self_app,
                [0x15; 32],
                self_app.timestamp_secs,
                &mut guards,
                &accel
            )
            .unwrap_err(),
            PolicyViolation::InitiatorSelfApprovalForbidden
        );

        // 4. Tier 2 missing hardware guardian (`party 4`) -> refused!
        let mut no_hw = good_intent;
        no_hw.approver_parties = vec![1, 2, 3];
        no_hw.session_id = [0x16; 32];
        assert_eq!(
            evaluate_policy_committed_barrier(
                &policy,
                &no_hw,
                [0x16; 32],
                no_hw.timestamp_secs,
                &mut guards,
                &accel
            )
            .unwrap_err(),
            PolicyViolation::MissingHardwareGuardian
        );
    }

    #[test]
    fn durable_checkpoint_restart_tamper_and_rollback() {
        let (mut policy, mut intent) = phase_fixture(&[1, 2, 4]);
        policy.max_single_tx_amount = 100;
        policy.velocity_window_cap = 100;
        intent.amount_units = 60;
        intent.rolling_window_spent = 0;
        let key = [0x91; 32];
        let mut guards = raw_test_guards([0x61; 32], &[1, 2, 4]);
        let old = guards[0].export_durable_checkpoint(&key, 1);
        run_phases(&mut guards, &policy, &intent);
        let snapshots: Vec<_> = guards
            .iter()
            .map(|g| g.export_durable_checkpoint(&key, 2))
            .collect();
        let mut restarted = raw_test_guards([0x61; 32], &[1, 2, 4]);
        for (g, bytes) in restarted.iter_mut().zip(&snapshots) {
            assert_eq!(g.restore_from_durable_checkpoint(bytes, &key, 2), Ok(2));
            assert_eq!(g.export_durable_checkpoint(&key, 2), *bytes);
            assert_eq!(g.accumulated_window_spend(), 60);
            assert!(g.is_nonce_burned(&intent.nonce));
            assert!(g.is_session_burned(&intent.session_id));
        }
        intent.nonce = [0xA2; 32];
        intent.session_id = [0xB2; 32];
        for g in &mut restarted {
            assert_eq!(
                g.round1_commit_intent(
                    &policy,
                    &intent,
                    intent.session_id,
                    intent.timestamp_secs,
                    0
                )
                .err(),
                Some(PolicyViolation::VelocityCapOverflowOrExceeded)
            );
        }
        let g = &mut restarted[0];
        assert_eq!(
            g.restore_from_durable_checkpoint(&old, &key, 0),
            Err(PolicyGuardError::Rollback)
        );
        assert_eq!(
            g.restore_from_durable_checkpoint(&snapshots[0], &key, 3),
            Err(PolicyGuardError::Rollback)
        );
        assert_eq!(
            g.restore_from_durable_checkpoint(&snapshots[1], &key, 0),
            Err(PolicyGuardError::WrongGuard)
        );
        for i in 0..snapshots[0].len() {
            let mut corrupt = snapshots[0].clone();
            corrupt[i] ^= 1;
            assert_eq!(
                g.restore_from_durable_checkpoint(&corrupt, &key, 0),
                Err(PolicyGuardError::AuthenticationFailed)
            );
        }
        assert_eq!(g.export_durable_checkpoint(&key, 2), snapshots[0]);
        let mut fresh = raw_test_guards([0x61; 32], &[1, 2, 4]);
        assert_eq!(
            fresh[0].restore_from_durable_checkpoint(&old, &key, 2),
            Err(PolicyGuardError::Rollback)
        );
        // A freshly authenticated higher generation still cannot erase live spend.
        let regressing = fresh[0].export_durable_checkpoint(&key, 5);
        assert_eq!(
            g.restore_from_durable_checkpoint(&regressing, &key, 0),
            Err(PolicyGuardError::Rollback)
        );
    }

    #[test]
    fn stateful_guard_enforces_accumulated_spend_cap_and_nonce_replay_even_when_caller_lies() {
        let accel = CpuReferenceBackend::new();
        let (mut policy, base_intent) = phase_fixture(&[1, 2, 4]);
        policy.max_single_tx_amount = 100;
        policy.velocity_window_cap = 100;

        // Path A: 4-round per-party phase state machine (`cap = 100`, two `60` intents).
        let mut guards = raw_test_guards([0x61; 32], &[1, 2, 4]);
        let mut tx1 = base_intent.clone();
        tx1.amount_units = 60;
        tx1.rolling_window_spent = 0;
        tx1.nonce = [0xA1; 32];
        tx1.session_id = [0xB1; 32];
        run_phases(&mut guards, &policy, &tx1);
        assert!(guards.iter().all(|g| g.accumulated_window_spend() == 60));
        assert!(guards.iter().all(|g| g.is_nonce_burned(&[0xA1; 32])));

        // Second `60` intent where caller dishonestly passes `rolling_window_spent = 0` and
        // `cumulative_epoch_spent = 0`: MUST be rejected by internal `accumulated_window_spend`!
        let mut tx2_over_cap = tx1.clone();
        tx2_over_cap.nonce = [0xA2; 32];
        tx2_over_cap.session_id = [0xB2; 32];
        tx2_over_cap.rolling_window_spent = 0;
        for g in &mut guards {
            assert_eq!(
                g.round1_commit_intent(
                    &policy,
                    &tx2_over_cap,
                    tx2_over_cap.session_id,
                    tx2_over_cap.timestamp_secs,
                    0,
                )
                .err(),
                Some(PolicyViolation::VelocityCapOverflowOrExceeded)
            );
        }

        // Replaying burned `nonce` (`[0xA1; 32]`) with small `amount_units = 10` and fresh session ID: MUST fail!
        let mut tx_replay_nonce = tx1.clone();
        tx_replay_nonce.amount_units = 10;
        tx_replay_nonce.session_id = [0xB3; 32];
        for g in &mut guards {
            assert_eq!(
                g.round1_commit_intent(
                    &policy,
                    &tx_replay_nonce,
                    tx_replay_nonce.session_id,
                    tx_replay_nonce.timestamp_secs,
                    0,
                )
                .err(),
                Some(PolicyViolation::DuplicateIntentNonce)
            );
        }

        // Replaying burned `session_id` (`[0xB1; 32]`) with fresh `nonce`: MUST fail!
        let mut tx_replay_session = tx1.clone();
        tx_replay_session.amount_units = 10;
        tx_replay_session.nonce = [0xA4; 32];
        for g in &mut guards {
            assert_eq!(
                g.round1_commit_intent(
                    &policy,
                    &tx_replay_session,
                    tx_replay_session.session_id,
                    tx_replay_session.timestamp_secs,
                    0,
                )
                .err(),
                Some(PolicyViolation::DuplicateIntentNonce)
            );
        }

        // Honest `40` intent (`60 + 40 == 100 <= 100`) succeeds, even if caller passes `rolling_window_spent = 0`!
        let mut tx3_fits = tx1.clone();
        tx3_fits.amount_units = 40;
        tx3_fits.nonce = [0xA5; 32];
        tx3_fits.session_id = [0xB5; 32];
        run_phases(&mut guards, &policy, &tx3_fits);
        assert!(guards.iter().all(|g| g.accumulated_window_spend() == 100));

        // Window mismatch rejected; advancing strictly to `window_id = 1` resets window spend while rejecting rollback!
        let mut tx_wrong_win = tx3_fits.clone();
        tx_wrong_win.window_id = 1;
        tx_wrong_win.nonce = [0xA6; 32];
        tx_wrong_win.session_id = [0xB6; 32];
        assert_eq!(
            guards[0]
                .round1_commit_intent(
                    &policy,
                    &tx_wrong_win,
                    tx_wrong_win.session_id,
                    tx_wrong_win.timestamp_secs,
                    0,
                )
                .err(),
            Some(PolicyViolation::WindowIdMismatch)
        );
        for g in &mut guards {
            assert_eq!(
                g.advance_velocity_window(&WindowAdvanceAuthorization::new(
                    &[43; 32], &[42; 32], 0, 0
                ))
                .err(),
                Some(PolicyViolation::WindowIdMismatch)
            );
            g.advance_velocity_window(&WindowAdvanceAuthorization::new(&[43; 32], &[42; 32], 0, 1))
                .unwrap();
            assert_eq!(g.current_window_id(), 1);
            assert_eq!(g.accumulated_window_spend(), 0);
            assert_eq!(
                g.advance_velocity_window(&WindowAdvanceAuthorization::new(
                    &[43; 32], &[42; 32], 0, 1
                ))
                .err(),
                Some(PolicyViolation::WindowIdMismatch)
            );
        }
        run_phases(&mut guards, &policy, &tx_wrong_win);
        assert!(guards.iter().all(|g| g.accumulated_window_spend() == 40));

        // Path B: Direct `evaluate_policy_committed_barrier` (`cap = 100`, two `60` intents).
        let mut barrier_guards = raw_test_guards([0x62; 32], &[1, 2, 4]);
        evaluate_policy_committed_barrier(
            &policy,
            &tx1,
            tx1.session_id,
            tx1.timestamp_secs,
            &mut barrier_guards,
            &accel,
        )
        .unwrap();
        assert_eq!(
            evaluate_policy_committed_barrier(
                &policy,
                &tx2_over_cap,
                tx2_over_cap.session_id,
                tx2_over_cap.timestamp_secs,
                &mut barrier_guards,
                &accel,
            )
            .unwrap_err(),
            PolicyViolation::VelocityCapOverflowOrExceeded
        );
    }

    #[test]
    fn peer_fault_aborts_only_session_slot_without_bricking_honest_guard_or_ledger() {
        let (policy, base_intent) = phase_fixture(&[1, 2, 4]);
        let mut guards = raw_test_guards([0x63; 32], &[1, 2, 4]);

        // 1. Complete an initial honest session (`accumulated_window_spend == 30`, slot 0 retired).
        run_phases(&mut guards, &policy, &base_intent);
        assert!(guards.iter().all(|g| g.accumulated_window_spend() == 30));
        assert!(guards.iter().all(|g| g.next_slot.get() == 1));

        // 2. Malicious peer `2` corrupts its Round-2 delta opening in session 2 (slot 1):
        //    Honest guards `1` and `4` MUST abort ONLY slot 1 without poisoning their keys or wiping `30` spend!
        let mut grief_intent = base_intent.clone();
        grief_intent.nonce = [0xC1; 32];
        grief_intent.session_id = [0xD1; 32];
        grief_intent.rolling_window_spent = 30;
        let (states, mut opens) = delta_phases(&mut guards, &policy, &grief_intent);
        opens[1].delta_i[0] ^= 0xDEAD_BEEF;
        for (st, g) in states.into_iter().zip(&mut guards) {
            assert!(matches!(
                st.round3_commit_sigma(g, &opens),
                Err(PolicyViolation::BarrierCommitmentMismatch { party_id: 2 })
            ));
            assert_slot_aborted_not_bricked(g, 1);
            assert_eq!(g.accumulated_window_spend(), 30);
        }

        // 3. Malicious peer `2` next corrupts its Round-4 sigma opening in session 3 (slot 2):
        let mut grief_sigma = grief_intent.clone();
        grief_sigma.nonce = [0xC2; 32];
        grief_sigma.session_id = [0xD2; 32];
        let (states, commits) = sigma_phases(&mut guards, &policy, &grief_sigma);
        let (finals, mut sig_opens): (Vec<_>, Vec<_>) = states
            .into_iter()
            .zip(&mut guards)
            .map(|(s, g)| s.round4_open_sigma(g, &commits).unwrap())
            .unzip();
        sig_opens[1].sigma_i[1] ^= 1;
        for (fin, g) in finals.into_iter().zip(&mut guards) {
            assert!(matches!(
                fin.finalize(g, &sig_opens),
                Err(PolicyViolation::BarrierCommitmentMismatch { party_id: 2 })
            ));
            assert_slot_aborted_not_bricked(g, 2);
            assert_eq!(g.accumulated_window_spend(), 30);
        }

        // 4. Subsequent honest session on slot 3 succeeds cleanly and advances durable spend to `40`!
        let mut recovery_intent = grief_sigma;
        recovery_intent.nonce = [0xC3; 32];
        recovery_intent.session_id = [0xD3; 32];
        run_phases(&mut guards, &policy, &recovery_intent);
        assert!(guards.iter().all(|g| !g.is_poisoned()));
        assert!(guards.iter().all(|g| g.next_slot.get() == 4));
        assert!(guards.iter().all(|g| g.accumulated_window_spend() == 40));
    }

    #[test]
    fn authenticated_initiator_prevents_self_approval_spoofing_and_transcript_equivocation() {
        let accel = CpuReferenceBackend::new();
        let all_ids = [10u16, 20, 30, 50];
        let approvers = [20u16, 30, 50];
        let (policy, mut intent) = phase_fixture(&approvers);
        intent.initiator_party = 10;

        let mut all_guards = raw_test_guards([0x88; 32], &all_ids);
        let guard_10 = all_guards.remove(0);
        // Remaining guards in `all_guards` are `[20, 30, 50]`.
        for g in &mut all_guards {
            g.set_require_authenticated_initiator(true);
        }

        // 1. Unauthenticated intent claiming `initiator_party = 10` is rejected!
        assert_eq!(
            evaluate_policy_committed_barrier_authenticated(
                &policy,
                &intent,
                intent.session_id,
                intent.timestamp_secs,
                &mut all_guards,
                &accel,
            )
            .unwrap_err(),
            PolicyViolation::UnauthenticatedInitiator
        );

        // 2. Insider approver `20` initiates a self-dealing request, tries to sign with `20`'s guard
        //    then rewrite `initiator_party = 10` to bypass `forbid_initiator_self_approval`: REJECTED!
        let mut forged = intent.clone();
        forged.initiator_party = 20;
        all_guards[0]
            .authenticate_initiated_intent(&policy, &mut forged)
            .unwrap();
        forged.initiator_party = 10;
        let forged_bytes = forged.to_canonical_signing_bytes(&policy.canonical_digest());
        forged.message_digest = cshake256_framed_32(b"QSAG.POLICY.MSG.V1", &[&forged_bytes]);
        assert_eq!(
            all_guards[1]
                .round1_commit_intent_authenticated(
                    &policy,
                    &forged,
                    forged.session_id,
                    forged.timestamp_secs,
                    forged.rolling_window_spent,
                )
                .err(),
            Some(PolicyViolation::UnauthenticatedInitiator)
        );

        // 3. Genuine authentication by `guard_10` succeeds across all approvers `[20, 30, 50]`!
        let signed_bytes = guard_10
            .authenticate_initiated_intent(&policy, &mut intent)
            .unwrap();
        // Tampering with `amount_units` after `guard_10` authenticated invalidates the MAC!
        let mut tampered = intent.clone();
        tampered.amount_units += 1;
        assert_eq!(
            all_guards[0]
                .round1_commit_intent_authenticated(
                    &policy,
                    &tampered,
                    tampered.session_id,
                    tampered.timestamp_secs,
                    tampered.rolling_window_spent,
                )
                .err(),
            Some(PolicyViolation::UnauthenticatedInitiator)
        );

        let token = evaluate_policy_committed_barrier_authenticated(
            &policy,
            &intent,
            intent.session_id,
            intent.timestamp_secs,
            &mut all_guards,
            &accel,
        )
        .unwrap();
        assert!(token.matches_signing(
            &intent.signing_key_id,
            &signed_bytes,
            b"context",
            &approvers,
        ));
    }

    #[test]
    fn quorum_switching_cannot_bypass_cumulative_velocity_cap_across_subsets() {
        let accel = CpuReferenceBackend::new();
        let (mut policy, base_intent) = phase_fixture(&[1, 2, 3, 4]);
        policy.max_single_tx_amount = 100;
        policy.velocity_window_cap = 100;
        policy.hardware_guardian_party = None;
        policy.quorum_tiers = vec![QuorumTierRule {
            max_amount_units: 100,
            min_approvers: 2,
            require_hardware_guardian: false,
        }];

        let mut committee = raw_test_guards([0x71; 32], &[1, 2, 3, 4]);
        let mut q1_intent = base_intent.clone();
        q1_intent.amount_units = 60;
        q1_intent.rolling_window_spent = 0;
        q1_intent.nonce = [0xE1; 32];
        q1_intent.session_id = [0xF1; 32];
        q1_intent.approver_parties = vec![1, 2];
        q1_intent.quorum_ids = vec![1, 2];

        // 1. Disjoint 2-of-4 subset `{1, 2}` without a fixed accounting guardian or shared ledger
        //    is refused on both batch and 4-round APIs so disjoint quorums cannot double-spend!
        assert_eq!(
            evaluate_policy_committed_barrier(
                &policy,
                &q1_intent,
                q1_intent.session_id,
                q1_intent.timestamp_secs,
                &mut committee[0..2],
                &accel,
            )
            .unwrap_err(),
            PolicyViolation::MissingHardwareGuardian
        );
        assert_eq!(
            committee[0]
                .round1_commit_intent(
                    &policy,
                    &q1_intent,
                    q1_intent.session_id,
                    q1_intent.timestamp_secs,
                    0,
                )
                .err(),
            Some(PolicyViolation::MissingHardwareGuardian)
        );
        assert!(committee.iter().all(|g| g.next_slot.get() == 0));

        // 2. With `SharedWindowSpendLedger`, `{1, 2}` approves `60`, and switching to disjoint
        //    quorum `{3, 4}` for a second `60` (even lying `rolling_window_spent = 0`) is rejected!
        let mut shared_ledger = SharedWindowSpendLedger::new(&policy, 0);
        let old_checkpoint = shared_ledger.export_durable_checkpoint(&[77; 32]);
        let mut saved = Vec::new();
        evaluate_policy_committed_barrier_with_ledger(
            &policy,
            &q1_intent,
            q1_intent.session_id,
            q1_intent.timestamp_secs,
            &mut committee[0..2],
            &mut shared_ledger,
            |ledger, _| {
                saved = ledger.export_durable_checkpoint(&[77; 32]);
                Ok(())
            },
            &accel,
        )
        .unwrap();
        assert_eq!(shared_ledger.accumulated_window_spend(), 60);

        let generation = shared_ledger.generation();
        assert_eq!(
            shared_ledger.restore_from_durable_checkpoint(&old_checkpoint, &[77; 32], 0),
            Err(PolicyGuardError::Rollback)
        );
        let mut recovered = SharedWindowSpendLedger::new(&policy, 0);
        assert_eq!(
            recovered.restore_from_durable_checkpoint(&old_checkpoint, &[77; 32], generation),
            Err(PolicyGuardError::Rollback)
        );
        let mut tampered = saved.clone();
        tampered[40] ^= 1;
        assert_eq!(
            recovered.restore_from_durable_checkpoint(&tampered, &[77; 32], generation),
            Err(PolicyGuardError::AuthenticationFailed)
        );
        recovered
            .restore_from_durable_checkpoint(&saved, &[77; 32], generation)
            .unwrap();
        assert_eq!(recovered.accumulated_window_spend(), 60);
        let verified = recovered.verified_velocity.as_ref().unwrap();
        assert_eq!(verified.spent_units(), 60);
        assert_eq!(verified.last_nonce(), generation);
        assert_eq!(verified.cap_units(), policy.velocity_window_cap);
        // Even a direct internal commit cannot bypass the retained verified cap.
        let mut over_cap = SharedWindowSpendLedger::new(&policy, 0);
        over_cap
            .restore_from_durable_checkpoint(&saved, &[77; 32], generation)
            .unwrap();
        assert_eq!(
            over_cap.record_approved_intent(policy.velocity_window_cap + 1, [0xA1; 32], [0xB1; 32]),
            Err(PolicyViolation::VelocityCapOverflowOrExceeded)
        );
        assert!(over_cap.failed);
        assert_eq!(
            over_cap.verified_velocity.as_ref().unwrap().spent_units(),
            60
        );
        assert!(recovered.is_nonce_burned(&q1_intent.nonce));
        shared_ledger = recovered;

        let mut q2_intent = q1_intent.clone();
        q2_intent.nonce = [0xE2; 32];
        q2_intent.session_id = [0xF2; 32];
        q2_intent.approver_parties = vec![3, 4];
        q2_intent.quorum_ids = vec![3, 4];
        assert_eq!(
            evaluate_policy_committed_barrier_with_ledger(
                &policy,
                &q2_intent,
                q2_intent.session_id,
                q2_intent.timestamp_secs,
                &mut committee[2..4],
                &mut shared_ledger,
                |_, _| Ok(()),
                &accel,
            )
            .unwrap_err(),
            PolicyViolation::VelocityCapOverflowOrExceeded
        );
        assert_eq!(committee[2].next_slot.get(), 0);
        assert_eq!(committee[3].next_slot.get(), 0);

        // A failed persistence callback withholds release and disables all later approvals.
        q2_intent.amount_units = 10;
        assert_eq!(
            evaluate_policy_committed_barrier_with_ledger(
                &policy,
                &q2_intent,
                q2_intent.session_id,
                q2_intent.timestamp_secs,
                &mut committee[2..4],
                &mut shared_ledger,
                |_, _| Err(PolicyViolation::LedgerPersistenceFailed),
                &accel
            )
            .unwrap_err(),
            PolicyViolation::LedgerPersistenceFailed
        );
        assert!(shared_ledger.failed);
        q2_intent.nonce = [0xE5; 32];
        q2_intent.session_id = [0xF5; 32];
        assert_eq!(
            evaluate_policy_committed_barrier_with_ledger(
                &policy,
                &q2_intent,
                q2_intent.session_id,
                q2_intent.timestamp_secs,
                &mut committee[2..4],
                &mut shared_ledger,
                |_, _| Ok(()),
                &accel
            )
            .unwrap_err(),
            PolicyViolation::LedgerPersistenceFailed
        );

        // 3. With a fixed accounting guardian `Some(4)`, switching `{1, 4}` (`60`) then `{2, 4}` (`60`)
        //    intersects at party `4` and rejects the second `60` even with dishonest `rolling_window_spent = 0`!
        let mut hw_policy = policy;
        hw_policy.hardware_guardian_party = Some(4);
        let mut hw_committee = raw_test_guards([0x72; 32], &[1, 2, 4]);
        let mut g1_intent = base_intent.clone();
        g1_intent.amount_units = 60;
        g1_intent.rolling_window_spent = 0;
        g1_intent.nonce = [0xE3; 32];
        g1_intent.session_id = [0xF3; 32];
        g1_intent.approver_parties = vec![1, 4];
        g1_intent.quorum_ids = vec![1, 4];
        let g4 = hw_committee.pop().unwrap();
        let g2 = hw_committee.pop().unwrap();
        let g1 = hw_committee.pop().unwrap();
        let mut pair_14 = vec![g1, g4];
        evaluate_policy_committed_barrier(
            &hw_policy,
            &g1_intent,
            g1_intent.session_id,
            g1_intent.timestamp_secs,
            &mut pair_14,
            &accel,
        )
        .unwrap();
        let g4_after = pair_14.pop().unwrap();
        let mut pair_24 = vec![g2, g4_after];
        let mut g2_intent = g1_intent;
        g2_intent.nonce = [0xE4; 32];
        g2_intent.session_id = [0xF4; 32];
        g2_intent.approver_parties = vec![2, 4];
        g2_intent.quorum_ids = vec![2, 4];
        assert_eq!(
            evaluate_policy_committed_barrier(
                &hw_policy,
                &g2_intent,
                g2_intent.session_id,
                g2_intent.timestamp_secs,
                &mut pair_24,
                &accel,
            )
            .unwrap_err(),
            PolicyViolation::VelocityCapOverflowOrExceeded
        );
    }

    #[test]
    fn batch_barrier_enforces_authoritative_current_timestamp_before_consuming_slot() {
        let accel = CpuReferenceBackend::new();
        let (policy, intent) = phase_fixture(&[1, 2, 4]);
        let mut guards = raw_test_guards([0x73; 32], &[1, 2, 4]);

        // Expired wall-clock (`150 > valid_not_after_secs == 100`) and mismatched live clock (`51 != 50`)
        // both fail closed with `TimestampOutsideWindow` without consuming any preprocessing slot!
        for bad_now in [0u64, 51, 150] {
            assert_eq!(
                evaluate_policy_committed_barrier(
                    &policy,
                    &intent,
                    intent.session_id,
                    bad_now,
                    &mut guards,
                    &accel,
                )
                .unwrap_err(),
                PolicyViolation::TimestampOutsideWindow
            );
            assert!(
                guards
                    .iter()
                    .all(|g| g.next_slot.get() == 0 && !g.is_poisoned())
            );
        }

        // Exact authoritative clock (`50 == intent.timestamp_secs`) succeeds cleanly!
        evaluate_policy_committed_barrier(
            &policy,
            &intent,
            intent.session_id,
            intent.timestamp_secs,
            &mut guards,
            &accel,
        )
        .unwrap();
        assert!(guards.iter().all(|g| g.next_slot.get() == 1));
    }
}

#[cfg(test)]
mod cleanup_tests {
    use super::*;
    #[test]
    fn malformed_quorums_never_fan_out() {
        let (policy, intent) = super::tests::phase_fixture(&[1, 2]);
        for ids in [alloc::vec![], alloc::vec![1, 1], alloc::vec![2, 1]] {
            let mut intent = intent.clone();
            intent.quorum_ids = ids;
            let token = AuthorizedSignReleaseToken {
                session_id: intent.session_id,
                policy_digest: policy.canonical_digest(),
                intent_digest: [0; 32],
                intent,
                quorum_split: false,
            };
            assert!(token.into_quorum_party_tokens().is_empty());
        }
    }

    #[test]
    fn cust06_staging_pool_isolates_unauthenticated_spam_and_enforces_self_mac() {
        let recipient = QsagAddress::from_pubkey_cshake256(
            "qsp",
            WitnessSuiteTag::MlDsa65,
            qsag_addr::KeyIdentityKind::SingleOrThreshold,
            b"cust06-recipient",
        )
        .unwrap();
        let policy = TransactionPolicy {
            chain_id: 1,
            pinned_suite: WitnessSuiteTag::MlDsa65,
            recipient_allowlist: alloc::vec![recipient.commitment_256],
            max_single_tx_amount: 100,
            velocity_window_cap: 10_000,
            valid_not_before_secs: 1,
            valid_not_after_secs: 1_000,
            forbid_initiator_self_approval: false,
            hardware_guardian_party: Some(2),
            quorum_tiers: alloc::vec![QuorumTierRule {
                max_amount_units: 100,
                min_approvers: 2,
                require_hardware_guardian: true,
            }],
        };
        let guards = trusted_dealer_setup_for_testing([0x77; 32], &[1, 2]);
        let mut pool = PendingIntentStagingPool::new(4);

        // 1. Unauthenticated spammer spoofing `initiator_party == 1` directly against guard 1
        //    (even when `forbid_initiator_self_approval == false`) is rejected with `UnauthenticatedInitiator`
        //    and consumes ZERO staging slots and ZERO committed replay slots!
        for i in 0..500u32 {
            let mut forged_nonce = [0u8; 32];
            forged_nonce[..4].copy_from_slice(&i.to_be_bytes());
            let forged_intent = TransactionIntent {
                chain_id: 1,
                suite: WitnessSuiteTag::MlDsa65,
                recipient: recipient.clone(),
                amount_units: 10,
                rolling_window_spent: 0,
                window_id: 0,
                nonce: forged_nonce,
                timestamp_secs: 10,
                initiator_party: 1,
                initiator_macs: Vec::new(),
                approver_parties: alloc::vec![1, 2],
                payload_digest: [0x11; 32],
                guard_authority_pk: [0x22; 32],
                rolling_window_accumulator: [0x33; 32],
                signing_key_id: [0x44; 32],
                policy_revision: 1,
                message_digest: [0; 32],
                signing_context_digest: [0x55; 32],
                session_id: forged_nonce,
                quorum_ids: alloc::vec![1, 2],
            };
            assert_eq!(
                pool.stage_authenticated_intent(&policy, &guards[0], &forged_intent, 10, 30),
                Err(PolicyViolation::UnauthenticatedInitiator)
            );
        }
        assert!(pool.is_empty());

        // 2. Authenticated pending proposals stage cleanly, expire after TTL without burning committed
        //    replay slots, and never evict committed replay nonces!
        for i in 0..4u8 {
            let mut valid_intent = TransactionIntent {
                chain_id: 1,
                suite: WitnessSuiteTag::MlDsa65,
                recipient: recipient.clone(),
                amount_units: 10,
                rolling_window_spent: 0,
                window_id: 0,
                nonce: [i + 1; 32],
                timestamp_secs: 10,
                initiator_party: 1,
                initiator_macs: Vec::new(),
                approver_parties: alloc::vec![1, 2],
                payload_digest: [0x11; 32],
                guard_authority_pk: [0x22; 32],
                rolling_window_accumulator: [0x33; 32],
                signing_key_id: [0x44; 32],
                policy_revision: 1,
                message_digest: [0; 32],
                signing_context_digest: [0x55; 32],
                session_id: [i + 0x81; 32],
                quorum_ids: alloc::vec![1, 2],
            };
            guards[0]
                .authenticate_initiated_intent(&policy, &mut valid_intent)
                .unwrap();
            pool.stage_authenticated_intent(&policy, &guards[0], &valid_intent, 10, 30)
                .unwrap();
            pool.complete_intent(&valid_intent.nonce, &valid_intent.session_id);
            pool.stage_authenticated_intent(&policy, &guards[1], &valid_intent, 10, 30)
                .unwrap();
        }
        assert_eq!(pool.len(), 4);
        // Advance past `10 + 30 = 40`: all 4 abandoned pending proposals expire without touching `guards[1]`.
        assert_eq!(pool.evict_expired(40), 4);
        assert!(pool.is_empty());
        assert!(!guards[1].is_nonce_burned(&[1; 32]));
    }

    #[test]
    fn cust06_monotone_replay_floor_compacts_without_unburning_and_survives_checkpoint() {
        let mut guards = trusted_dealer_setup_for_testing([0x99; 32], &[1, 2]);
        let guard = &mut guards[0];

        // Fill all 256 slots with monotone nonces `1..=256`, plus keep a high random nonce `[0xFF; 32]`.
        for i in 1..=255u32 {
            let mut n = [0u8; 32];
            n[..4].copy_from_slice(&i.to_be_bytes());
            guard
                .record_approved_intent(100_000, i as u128, n, n)
                .unwrap();
        }
        guard
            .record_approved_intent(100_000, 256, [0xFF; 32], [0xFF; 32])
            .unwrap();

        // Compact monotone floor up to `200`: nonces `<= 200` remain permanently burned via floor,
        // nonces `201..=255` and `[0xFF; 32]` remain explicitly retained, and 200 slots are freed!
        let mut floor200 = [0u8; 32];
        floor200[..4].copy_from_slice(&200u32.to_be_bytes());
        guard
            .compact_monotone_replay_floor(floor200, floor200)
            .unwrap();

        // Regressing the floor is rejected.
        let mut floor199 = [0u8; 32];
        floor199[..4].copy_from_slice(&199u32.to_be_bytes());
        assert_eq!(
            guard.compact_monotone_replay_floor(floor199, floor199),
            Err(PolicyViolation::IntentBindingMismatch)
        );

        // Floored nonces (`1`, `200`) AND retained high nonces (`[0xFF; 32]`) CANNOT replay!
        let mut n1 = [0u8; 32];
        n1[..4].copy_from_slice(&1u32.to_be_bytes());
        assert!(guard.is_nonce_burned(&n1));
        assert!(guard.is_nonce_burned(&floor200));
        assert!(guard.is_nonce_burned(&[0xFF; 32]));
        assert_eq!(
            guard.record_approved_intent(100_000, 257, n1, n1),
            Err(PolicyViolation::DuplicateIntentNonce)
        );

        // Subsequent new intents (> 256 total in the same window!) succeed AND preserve `min_nonce_watermark`.
        for i in 256..=320u32 {
            let mut n = [0u8; 32];
            n[..4].copy_from_slice(&i.to_be_bytes());
            guard
                .record_approved_intent(100_000, (i + 10) as u128, n, n)
                .unwrap();
        }
        assert!(guard.is_nonce_burned(&n1));

        // Durable checkpoint export + restore preserves the monotone floor and blocks floored replays.
        let snap = guard.export_durable_checkpoint(&[0xAB; 32], 11);
        let mut fresh_guards = trusted_dealer_setup_for_testing([0x99; 32], &[1, 2]);
        fresh_guards[0]
            .restore_from_durable_checkpoint(&snap, &[0xAB; 32], 11)
            .unwrap();
        assert!(fresh_guards[0].is_nonce_burned(&n1));
        assert!(fresh_guards[0].is_nonce_burned(&floor200));
        assert!(fresh_guards[0].is_nonce_burned(&[0xFF; 32]));
    }

    #[test]
    fn policy_engine_integrates_macaroon_discharges_and_pq_biscuits_before_bdoz_barrier() {
        let accel = qsag_accel::CpuReferenceBackend::new();
        let (policy, mut intent) = crate::tests::phase_fixture(&[1, 2]);
        intent.session_id = [0x71; 32];
        intent.nonce = [0x72; 32];
        let policy_digest = policy.canonical_digest();
        let signing_bytes = intent.to_canonical_signing_bytes(&policy_digest);
        intent.message_digest = cshake256_framed_32(b"QSAG.POLICY.MSG.V1", &[&signing_bytes]);

        let mut guards = crate::tests::raw_test_guards([0x44; 32], &[1, 2]);
        let engine = PolicyEngine::new(&policy, 0b0001);

        // 1. Attenuated SpongeMacaroon with 3P discharge: narrower MaxAmount(1) refuses BEFORE
        // consuming any BDOZ preprocessing slot!
        let root_key = [0xA1; 32];
        let third_key = [0xB2; 32];
        let mut denied_mac = SpongeMacaroon::issue(&root_key, [0x01; 32], policy_digest);
        denied_mac
            .attenuate(Caveat::MaxAmount(intent.amount_units.saturating_sub(1)))
            .unwrap();
        let verifier = MacaroonVerifier::new(&root_key, [0x01; 32], policy_digest);
        assert_eq!(
            engine
                .authorize_committed_barrier(
                    &intent,
                    intent.session_id,
                    intent.timestamp_secs,
                    Some(&CapabilityGate::Macaroon {
                        verifier: &verifier,
                        token: &denied_mac,
                        discharges: &[],
                    }),
                    &mut guards,
                    &accel,
                )
                .err(),
            Some(PolicyViolation::CapabilityDenied(CapabilityError::Denied))
        );
        assert_eq!(guards[0].next_slot.get(), 0);

        let mut ok_mac = SpongeMacaroon::issue(&root_key, [0x01; 32], policy_digest);
        ok_mac
            .attenuate(Caveat::Resource(intent.recipient.commitment_256))
            .unwrap();
        ok_mac.attenuate(Caveat::Actions(0b0011)).unwrap();
        ok_mac
            .attenuate(Caveat::MaxAmount(intent.amount_units))
            .unwrap();
        ok_mac.attenuate(Caveat::ThirdParty([0xCC; 32])).unwrap();
        let mut discharge = SpongeMacaroon::issue_discharge(&third_key, [0xCC; 32], policy_digest);
        ok_mac.bind_discharge(&mut discharge).unwrap();
        let discharges = [Discharge {
            token: &discharge,
            root_key: &third_key,
        }];
        let release = engine
            .authorize_committed_barrier(
                &intent,
                intent.session_id,
                intent.timestamp_secs,
                Some(&CapabilityGate::Macaroon {
                    verifier: &verifier,
                    token: &ok_mac,
                    discharges: &discharges,
                }),
                &mut guards,
                &accel,
            )
            .unwrap();
        let party_tokens = release.into_quorum_party_tokens();
        assert_eq!(party_tokens.len(), 2);
        // Splitting a child again cannot multiply a successful barrier's releases.
        for token in party_tokens {
            let mut tokens = token.into_quorum_party_tokens();
            assert_eq!(tokens.len(), 1);
            assert_eq!(tokens.pop().unwrap().into_quorum_party_tokens().len(), 1);
        }

        // 2. Ephemeral Compact1122 PqBiscuit 2-hop delegation chain + PoP seal gates BDOZ barrier!
        let dp = qsag_fts::FrontierDpTable::build(qsag_fts::FrontierFtsProfile::Compact1122);
        let mut auth =
            PqBiscuitAuthorityKey::keygen([0xD1; 32], [0xD2; 32], 1, &accel).unwrap();
        let auth_pk = *auth.public_key();
        let mut intent2 = intent.clone();
        intent2.session_id = [0x81; 32];
        intent2.nonce = [0x82; 32];
        intent2.rolling_window_spent = intent.amount_units;
        let sb2 = intent2.to_canonical_signing_bytes(&policy_digest);
        intent2.message_digest = cshake256_framed_32(b"QSAG.POLICY.MSG.V1", &[&sb2]);

        let (b0, s1) = auth
            .mint(
                &dp,
                [0x91; 32],
                policy_digest,
                &[Caveat::Resource(intent2.recipient.commitment_256)],
                [0x92; 32],
                &[0x93; 32],
                &accel,
            )
            .unwrap();
        let (b1, s2) = s1
            .attenuate(
                &b0,
                &dp,
                &[
                    Caveat::Actions(0b0001),
                    Caveat::MaxAmount(intent2.amount_units),
                ],
                [0x94; 32],
                &[0x95; 32],
                &accel,
            )
            .unwrap();
        let req2 = CapabilityRequest::from_policy_intent(
            &policy,
            &intent2,
            0b0001,
            intent2.timestamp_secs,
        );
        let b_sealed = s2.seal(&b1, &dp, Some(&req2), &[0x96; 32], &accel).unwrap();
        let release2 = engine
            .authorize_committed_barrier(
                &intent2,
                intent2.session_id,
                intent2.timestamp_secs,
                Some(&CapabilityGate::Biscuit {
                    authority_pk: &auth_pk,
                    dp: &dp,
                    token: &b_sealed,
                }),
                &mut guards,
                &accel,
            )
            .unwrap();
        assert_eq!(release2.quorum_ids(), &[1, 2]);
    }
}
