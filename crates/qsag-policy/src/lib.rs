#![cfg_attr(not(test), deny(clippy::unwrap_used, clippy::expect_used))]
#![no_std]
#![forbid(unsafe_code)]
//! Authenticated transaction-predicate guard (`qsag-policy`) evaluating recipient allowlists,
//! per-tx & rolling velocity caps, anti-self-approval, and quorum-tier rules inside committed
//! Eurocrypt-2011 pairwise 2-lane BDOZ GF($2^{128}$) MAC barriers before releasing any MPC share.

extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

pub mod durable;
pub use durable::PolicyGuardError;

use alloc::vec::Vec;
use core::cell::Cell;
use core::fmt;

use qsag_accel::AcceleratorBackend;
use qsag_accel::ct::{ct_eq_bytes, ct_eq_u128};

#[inline(never)]
fn ct_zeroize_bytes(secret: &mut [u8]) {
    secret.fill(0);
    core::hint::black_box(&mut *secret);
    qsag_accel::ct::ct_zeroize_bytes(secret);
}

#[inline(never)]
fn ct_zeroize_u128s(secret: &mut [u128]) {
    secret.fill(0);
    core::hint::black_box(&mut *secret);
    qsag_accel::ct::ct_zeroize_u128s(secret);
}
use qsag_accel::gf2_128::gf2_128_mul;
use qsag_accel::keccak::{commit_mpc_broadcast, cshake256_framed_32};
use qsag_addr::{QsagAddress, WitnessSuiteTag};

/// Default number of single-use preprocessed pairwise BDOZ MAC tuples per signer guard.
pub const BDOZ_PREPROC_SLOTS: usize = 64;

/// Bounded capacity of the durable per-window burned intent-nonce & session-ID rings.
pub const MAX_BURNED_INTENT_NONCES: usize = 256;

/// Pairwise cryptographic authenticator binding `initiator_party` to an approver's guard share.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InitiatorPeerMac {
    pub approver_party: u16,
    pub mac_tag: [u8; 32],
}

/// Amount-escalating quorum tier rule.
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
    UnauthenticatedInitiator,
    RecipientNotAllowlisted,
    SingleTxCapExceeded,
    VelocityCapOverflowOrExceeded,
    InitiatorSelfApprovalForbidden,
    DuplicateApproverInQuorum,
    NoMatchingQuorumTier,
    InsufficientTierApprovers { have: u16, need: u16 },
    MissingHardwareGuardian,
    EmptySignerBarrierSet,
    IntentBindingMismatch,
    GuardPoisoned,
    BarrierPreprocExhausted,
    BarrierCommitmentMismatch { party_id: u16 },
    BarrierBdozMacFailed,
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

    /// Deterministically evaluate `intent` against `self` in constant-time allowlist scan mode.
    pub fn evaluate(&self, intent: &TransactionIntent) -> Result<(), PolicyViolation> {
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
        let cumulative = intent
            .rolling_window_spent
            .checked_add(intent.amount_units)
            .ok_or(PolicyViolation::VelocityCapOverflowOrExceeded)?;
        if cumulative > self.velocity_window_cap {
            return Err(PolicyViolation::VelocityCapOverflowOrExceeded);
        }

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

        // Select the first applicable quorum tier `intent.amount_units <= tier.max_amount_units`.
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
        let mut appr = Vec::with_capacity(self.approver_parties.len() * 2);
        let mut sorted_approvers = self.approver_parties.clone();
        sorted_approvers.sort_unstable();
        for p in sorted_approvers {
            appr.extend_from_slice(&p.to_be_bytes());
        }
        let quorum_bytes: Vec<u8> = self
            .quorum_ids
            .iter()
            .flat_map(|p| p.to_be_bytes())
            .collect();
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
        let mut appr = Vec::with_capacity(self.approver_parties.len() * 2);
        let mut sorted_approvers = self.approver_parties.clone();
        sorted_approvers.sort_unstable();
        for p in sorted_approvers {
            appr.extend_from_slice(&p.to_be_bytes());
        }
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
                &self
                    .quorum_ids
                    .iter()
                    .flat_map(|p| p.to_be_bytes())
                    .collect::<Vec<_>>(),
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
    pub fn new(authority_key: &[u8; 32], policy_id: &[u8; 32],
        prev_epoch: u64, new_window_epoch: u64) -> Self
    {
        Self {
            new_window_epoch,
            mac: cshake256_framed_32(b"QSAG.POLICY.WINDOW_ADVANCE/v1",
                &[authority_key, policy_id, &prev_epoch.to_be_bytes(), &new_window_epoch.to_be_bytes()]),
        }
    }
}

struct WindowAuthority {
    policy_id: [u8; 32],
    key: [u8; 32],
}
impl Drop for WindowAuthority {
    fn drop(&mut self) { ct_zeroize_bytes(&mut self.key); }
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
    consumed_peer_slots: Vec<(u16, u64)>,
    next_slot: Cell<usize>,
    poisoned: bool,
    enrolled_party_id: u16,
    active_phase: Option<(usize, u8)>,
    current_window_id: u64,
    accumulated_window_spend: u128,
    burned_intent_nonces: Vec<[u8; 32]>,
    burned_nonce_cursor: usize,
    min_nonce_watermark: Option<[u8; 32]>,
    burned_sessions: Vec<[u8; 32]>,
    burned_session_cursor: usize,
    min_session_watermark: Option<[u8; 32]>,
    require_authenticated_initiator: bool,
    window_authority: Option<WindowAuthority>,
    durable_key_id: [u8; 32],
    durable_generation: Cell<u64>,
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

fn derive_peer_slot_alpha(alpha_root: &[u128; 2], peer_id: u16, peer_slot: usize) -> [u128; 2] {
    let mut root_bytes = [0u8; 32];
    root_bytes[..16].copy_from_slice(&alpha_root[0].to_le_bytes());
    root_bytes[16..].copy_from_slice(&alpha_root[1].to_le_bytes());
    let raw = cshake256_framed_32(
        b"QSAG.POLICY.PEER_SLOT_ALPHA.V1",
        &[
            &root_bytes,
            &peer_id.to_be_bytes(),
            &(peer_slot as u64).to_be_bytes(),
        ],
    );
    ct_zeroize_bytes(&mut root_bytes);
    [
        policy_pair(raw)[0],
        policy_pair(raw)[1],
    ]
}

impl PolicySignerGuardShare {
    /// Trusted provisioning, before using the guard: pin an application policy ID
    /// and its authority key. The ID must uniquely identify the policy/ledger.
    /// Cannot replace an authority or enable resets after spending has started.
    /// Provision identically before restoring a durable checkpoint.
    pub fn with_window_authority(mut self, policy_id: [u8; 32], mut key: [u8; 32])
        -> Result<Self, PolicyViolation>
    {
        if self.window_authority.is_some() || self.next_slot.get() != 0
            || self.current_window_id != 0 || self.accumulated_window_spend != 0
            || self.active_phase.is_some() || self.poisoned
        {
            ct_zeroize_bytes(&mut key);
            return Err(PolicyViolation::IntentBindingMismatch);
        }
        // Durable snapshots cannot be restored under different authority provisioning.
        self.durable_key_id = cshake256_framed_32(b"QSAG.POLICY.WINDOW_KEY/v1",
            &[&self.durable_key_id, &policy_id, &key]);
        self.window_authority = Some(WindowAuthority { policy_id, key });
        ct_zeroize_bytes(&mut key);
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

    pub fn set_require_authenticated_initiator(&mut self, required: bool) {
        self.require_authenticated_initiator = required;
    }

    pub fn is_nonce_burned(&self, nonce: &[u8; 32]) -> bool {
        let mut hit = self.min_nonce_watermark.is_some_and(|floor| *nonce <= floor);
        for b in &self.burned_intent_nonces {
            hit |= ct_eq_bytes(b, nonce);
        }
        hit
    }

    pub fn is_session_burned(&self, session_id: &[u8; 32]) -> bool {
        let mut hit = self.min_session_watermark.is_some_and(|floor| *session_id <= floor);
        for b in &self.burned_sessions {
            hit |= ct_eq_bytes(b, session_id);
        }
        hit
    }

    /// Roll the guard into a strictly newer velocity window (`next_window_id > current_window_id`),
    /// resetting spend while permanently retaining nonce and session replay protection.
    pub fn advance_velocity_window(&mut self, authorization: &WindowAdvanceAuthorization) -> Result<(), PolicyViolation> {
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
        let authority = self.window_authority.as_ref().ok_or(PolicyViolation::IntentBindingMismatch)?;
        let expected = WindowAdvanceAuthorization::new(&authority.key, &authority.policy_id,
            self.current_window_id, next_window_id);
        if !ct_eq_bytes(&expected.mac, &authorization.mac) {
            return Err(PolicyViolation::IntentBindingMismatch);
        }
        self.current_window_id = next_window_id;
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
            if approver == self.party_id {
                continue;
            }
            let (_, z_seed) = self
                .pairwise_zero_seeds
                .iter()
                .find(|(p, _)| *p == approver)
                .ok_or(PolicyViolation::UnauthenticatedInitiator)?;
            let mac_tag = cshake256_framed_32(
                b"QSAG.POLICY.INITIATOR_AUTH_MAC.V1",
                &[
                    z_seed,
                    &self.party_id.to_be_bytes(),
                    &approver.to_be_bytes(),
                    &auth_digest,
                ],
            );
            macs.push(InitiatorPeerMac {
                approver_party: approver,
                mac_tag,
            });
        }
        intent.initiator_macs = macs;
        let signing_bytes = intent.to_canonical_signing_bytes(&policy_digest);
        intent.message_digest = cshake256_framed_32(b"QSAG.POLICY.MSG.V1", &[&signing_bytes]);
        Ok(signing_bytes)
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
        if intent.initiator_party == self.party_id {
            if policy.forbid_initiator_self_approval {
                return Err(PolicyViolation::InitiatorSelfApprovalForbidden);
            }
            return Ok(());
        }
        let (_, z_seed) = self
            .pairwise_zero_seeds
            .iter()
            .find(|(p, _)| *p == intent.initiator_party)
            .ok_or(PolicyViolation::UnauthenticatedInitiator)?;
        let policy_digest = policy.canonical_digest();
        let auth_digest = intent.initiator_auth_digest(&policy_digest);
        let expected_tag = cshake256_framed_32(
            b"QSAG.POLICY.INITIATOR_AUTH_MAC.V1",
            &[
                z_seed,
                &intent.initiator_party.to_be_bytes(),
                &self.party_id.to_be_bytes(),
                &auth_digest,
            ],
        );
        let mut matched = false;
        let mut count_for_self = 0usize;
        for m in &intent.initiator_macs {
            if m.approver_party == self.party_id {
                count_for_self += 1;
                matched |= ct_eq_bytes(&m.mac_tag, &expected_tag);
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
        let effective_prior = self
            .accumulated_window_spend
            .max(intent.rolling_window_spent)
            .max(external_floor);
        let projected = effective_prior
            .checked_add(intent.amount_units)
            .ok_or(PolicyViolation::VelocityCapOverflowOrExceeded)?;
        if projected > velocity_window_cap {
            return Err(PolicyViolation::VelocityCapOverflowOrExceeded);
        }
        Ok(projected)
    }

    fn record_approved_intent(
        &mut self,
        projected_spend: u128,
        nonce: [u8; 32],
        session_id: [u8; 32],
    ) {
        self.accumulated_window_spend = projected_spend;
        // Keep a bounded sparse window above a permanent lexicographic floor.
        // Evicted values remain burned forever, including across velocity windows.
        for (values, floor, value) in [
            (&mut self.burned_intent_nonces, &mut self.min_nonce_watermark, nonce),
            (&mut self.burned_sessions, &mut self.min_session_watermark, session_id),
        ] {
            values.push(value);
            values.sort_unstable();
            values.dedup();
            if values.len() > MAX_BURNED_INTENT_NONCES {
                *floor = Some(values.remove(0));
            }
        }
    }

    fn incoming_slot_alpha(&self, peer_id: u16, peer_slot: usize) -> [u128; 2] {
        derive_peer_slot_alpha(&self.bdoz_alpha_share, peer_id, peer_slot)
    }

    fn is_peer_slot_consumed(&self, peer_id: u16, peer_slot: usize) -> bool {
        if peer_slot >= 64 {
            return true;
        }
        self.consumed_peer_slots
            .iter()
            .find(|(p, _)| *p == peer_id)
            .is_some_and(|(_, mask)| ((mask >> peer_slot) & 1) != 0)
    }

    fn retire_own_slot(&mut self, slot: usize) {
        if let Some(r) = self.preproc_r.get_mut(slot) {
            ct_zeroize_u128s(r);
        }
        for (_, vec_m) in &mut self.preproc_outgoing_macs {
            if let Some(m) = vec_m.get_mut(slot) {
                ct_zeroize_u128s(m);
            }
        }
    }

    fn retire_peer_slot(&mut self, peer_id: u16, peer_slot: usize) {
        if peer_slot < 64 {
            if let Some((_, mask)) = self
                .consumed_peer_slots
                .iter_mut()
                .find(|(p, _)| *p == peer_id)
            {
                *mask |= 1u64 << peer_slot;
            } else {
                self.consumed_peer_slots.push((peer_id, 1u64 << peer_slot));
            }
        }
        for (p, vec_k) in &mut self.preproc_incoming_keys {
            if *p == peer_id
                && let Some(k) = vec_k.get_mut(peer_slot)
            {
                ct_zeroize_u128s(k);
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
        ct_zeroize_u128s(&mut self.bdoz_alpha_share);
        ct_zeroize_bytes(&mut self.local_salt_seed);
        for (_, seed) in &mut self.pairwise_zero_seeds {
            ct_zeroize_bytes(seed);
        }
        for r in &mut self.preproc_r {
            ct_zeroize_u128s(r);
        }
        for (_, vec_m) in &mut self.preproc_outgoing_macs {
            for m in vec_m {
                ct_zeroize_u128s(m);
            }
        }
        for (_, vec_k) in &mut self.preproc_incoming_keys {
            for k in vec_k {
                ct_zeroize_u128s(k);
            }
        }
    }
}

impl Drop for PolicySignerGuardShare {
    fn drop(&mut self) {
        self.poison();
    }
}

pub type PartyPolicyGuard = PolicySignerGuardShare;
pub type PolicyIntent = TransactionIntent;

/// Unforgeable linear capability token (`!Clone`, `!Copy`, private constructor) minted ONLY when
/// `TransactionPolicy::evaluate` AND the committed pairwise BDOZ 2-lane GF($2^{128}$) MAC barrier succeed!
#[derive(Debug)]
pub struct AuthorizedSignReleaseToken {
    session_id: [u8; 32],
    policy_digest: [u8; 32],
    intent_digest: [u8; 32],
    intent: TransactionIntent,
}

impl AuthorizedSignReleaseToken {
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
}

/// Trusted recovery/test setup: the caller knows every guard secret.
/// Provision `n` [`PolicySignerGuardShare`]s with Eurocrypt-2011 pairwise BDOZ correlations and
/// private pairwise PRG zero-share seeds (`0` shared global mask seeds; offline entropy zeroized!).
#[cfg(any(test, feature = "test-dealer"))]
