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
#[cfg(feature = "std")]
pub use durable::{FsPolicyDurableLedger, FsPolicyGenerationFence};

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
    LedgerPersistenceFailed,
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
        qsag_verified::policy_and_addr::checked_velocity_spend(
            intent.rolling_window_spent, intent.amount_units, self.velocity_window_cap,
        ).ok_or(PolicyViolation::VelocityCapOverflowOrExceeded)?;

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
        let guard = qsag_verified::StatefulVelocityGuard::new_window(
            self.current_window_id,
            velocity_window_cap,
            self.durable_key_id,
            *session_id,
        );
        let (guard, prior_res) = guard.authorize_spend(qsag_verified::VelocitySpendRequest {
            window_id: intent.window_id,
            nonce: 1,
            amount_units: effective_prior,
            policy_pin: self.durable_key_id,
            authority_pin: *session_id,
        });
        if prior_res.is_err() {
            return Err(PolicyViolation::VelocityCapOverflowOrExceeded);
        }
        let (guard, tx_res) = guard.authorize_spend(qsag_verified::VelocitySpendRequest {
            window_id: intent.window_id,
            nonce: 2,
            amount_units: intent.amount_units,
            policy_pin: self.durable_key_id,
            authority_pin: *session_id,
        });
        match tx_res {
            Ok(_) => Ok(guard.spent_units()),
            Err(_) => Err(PolicyViolation::VelocityCapOverflowOrExceeded),
        }
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
        let raw = cshake256_framed_32(b"QSAG.POLICY.ALPHA_SH.V2", &[&ent, &p_be]);
        alphas.push([
            policy_pair(raw)[0],
            policy_pair(raw)[1],
        ]);

        let mut r_slots = Vec::with_capacity(BDOZ_PREPROC_SLOTS);
        for s in 0..BDOZ_PREPROC_SLOTS {
            let s_be = (s as u32).to_be_bytes();
            let r_raw = cshake256_framed_32(b"QSAG.POLICY.PREPROC_R.V2", &[&ent, &p_be, &s_be]);
            r_slots.push([
                policy_pair(r_raw)[0],
                policy_pair(r_raw)[1],
            ]);
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
            consumed_peer_slots.push((pid_j, 0u64));

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
                    cshake256_framed_32(b"QSAG.POLICY.BDOZ_KEY.V2", &[&ent, &pj_be, &pi_be, &s_be]);
                let k_j_from_i = [
                    policy_pair(k_j_from_i_raw)[0],
                    policy_pair(k_j_from_i_raw)[1],
                ];
                let m_i_to_j = [
                    k_j_from_i[0] ^ gf2_128_mul(alpha_j_slot[0], r_is[0]),
                    k_j_from_i[1] ^ gf2_128_mul(alpha_j_slot[1], r_is[1]),
                ];
                m_vec.push(m_i_to_j);

                // Key held by `i` on `j`'s wire `r_{j, s}`:
                let k_i_from_j_raw =
                    cshake256_framed_32(b"QSAG.POLICY.BDOZ_KEY.V2", &[&ent, &pi_be, &pj_be, &s_be]);
                k_vec.push([
                    policy_pair(k_i_from_j_raw)[0],
                    policy_pair(k_i_from_j_raw)[1],
                ]);
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
            burned_intent_nonces: Vec::new(),
            burned_nonce_cursor: 0,
            min_nonce_watermark: None,
            burned_sessions: Vec::new(),
            burned_session_cursor: 0,
            min_session_watermark: None,
            require_authenticated_initiator: true,
        });
    }

    // Zeroize all offline preprocessing material before returning!
    for a in &mut alphas {
        ct_zeroize_u128s(a);
    }
    for vec_r in &mut all_r {
        for r in vec_r {
            ct_zeroize_u128s(r);
        }
    }
    ct_zeroize_bytes(&mut ent);
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
    let x_vec = [
        (
            policy_pair(*policy_digest)[0],
            policy_pair(*policy_digest)[1],
        ),
        (
            policy_pair(*intent_digest)[0],
            policy_pair(*intent_digest)[1],
        ),
        (
            policy_pair(meta)[0],
            policy_pair(meta)[1],
        ),
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
    let w0 = policy_pair(w_raw)[0];
    let w1 = policy_pair(w_raw)[1];
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
    ) -> (u128, u128) {
        let mut z0 = 0u128;
        let mut z1 = 0u128;
        for &peer in quorum_ids {
            if peer == self.party_id {
                continue;
            }
            if let Some((_, seed)) = self.pairwise_zero_seeds.iter().find(|(p, _)| *p == peer) {
                let prf = cshake256_framed_32(
                    b"QSAG.POLICY.PAIR_ZERO_PRF.V2",
                    &[seed, session_id, q_digest],
                );
                z0 ^= policy_pair(prf)[0];
                z1 ^= policy_pair(prf)[1];
            }
        }
        (z0, z1)
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
    generation: u64,
    failed: bool,
    current_window_id: u64,
    accumulated_window_spend: u128,
    burned_intent_nonces: Vec<[u8; 32]>,
    min_nonce_watermark: Option<[u8; 32]>,
    burned_sessions: Vec<[u8; 32]>,
    min_session_watermark: Option<[u8; 32]>,
    window_authority: Option<WindowAuthority>,
}

impl SharedWindowSpendLedger {
    pub fn new(policy: &TransactionPolicy, initial_window_id: u64) -> Self {
        Self {
            policy_digest: policy.canonical_digest(),
            generation: 0,
            failed: false,
            current_window_id: initial_window_id,
            accumulated_window_spend: 0,
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
        if self.window_authority.is_some() {
            return Err(PolicyViolation::IntentBindingMismatch);
        }
        self.window_authority = Some(WindowAuthority { policy_id, key });
        Ok(self)
    }

    pub const fn current_window_id(&self) -> u64 {
        self.current_window_id
    }

    pub const fn accumulated_window_spend(&self) -> u128 {
        self.accumulated_window_spend
    }

    pub fn is_nonce_burned(&self, nonce: &[u8; 32]) -> bool {
        let mut hit = self.min_nonce_watermark.is_some_and(|floor| *nonce <= floor);
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
        self.generation = self.generation.checked_add(1)
            .ok_or(PolicyViolation::LedgerPersistenceFailed)?;
        self.current_window_id = next_window_id;
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
        let effective_prior = self
            .accumulated_window_spend
            .max(intent.rolling_window_spent);
        let guard = qsag_verified::StatefulVelocityGuard::new_window(
            self.current_window_id,
            policy.velocity_window_cap,
            self.policy_digest,
            *session_id,
        );
        let (guard, prior_res) = guard.authorize_spend(qsag_verified::VelocitySpendRequest {
            window_id: intent.window_id,
            nonce: 1,
            amount_units: effective_prior,
            policy_pin: self.policy_digest,
            authority_pin: *session_id,
        });
        if prior_res.is_err() {
            return Err(PolicyViolation::VelocityCapOverflowOrExceeded);
        }
        let (guard, tx_res) = guard.authorize_spend(qsag_verified::VelocitySpendRequest {
            window_id: intent.window_id,
            nonce: 2,
            amount_units: intent.amount_units,
            policy_pin: self.policy_digest,
            authority_pin: *session_id,
        });
        match tx_res {
            Ok(_) => Ok(guard.spent_units()),
            Err(_) => Err(PolicyViolation::VelocityCapOverflowOrExceeded),
        }
    }

    fn record_approved_intent(
        &mut self,
        projected_spend: u128,
        nonce: [u8; 32],
        session_id: [u8; 32],
    ) {
        // Capacity was checked before the barrier consumed preprocessing.
        self.generation += 1;
        self.accumulated_window_spend = projected_spend;
        for (values, floor, value) in [
            (
                &mut self.burned_intent_nonces,
                &mut self.min_nonce_watermark,
                nonce,
            ),
            (
                &mut self.burned_sessions,
                &mut self.min_session_watermark,
                session_id,
            ),
        ] {
            values.push(value);
            values.sort_unstable();
            values.dedup();
            if values.len() > MAX_BURNED_INTENT_NONCES {
                *floor = Some(values.remove(0));
            }
        }
    }
}

/// Evaluate `policy` across `quorum_guards` where each signer $i$ independently evaluates its own
/// local `per_party_intents[i]` inside a 2-round **commit-then-open Eurocrypt-2011 pairwise BDOZ**
/// barrier (`0` central MAC key reconstruction, private pairwise zero-shares!).
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

    let mut quorum_ids = Vec::with_capacity(m);
    let mut quorum_flat = Vec::with_capacity(m * 2);
    for (idx, g) in quorum_guards.iter().enumerate() {
        for &prev in &quorum_ids[..idx] {
            if prev == g.party_id {
                return Err(PolicyViolation::DuplicateApproverInQuorum);
            }
        }
        quorum_ids.push(g.party_id);
        quorum_flat.extend_from_slice(&g.party_id.to_be_bytes());
    }
    quorum_ids.sort_unstable();
    quorum_flat.clear();
    for id in &quorum_ids {
        quorum_flat.extend_from_slice(&id.to_be_bytes());
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
    let quorum_digest = cshake256_framed_32(b"QSAG.POLICY.QUORUM_SET.V2", &[&quorum_flat]);
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

    // Round 1: Each party `i` independently consumes a single-use BDOZ preprocessing slot and
    // broadcasts masked wire `delta_i = r_{i, slot} ^ folded_x_i`!
    struct PartyLocalRound1 {
        party_id: u16,
        slot: usize,
        intent_digest: [u8; 32],
        folded_x: (u128, u128),
        delta_broadcast: (u128, u128),
    }

    let mut r1_states: Vec<PartyLocalRound1> = Vec::with_capacity(m);
    let online_res: Result<(), PolicyViolation> = (|| {
        for (g, intent_i) in quorum_guards.iter().zip(per_party_intents.iter()) {
            let slot = g.next_slot.get();
            g.next_slot.set(slot + 1);

            let intent_digest = intent_i.canonical_digest();
            let folded_x = compute_folded_policy_wire(
                &policy_digest,
                &intent_digest,
                &session_id,
                intent_i.initiator_party,
                intent_i.window_id,
                &intent_i.nonce,
                accel,
            )?;
            let r_mask = g.preproc_r[slot];
            let delta = (r_mask[0] ^ folded_x.0, r_mask[1] ^ folded_x.1);
            #[cfg(test)]
            let delta = {
                let mut delta = delta;
                if let Some((fault_idx, fault_xor)) = injected_delta_fault
                    && fault_idx == r1_states.len()
                {
                    delta.0 ^= fault_xor.0;
                    delta.1 ^= fault_xor.1;
                }
                delta
            };
            r1_states.push(PartyLocalRound1 {
                party_id: g.party_id,
                slot,
                intent_digest,
                folded_x,
                delta_broadcast: delta,
            });
        }

        let mut delta_transcript = Vec::new();
        for st in &r1_states {
            delta_transcript.extend_from_slice(&st.party_id.to_be_bytes());
            delta_transcript.extend_from_slice(&(st.slot as u64).to_be_bytes());
            delta_transcript.extend_from_slice(&st.delta_broadcast.0.to_le_bytes());
            delta_transcript.extend_from_slice(&st.delta_broadcast.1.to_le_bytes());
        }

        // Round 2a (Commit ONLY): Every party `i` computes its pairwise BDOZ difference share `sigma_i`
        // strictly from its own `PolicySignerGuardShare` + Round-1 `delta_broadcast`s and commits BEFORE any open!
        let mut commits = Vec::with_capacity(m);
        let mut deferred_openings = Vec::with_capacity(m);

        for (g, st_i) in quorum_guards.iter().zip(r1_states.iter()) {
            let (mut sigma0, mut sigma1) =
                g.pairwise_zero_share(&quorum_ids, &session_id, &quorum_digest);

            for st_j in &r1_states {
                if st_j.party_id == g.party_id {
                    continue;
                }
                let m_ij = g.outgoing_mac(st_j.party_id, st_i.slot)?;
                let k_ij = g.incoming_key(st_j.party_id, st_j.slot)?;
                let alpha_ij = g.incoming_slot_alpha(st_j.party_id, st_j.slot);
                let expected_r_j0 = st_i.folded_x.0 ^ st_j.delta_broadcast.0;
                let expected_r_j1 = st_i.folded_x.1 ^ st_j.delta_broadcast.1;

                let chi = cshake256_framed_32(
                    b"QSAG.POLICY.PAIR_WEIGHT.V1",
                    &[
                        &session_id,
                        &policy_digest,
                        &st_i.intent_digest,
                        &quorum_digest,
                        &delta_transcript,
                        &g.party_id.min(st_j.party_id).to_be_bytes(),
                        &g.party_id.max(st_j.party_id).to_be_bytes(),
                    ],
                );
                let chi0 = policy_pair(chi)[0];
                let chi1 = policy_pair(chi)[1];
                sigma0 ^= gf2_128_mul(
                    chi0,
                    m_ij[0] ^ k_ij[0] ^ gf2_128_mul(alpha_ij[0], expected_r_j0),
                );
                sigma1 ^= gf2_128_mul(
                    chi1,
                    m_ij[1] ^ k_ij[1] ^ gf2_128_mul(alpha_ij[1], expected_r_j1),
                );
            }

            let mut payload = [0u8; 32];
            payload[0..16].copy_from_slice(&sigma0.to_le_bytes());
            payload[16..32].copy_from_slice(&sigma1.to_le_bytes());
            let slot_be = (st_i.slot as u32).to_be_bytes();
            let salt = cshake256_framed_32(
                b"QSAG.POLICY.COMMIT_SALT.V2",
                &[&g.local_salt_seed, &session_id, &slot_be],
            );
            let comm = commit_mpc_broadcast(&session_id, 0x504F_4C32, g.party_id, &payload, &salt);
            commits.push((g.party_id, comm));
            deferred_openings.push((g.party_id, payload, (sigma0, sigma1), salt));
        }

        // Round 2b: Verify ALL commitments in constant time FIRST, then verify `\bigoplus_i \sigma_i == (0, 0)`!
        let mut sigma_xor = (0u128, 0u128);
        for ((c_pid, comm), (o_pid, payload, sigmas, salt)) in
            commits.iter().zip(deferred_openings.iter())
        {
            debug_assert_eq!(c_pid, o_pid);
            let expected_comm =
                commit_mpc_broadcast(&session_id, 0x504F_4C32, *o_pid, payload, salt);
            if !ct_eq_bytes(&expected_comm, comm) {
                return Err(PolicyViolation::BarrierCommitmentMismatch { party_id: *o_pid });
            }
            sigma_xor.0 ^= sigmas.0;
            sigma_xor.1 ^= sigmas.1;
        }

        let mut all_digests_equal = true;
        for st in &r1_states[1..] {
            all_digests_equal &= ct_eq_bytes(&st.intent_digest, &r1_states[0].intent_digest);
        }

        if !ct_eq_u128(sigma_xor.0, 0) || !ct_eq_u128(sigma_xor.1, 0) || !all_digests_equal {
            return Err(PolicyViolation::BarrierBdozMacFailed);
        }

        Ok(())
    })();

    if let Err(err) = online_res {
        for (idx, g_abort) in quorum_guards.iter_mut().enumerate() {
            if let Some(st_own) = r1_states.get(idx) {
                let peer_slots: Vec<(u16, usize)> = r1_states
                    .iter()
                    .filter(|st| st.party_id != g_abort.party_id)
                    .map(|st| (st.party_id, st.slot))
                    .collect();
                g_abort.abort_session_slot(st_own.slot, &peer_slots);
            }
        }
        return Err(err);
    }

    let global_projected = projected_spends.iter().copied().max().unwrap_or(0);
    if let Some(ledger) = shared_ledger.as_deref_mut() {
        ledger.record_approved_intent(global_projected, per_party_intents[0].nonce, session_id);
    }

    // Atomically advance accumulated window spend, burn intent nonces + session ID, and retire slots.
    for (idx, g) in quorum_guards.iter_mut().enumerate() {
        let peer_slots: Vec<(u16, usize)> = r1_states
            .iter()
            .filter(|st| st.party_id != g.party_id)
            .map(|st| (st.party_id, st.slot))
            .collect();
        let recorded_spend = if shared_ledger.is_some() {
            projected_spends[idx].max(global_projected)
        } else {
            projected_spends[idx]
        };
        g.record_approved_intent(recorded_spend, per_party_intents[idx].nonce, session_id);
        g.abort_session_slot(r1_states[idx].slot, &peer_slots);
    }

    Ok(AuthorizedSignReleaseToken {
        session_id,
        policy_digest,
        intent_digest: r1_states[0].intent_digest,
        intent: per_party_intents[0].clone(),
    })
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
    persist: impl FnOnce(&SharedWindowSpendLedger, &[PolicySignerGuardShare]) -> Result<(), PolicyViolation>,
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
impl<W: qsag_fts::ot::AuthenticatedOtWire> PolicyAuthenticatedOt for qsag_fts::ot::CommittedCorrelatedOt<W> {
    fn exchange(&mut self, local_party: u16, peer: u16, domain: [u8; 32], alternatives: &[[u128; 2]], choices: &[bool]) -> Result<Vec<u128>, PolicyViolation> {
        if local_party != self.party_id() || alternatives.len() != choices.len() { return Err(PolicyViolation::IntentBindingMismatch); }
        let failed = |_| PolicyViolation::BarrierBdozMacFailed;
        if local_party < peer {
            self.send_values(peer, domain, alternatives).map_err(failed)?;
            self.receive_values(peer, domain, choices).map_err(failed)
        } else {
            let values = self.receive_values(peer, domain, choices).map_err(failed)?;
            self.send_values(peer, domain, alternatives).map_err(failed)?;
            Ok(values)
        }
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
        ct_zeroize_bytes(&mut self.seed);
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
        mut entropy: [u8; 32],
    ) -> Result<(Self, Vec<PolicyGuardSeedCommitMsg>), PolicyViolation> {
        let mut ids = party_ids.to_vec();
        ids.sort_unstable();
        if ids.len() < 2 || !ids.contains(&party_id) || ids.windows(2).any(|w| w[0] == w[1]) {
            ct_zeroize_bytes(&mut entropy);
            return Err(PolicyViolation::IntentBindingMismatch);
        }
        let digest =
            cshake256_framed_32(b"QSAG.POLICY.DKG.V1", &[&setup_id, &policy_ids_bytes(&ids)]);
        let mut local = cshake256_framed_32(
            b"QSAG.POLICY.DKG.LOCAL.V1",
            &[&entropy, &digest, &party_id.to_be_bytes()],
        );
        ct_zeroize_bytes(&mut entropy);
        let mut guard = PolicySignerGuardShare {
            party_id,
            enrolled_party_id: party_id,
            active_phase: None,
            poisoned: false,
            bdoz_alpha_share: policy_pair(cshake256_framed_32(
                b"QSAG.POLICY.DKG.ALPHA.V1",
                &[&local],
            )),
            window_authority: None,
            durable_key_id: cshake256_framed_32(b"QSAG.POLICY.DURABLE_KEY.V2", &[&local]),
            durable_generation: Cell::new(0),
            local_salt_seed: local,
            pairwise_zero_seeds: Vec::new(),
            preproc_r: Vec::new(),
            preproc_outgoing_macs: Vec::new(),
            preproc_incoming_keys: Vec::new(),
            consumed_peer_slots: Vec::new(),
            next_slot: Cell::new(0),
            current_window_id: 0,
            accumulated_window_spend: 0,
            burned_intent_nonces: Vec::new(),
            burned_nonce_cursor: 0,
            min_nonce_watermark: None,
            burned_sessions: Vec::new(),
            burned_session_cursor: 0,
            min_session_watermark: None,
            require_authenticated_initiator: true,
        };
        ct_zeroize_bytes(&mut local);
        for slot in 0..BDOZ_PREPROC_SLOTS {
            guard.preproc_r.push(policy_pair(cshake256_framed_32(
                b"QSAG.POLICY.DKG.R.V1",
                &[&guard.local_salt_seed, &(slot as u64).to_be_bytes()],
            )));
        }
        let mut seeds = Vec::new();
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
        g.consumed_peer_slots.push((o.sender, 0u64));
        let mut alternatives = Vec::new();
        let mut choices = Vec::new();
        let mut keys = Vec::new();
        for slot in 0..BDOZ_PREPROC_SLOTS {
            let mut slot_alpha = g.incoming_slot_alpha(o.sender, slot);
            let mut key = [0u128; 2];
            for (lane, key_lane) in key.iter_mut().enumerate() {
                for bit in 0..128 {
                    let mut raw = cshake256_framed_32(
                        b"QSAG.POLICY.DKG.OT_PAD.V1",
                        &[
                            &g.local_salt_seed,
                            &domain,
                            &(slot as u64).to_be_bytes(),
                            &[lane as u8, bit as u8],
                        ],
                    );
                    let pad = policy_pair(raw)[0];
                    ct_zeroize_bytes(&mut raw);
                    alternatives.push([pad, pad ^ gf2_128_mul(slot_alpha[lane], 1u128 << bit)]);
                    choices.push(((g.preproc_r[slot][lane] >> bit) & 1) != 0);
                    *key_lane ^= pad;
                }
            }
            ct_zeroize_u128s(&mut slot_alpha);
            keys.push(key);
        }
        let response = ot.exchange(g.party_id, o.sender, domain, &alternatives, &choices);
        for pair in &mut alternatives {
            ct_zeroize_u128s(pair);
        }
        for choice in &mut choices {
            qsag_asm::volatile_fill(core::slice::from_mut(choice), false);
        }
        let mut selected = match response {
            Ok(values) => values,
            Err(err) => {
                for key in &mut keys {
                    ct_zeroize_u128s(key);
                }
                return Err(err);
            }
        };
        if selected.len() != BDOZ_PREPROC_SLOTS * 256 {
            ct_zeroize_u128s(&mut selected);
            for key in &mut keys {
                ct_zeroize_u128s(key);
            }
            return Err(PolicyViolation::BarrierBdozMacFailed);
        }
        let mut macs = Vec::new();
        for chunk in selected.chunks_exact(256) {
            macs.push([
                chunk[..128].iter().fold(0, |a, b| a ^ b),
                chunk[128..].iter().fold(0, |a, b| a ^ b),
            ]);
        }
        ct_zeroize_u128s(&mut selected);
        g.preproc_outgoing_macs.push((o.sender, macs));
        g.preproc_incoming_keys.push((o.sender, keys));
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

/// Round two opens only delta. Sigma cannot be computed until every delta is verified.
pub type PartyPolicyDeltaOpenAndSigmaCommitMsg = PartyPolicyDeltaOpenMsg;

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
        ct_zeroize_bytes(&mut self.guard_binding);
        ct_zeroize_bytes(&mut self.salt);
        ct_zeroize_bytes(&mut self.sigma_salt);
        ct_zeroize_u128s(&mut self.delta);
        ct_zeroize_u128s(&mut self.folded);
        ct_zeroize_u128s(&mut self.sigma);
    }
}

/// Owns the pending opening. Abandoning a state leaves its guard latched; discard that guard.
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

fn policy_pair(bytes: [u8; 32]) -> [u128; 2] {
    [
        u128::from_le_bytes(core::array::from_fn(|i| bytes[i])),
        u128::from_le_bytes(core::array::from_fn(|i| bytes[16 + i])),
    ]
}

fn delta_commitment(c: &PartyPolicyDeltaCommitMsg, salt: &[u8; 32], delta: &[u128; 2]) -> [u8; 32] {
    cshake256_framed_32(
        b"DELTA_COMMIT.V2",
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
        b"SIGMA_COMMIT",
        &[
            &c.transcript_digest,
            &c.party_id.to_be_bytes(),
            salt,
            &policy_pair_bytes(sigma),
        ],
    )
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
        let r = *self
            .preproc_r
            .get(slot)
            .ok_or(PolicyViolation::BarrierPreprocExhausted)?;
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
        let x = match compute_folded_policy_wire(
            &own.policy_digest,
            &own.intent_digest,
            &session_id,
            intent.initiator_party,
            intent.window_id,
            &intent.nonce,
            &qsag_accel::CpuReferenceBackend::new(),
        ) {
            Ok(v) => v,
            Err(err) => {
                self.abort_session_slot(slot, &[]);
                return Err(err);
            }
        };
        let delta = [r[0] ^ x.0, r[1] ^ x.1];
        let salt = cshake256_framed_32(
            b"QSAG.POLICY.DELTA_SALT.V1",
            &[
                &self.local_salt_seed,
                &session_id,
                &(slot as u64).to_be_bytes(),
            ],
        );
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
            folded: [x.0, x.1],
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
    ) -> Result<
        (
            PartyPolicyRound2State,
            PartyPolicyDeltaOpenAndSigmaCommitMsg,
        ),
        PolicyViolation,
    > {
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
            if opens.len() != self.commits.len() {
                return Err(PolicyViolation::IntentBindingMismatch);
            }
            let mut transcript = Vec::new();
            for (c, o) in self.commits.iter().zip(&opens) {
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
            let own = &self.context.own;
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
            let z = guard.pairwise_zero_share(&own.quorum_ids, &own.session_id, &q_digest);
            let mut sigma = [z.0, z.1];
            for (c, o) in self.commits.iter().zip(&opens) {
                if c.party_id == own.party_id {
                    continue;
                }
                let m = guard.outgoing_mac(c.party_id, own.slot)?;
                let k = guard.incoming_key(c.party_id, c.slot)?;
                let mut peer_alpha = guard.incoming_slot_alpha(c.party_id, c.slot);
                let chi = policy_pair(cshake256_framed_32(
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
                            ^ gf2_128_mul(
                                peer_alpha[lane],
                                self.context.folded[lane] ^ o.delta_i[lane],
                            ),
                    );
                }
                ct_zeroize_u128s(&mut peer_alpha);
            }
            let salt = cshake256_framed_32(
                b"QSAG.POLICY.SIGMA_SALT.V1",
                &[
                    &guard.local_salt_seed,
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
            guard.active_phase = Some((own.slot, 3));
            self.context.sigma = sigma;
            self.context.sigma_salt = salt;
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
            if opens.len() != self.commits.len() {
                return Err(PolicyViolation::IntentBindingMismatch);
            }
            let mut sum = [0u128; 2];
            for (c, o) in self.commits.iter().zip(&opens) {
                if c.party_id != o.party_id
                    || !ct_eq_bytes(
                        &c.commitment,
                        &sigma_commitment(c, &o.sigma_salt_i, &o.sigma_i),
                    )
                {
                    return Err(PolicyViolation::BarrierCommitmentMismatch {
                        party_id: c.party_id,
                    });
                }
                sum[0] ^= o.sigma_i[0];
                sum[1] ^= o.sigma_i[1];
            }
            if !ct_eq_u128(sum[0], 0) || !ct_eq_u128(sum[1], 0) {
                return Err(PolicyViolation::BarrierBdozMacFailed);
            }
            let projected_spend = guard.check_window_nonce_and_projected_spend(
                self.context.velocity_window_cap,
                &self.context.intent,
                &self.context.own.session_id,
                self.context.cumulative_epoch_spent,
            )?;
            guard.record_approved_intent(
                projected_spend,
                self.context.intent.nonce,
                self.context.own.session_id,
            );
            guard.abort_session_slot(own_slot, &peer_slots);
            Ok(AuthorizedSignReleaseToken {
                session_id: self.context.own.session_id,
                policy_digest: self.context.own.policy_digest,
                intent_digest: self.context.own.intent_digest,
                intent: self.context.intent.clone(),
            })
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

#[cfg(test)]
mod tests {
    fn raw_test_guards(entropy: [u8; 32], ids: &[u16]) -> Vec<PolicySignerGuardShare> {
        let mut guards: Vec<_> = super::trusted_dealer_setup_for_testing(entropy, ids).into_iter()
            .map(|g| g.with_window_authority([42; 32], [43; 32]).unwrap()).collect();
        for guard in &mut guards { guard.set_require_authenticated_initiator(false); }
        guards
    }
    #[test]
    fn window_authority_is_required_and_bound_to_checkpoint() {
        let mut bare = super::trusted_dealer_setup_for_testing([9; 32], &[1, 2]).remove(0);
        let auth = WindowAdvanceAuthorization::new(&[43; 32], &[42; 32], 0, 1);
        assert!(bare.advance_velocity_window(&auth).is_err());
        let guard = bare.with_window_authority([42; 32], [43; 32]).unwrap();
        let snapshot = guard.export_durable_checkpoint(&[7; 32], 1);
        let mut other = super::trusted_dealer_setup_for_testing([9; 32], &[1, 2]).remove(0)
            .with_window_authority([41; 32], [43; 32]).unwrap();
        assert!(other.restore_from_durable_checkpoint(&snapshot, &[7; 32], 1).is_err());
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
    fn initiator_authentication_is_default() {
        assert!(super::trusted_dealer_setup_for_testing([8; 32], &[1, 2]).iter().all(|g| g.require_authenticated_initiator));
    }
    #[test]
    fn bounded_replay_window_never_reaccepts_evicted_nonces() {
        let mut guards = raw_test_guards([9; 32], &[1, 2]);
        let guard = &mut guards[0];
        for i in 0u32..600 {
            let mut nonce = [0; 32];
            nonce[28..].copy_from_slice(&i.to_be_bytes());
            guard.record_approved_intent(i as u128, nonce, nonce);
        }
        for i in 0u32..600 {
            let mut nonce = [0; 32];
            nonce[28..].copy_from_slice(&i.to_be_bytes());
            assert!(guard.is_nonce_burned(&nonce));
            assert!(guard.is_session_burned(&nonce));
        }
        let checkpoint = guard.export_durable_checkpoint(&[7; 32], 600);
        guard.restore_from_durable_checkpoint(&checkpoint, &[7; 32], 600).unwrap();
        let mut older = raw_test_guards([9; 32], &[1, 2]);
        for i in 0u32..100 {
            let mut nonce = [0; 32];
            nonce[28..].copy_from_slice(&i.to_be_bytes());
            older[0].record_approved_intent(i as u128, nonce, nonce);
        }
        older[0].restore_from_durable_checkpoint(&checkpoint, &[7; 32], 600).unwrap();
        guard.advance_velocity_window(&WindowAdvanceAuthorization::new(&[43; 32], &[42; 32], 0, 1)).unwrap();
        assert!(guard.is_nonce_burned(&[0; 32]));
    }

    use alloc::format;
    use alloc::vec;
    use qsag_accel::CpuReferenceBackend;
    use qsag_addr::KeyIdentityKind;

    use super::*;

    fn phase_fixture(ids: &[u16]) -> (TransactionPolicy, TransactionIntent) {
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
    struct IdealPolicyOt {
        peers: Vec<(u16, [u128; 2], [u8; 32])>,
    }
    impl Drop for IdealPolicyOt {
        fn drop(&mut self) {
            for (_, alpha, seed) in &mut self.peers {
                ct_zeroize_u128s(alpha);
                ct_zeroize_bytes(seed);
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
            assert_eq!(alternatives.len(), BDOZ_PREPROC_SLOTS * 256);
            assert_eq!(choices.len(), alternatives.len());
            let (_, local_alpha, _) = self
                .peers
                .iter()
                .find(|(id, _, _)| *id == local_party)
                .unwrap();
            let (_, alpha, seed) = self.peers.iter().find(|(id, _, _)| *id == peer).unwrap();
            let mut selected = Vec::new();
            for (i, choice) in choices.iter().enumerate() {
                let slot = i / 256;
                let lane = i % 256 / 128;
                let bit = i % 128;
                let local_slot_alpha = derive_peer_slot_alpha(local_alpha, peer, slot);
                let peer_slot_alpha = derive_peer_slot_alpha(alpha, local_party, slot);
                assert_eq!(
                    alternatives[i][0] ^ alternatives[i][1],
                    gf2_128_mul(local_slot_alpha[lane], 1u128 << bit)
                );
                let raw = cshake256_framed_32(
                    b"QSAG.POLICY.DKG.OT_PAD.V1",
                    &[
                        seed,
                        &domain,
                        &(slot as u64).to_be_bytes(),
                        &[lane as u8, bit as u8],
                    ],
                );
                let pad = policy_pair(raw)[0];
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
        let mut ot = IdealPolicyOt { peers: Vec::new() };
        for id in all_ids {
            let (state, messages) =
                PolicyGuardDkgRound1::new(id, &all_ids, [20; 32], [id as u8; 32]).unwrap();
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
                for slot in 0..BDOZ_PREPROC_SLOTS {
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
                let mut ot = IdealPolicyOt { peers: Vec::new() };
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
                g.advance_velocity_window(&WindowAdvanceAuthorization::new(&[43; 32], &[42; 32], 0, 0)).err(),
                Some(PolicyViolation::WindowIdMismatch)
            );
            g.advance_velocity_window(&WindowAdvanceAuthorization::new(&[43; 32], &[42; 32], 0, 1)).unwrap();
            assert_eq!(g.current_window_id(), 1);
            assert_eq!(g.accumulated_window_spend(), 0);
            assert_eq!(
                g.advance_velocity_window(&WindowAdvanceAuthorization::new(&[43; 32], &[42; 32], 0, 1)).err(),
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
        assert_eq!(shared_ledger.restore_from_durable_checkpoint(&old_checkpoint, &[77; 32], 0),
            Err(PolicyGuardError::Rollback));
        let mut recovered = SharedWindowSpendLedger::new(&policy, 0);
        assert_eq!(recovered.restore_from_durable_checkpoint(&old_checkpoint, &[77; 32], generation),
            Err(PolicyGuardError::Rollback));
        let mut tampered = saved.clone();
        tampered[40] ^= 1;
        assert_eq!(recovered.restore_from_durable_checkpoint(&tampered, &[77; 32], generation),
            Err(PolicyGuardError::AuthenticationFailed));
        recovered.restore_from_durable_checkpoint(&saved, &[77; 32], generation).unwrap();
        assert_eq!(recovered.accumulated_window_spend(), 60);
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
        assert_eq!(evaluate_policy_committed_barrier_with_ledger(
            &policy, &q2_intent, q2_intent.session_id, q2_intent.timestamp_secs,
            &mut committee[2..4], &mut shared_ledger,
            |_, _| Err(PolicyViolation::LedgerPersistenceFailed), &accel).unwrap_err(),
            PolicyViolation::LedgerPersistenceFailed);
        assert!(shared_ledger.failed);
        q2_intent.nonce = [0xE5; 32];
        q2_intent.session_id = [0xF5; 32];
        assert_eq!(evaluate_policy_committed_barrier_with_ledger(
            &policy, &q2_intent, q2_intent.session_id, q2_intent.timestamp_secs,
            &mut committee[2..4], &mut shared_ledger, |_, _| Ok(()), &accel).unwrap_err(),
            PolicyViolation::LedgerPersistenceFailed);

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
            assert!(guards.iter().all(|g| g.next_slot.get() == 0 && !g.is_poisoned()));
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
