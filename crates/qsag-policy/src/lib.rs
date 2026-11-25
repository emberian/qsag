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
pub mod seal_store;

mod barrier;
mod dkg;
mod engine;
mod guard;
mod ledger;
pub mod ot;
mod party;
pub use barrier::*;
pub use biscuit::{
    MAX_AUTHORITY_TREE_HEIGHT, MAX_BISCUIT_HOPS, PQ_BISCUIT_HOP_CRYPTO_BYTES, PqBiscuit,
    PqBiscuitAuthorityKey, PqBiscuitAuthorityPublicKey, PqBiscuitHopBlock, PqBiscuitSeal,
    PqBiscuitStepKey, capability_request_digest,
};
pub use dkg::*;
pub use durable::PolicyGuardError;
#[cfg(feature = "std")]
pub use durable::{FsPolicyDurableLedger, FsPolicyGenerationFence};
pub use engine::*;
pub use guard::*;
pub use ledger::*;
pub use macaroon::{
    CapabilityError, CapabilityRequest, Caveat, Discharge, MacaroonVerifier, SpongeMacaroon,
};
pub use party::*;
pub use qsag_addr::policy_signing_key_id;
#[cfg(feature = "std")]
pub use seal_store::{AnchoredSnapshot, FsSealConsumptionStore};
pub use seal_store::{MemorySealConsumptionStore, SealConsumptionDomain};

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
    /// `u128::MAX` leaves the window uncapped apart from `u128` overflow. It grants no
    /// exemption from cross-quorum accounting: a quorum that is neither the full committee
    /// nor contains `hardware_guardian_party` still needs a [`SharedWindowSpendLedger`].
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
    /// `approver_parties` is longer than `u16::MAX`, the largest count a tier can require.
    ApproverCountOutOfRange,
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
    ///
    /// The approver list is attacker-supplied, so its length is bounded before anything is
    /// scanned and every later step is linear in it.
    pub fn evaluate(&self, intent: &TransactionIntent) -> Result<(), PolicyViolation> {
        let approver_count = u16::try_from(intent.approver_parties.len())
            .map_err(|_| PolicyViolation::ApproverCountOutOfRange)?;
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

        // Distinct approvers and the anti-self-approval rule, in one pass each over a bitset
        // of the `u16` party-id space. The reverse pass leaves in `first_duplicate` the
        // lowest index whose party appears again later, so the violation reported is that of
        // the earliest offending approver, self-approval first when both name the same one.
        let mut later = [0u64; 1024];
        let mut first_duplicate = None;
        for (index, &party) in intent.approver_parties.iter().enumerate().rev() {
            let word = &mut later[usize::from(party >> 6)];
            let bit = 1u64 << (party & 63);
            if *word & bit != 0 {
                first_duplicate = Some(index);
            }
            *word |= bit;
        }
        let first_self_approval = if self.forbid_initiator_self_approval {
            intent
                .approver_parties
                .iter()
                .position(|&party| party == intent.initiator_party)
        } else {
            None
        };
        match (first_self_approval, first_duplicate) {
            (Some(own), Some(duplicate)) if duplicate < own => {
                return Err(PolicyViolation::DuplicateApproverInQuorum);
            }
            (Some(_), _) => return Err(PolicyViolation::InitiatorSelfApprovalForbidden),
            (None, Some(_)) => return Err(PolicyViolation::DuplicateApproverInQuorum),
            (None, None) => {}
        }

        // The first tier covering the amount; `validate_quorum_tiers` makes it the only
        // candidate and the weakest quorum any amount this large can select.
        let matched_tier = self
            .quorum_tiers
            .iter()
            .find(|t| intent.amount_units <= t.max_amount_units)
            .ok_or(PolicyViolation::NoMatchingQuorumTier)?;

        if approver_count < matched_tier.min_approvers {
            return Err(PolicyViolation::InsufficientTierApprovers {
                have: approver_count,
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

#[cfg(test)]
mod tests;

#[cfg(test)]
mod cleanup_tests;
