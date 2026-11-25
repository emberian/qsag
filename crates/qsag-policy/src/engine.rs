use super::*;

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
pub struct TransactionIntentBuilder(pub(crate) TransactionIntent);
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
        /// The audience's one consumption domain; see [`SealConsumptionDomain`].
        domain: &'a mut dyn SealConsumptionDomain,
    },
}

impl CapabilityRequest {
    /// Derive trusted [`CapabilityRequest`] facts directly from `(policy, intent, now, actions)`:
    /// - `intent_digest = intent.canonical_digest()` (the release-token binding)
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
            intent_digest: intent.canonical_digest(),
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
        capability: &mut CapabilityGate<'_>,
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
                domain,
            } => token.verify(authority_pk, dp, &req, *domain),
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
        capability: Option<&mut CapabilityGate<'_>>,
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
