//! Challenge-bound registered bearer capabilities. Each proof uses fresh, secret holder coins.
use super::*;
pub use qsag_cred::presentation_challenge::VerifierChallengeLedger;
use qsag_cred::presentation_challenge::{ChallengeError, PresentationChallenges};

/// Verifier-selected facts shared by every candidate in the anonymity set.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnlinkableCapabilityStatement {
    pub issuer_root: Digest,
    pub revocation_root: Digest,
    pub revocation_epoch: u64,
    pub request: CapabilityRequest,
}

impl UnlinkableCapabilityStatement {
    fn batch(&self) -> CapabilityBatchStatement {
        CapabilityBatchStatement {
            issuer_root: self.issuer_root,
            revocation_root: self.revocation_root,
            revocation_epoch: self.revocation_epoch,
            request: self.request,
            presentation_tags: Vec::new(),
        }
    }
}

/// The verifier supplies its own identity, service scope and expected nonce.
#[derive(Clone, Copy)]
pub struct CapabilityChallenge<'a> {
    pub verifier_id: &'a [u8],
    pub scope: &'a [u8],
    pub nonce: [u8; 32],
}

impl<'a> CapabilityChallenge<'a> {
    fn domain(verifier_id: &[u8], scope: &[u8]) -> Vec<u8> {
        let mut out = b"QSAG.CAPABILITY.UNLINKABLE/v1".to_vec();
        for field in [verifier_id, scope] {
            out.extend_from_slice(&(field.len() as u64).to_le_bytes());
            out.extend_from_slice(field);
        }
        out
    }

    pub fn issue(
        ledger: &mut VerifierChallengeLedger,
        verifier_id: &'a [u8],
        scope: &'a [u8],
        now: u64,
        ttl: u64,
        entropy: [u8; 32],
    ) -> Result<Self, ChallengeError> {
        let nonce = ledger.issue(&Self::domain(verifier_id, scope), now, ttl, entropy)?;
        Ok(Self {
            verifier_id,
            scope,
            nonce,
        })
    }

    fn context(&self) -> Vec<u8> {
        let mut out = Self::domain(self.verifier_id, self.scope);
        out.extend_from_slice(&self.nonce);
        out
    }
}

/// Only a v2 proof is sent. The verifier already knows the statement and challenge.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnlinkableCapabilityPresentation(ZkHemV2Proof);

impl UnlinkableCapabilityPresentation {
    const MAGIC: &[u8; 8] = b"QSAGCAU1";

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Self::MAGIC.to_vec();
        out.extend(self.0.to_bytes());
        out
    }

    pub fn from_bytes(
        bytes: &[u8],
        relation: &UnlinkableCapabilityRelation,
        profile: Profile,
    ) -> Option<Self> {
        let inner = bytes.strip_prefix(Self::MAGIC)?;
        let proof = ZkHemV2Proof::from_bytes(inner, relation.0.shape())?;
        (proof.profile == profile).then_some(Self(proof))
    }
}

/// Enrollment, caveats, non-revocation and batch distinctness with no public nullifier.
pub struct UnlinkableCapabilityRelation(CapabilityRelation);

impl UnlinkableCapabilityRelation {
    pub fn new(params: CapabilityParams) -> Result<Self, CapabilityZkError> {
        Ok(Self(CapabilityRelation::compile(params, false)?))
    }

    /// Supply a fresh uniform secret seed on every invocation, including retries.
    /// Inputs must be sorted by token ID, as for the scoped relation.
    pub fn prove(
        &self,
        statement: &UnlinkableCapabilityStatement,
        inputs: &[CapabilityPresentationInput],
        challenge: CapabilityChallenge<'_>,
        profile: Profile,
        seed: &[u8; 32],
    ) -> Result<UnlinkableCapabilityPresentation, CapabilityZkError> {
        let proof = self.0.prove(
            &statement.batch(),
            inputs,
            &challenge.context(),
            profile,
            seed,
        )?;
        Ok(UnlinkableCapabilityPresentation(proof.proof))
    }

    /// Accept once, after authenticating the proof against the verifier's expected facts.
    pub fn verify(
        &self,
        statement: &UnlinkableCapabilityStatement,
        challenge: CapabilityChallenge<'_>,
        profile: Profile,
        presentation: &UnlinkableCapabilityPresentation,
        ledger: &mut VerifierChallengeLedger,
        now: u64,
    ) -> bool {
        let context = challenge.context();
        v2::verify(
            self.0.shape(),
            &public_inputs_vec(&statement.batch(), &context),
            &self.0.statement_bytes(&context),
            profile,
            &presentation.0,
        ) && ledger
            .at(now)
            .consume(
                &CapabilityChallenge::domain(challenge.verifier_id, challenge.scope),
                &challenge.nonce,
            )
            .is_ok()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn candidate_capabilities_and_one_time_acceptance() {
        let params = CapabilityParams {
            batch_size: 1,
            max_hops: 1,
            issuer_depth: 1,
            revocation_depth: 1,
        };
        let caps = [11, 23].map(|id| {
            let mut cap = BearerCapability::issue(&[f(7); 4], [f(id); 4], [f(9); 4]).unwrap();
            cap.attenuate(CapCaveat::MaxAmount(5)).unwrap();
            cap
        });
        let directory =
            CapabilityIssuerDirectory::new(1, &caps.each_ref().map(BearerCapability::mint_leaf))
                .unwrap();
        let rev = SortedRevocationTree::new(1, 3, &[]).unwrap();
        let statement = UnlinkableCapabilityStatement {
            issuer_root: directory.root(),
            revocation_root: rev.root(),
            revocation_epoch: rev.epoch(),
            request: CapabilityRequest {
                audience: [f(9); 4],
                resource: [f(4); 4],
                actions: 1,
                amount: 3,
                now: 1,
            },
        };
        let inputs: Vec<_> = caps
            .into_iter()
            .enumerate()
            .map(|(i, cap)| CapabilityPresentationInput {
                issuer_index: i,
                issuer_siblings: directory.opening(i).unwrap(),
                non_membership: rev.prove_non_membership(cap.token_id()).unwrap(),
                capability: cap,
            })
            .collect();
        let profile = Profile::TurboShakeJohnson400;
        let relation = UnlinkableCapabilityRelation::new(params).unwrap();
        let mut ledger = VerifierChallengeLedger::new(3);
        let mut roots = Vec::new();
        for (round, source) in [0, 0, 1].into_iter().enumerate() {
            let challenge =
                CapabilityChallenge::issue(&mut ledger, b"bank", b"read", 1, 6, [round as u8; 32])
                    .unwrap();
            let context = challenge.context();
            let scoped = CapabilityBatchStatement::prepare_sorted(
                directory.root(),
                rev.root(),
                rev.epoch(),
                statement.request,
                &mut [inputs[source].clone()],
                &context,
            )
            .unwrap();
            // Positive control: the publicly visible scoped tag identifies the actual candidate.
            assert_eq!(
                inputs
                    .iter()
                    .map(|i| i.capability.presentation_tag(&context) == scoped.presentation_tags[0])
                    .collect::<Vec<_>>(),
                [source == 0, source == 1]
            );
            let proof = relation
                .prove(
                    &statement,
                    core::slice::from_ref(&inputs[source]),
                    challenge,
                    profile,
                    &[19 + round as u8; 32],
                )
                .unwrap();
            let proof =
                UnlinkableCapabilityPresentation::from_bytes(&proof.to_bytes(), &relation, profile)
                    .unwrap();
            assert!(!roots.contains(&proof.0.root));
            roots.push(proof.0.root);
            for candidate in &inputs {
                let batch = statement.batch();
                let slots = relation
                    .0
                    .validate_and_build_slots(&batch, core::slice::from_ref(candidate), &context)
                    .unwrap();
                let mut cs = ConstraintSystem::witness_only();
                populate(&mut cs, params, &batch, &context, &slots);
                let mut z = cs.finish_assignment(relation.0.shape()).unwrap();
                assert!(!v2::candidate_matches_masked_evaluation(
                    relation.0.shape(),
                    profile,
                    &public_inputs_vec(&batch, &context),
                    &relation.0.statement_bytes(&context),
                    &proof.0,
                    &z
                ));
                qsag_asm::volatile_fill(&mut z, F::ZERO);
            }

            for wrong in [
                CapabilityChallenge {
                    verifier_id: b"other",
                    ..challenge
                },
                CapabilityChallenge {
                    scope: b"write",
                    ..challenge
                },
                CapabilityChallenge {
                    nonce: [0; 32],
                    ..challenge
                },
            ] {
                assert!(!relation.verify(&statement, wrong, profile, &proof, &mut ledger, 1));
            }
            assert_eq!(ledger.outstanding(), 1);
            assert!(relation.verify(&statement, challenge, profile, &proof, &mut ledger, 1));
            assert!(!relation.verify(&statement, challenge, profile, &proof, &mut ledger, 1));
        }

        // Strip the caveat and repair the private chain endpoint. The enrolled leaf changes.
        let mut stripped = inputs[0].clone();
        stripped.capability.caveats.clear();
        stripped.capability.final_tag = stripped.capability.root_tag;
        assert!(
            stripped
                .capability
                .verify_native(&statement.request)
                .is_ok()
        );
        let challenge =
            CapabilityChallenge::issue(&mut ledger, b"bank", b"read", 1, 6, [7; 32]).unwrap();
        assert_eq!(
            relation.prove(
                &statement,
                core::slice::from_ref(&stripped),
                challenge,
                profile,
                &[17; 32]
            ),
            Err(CapabilityZkError::InvalidIssuerOpening)
        );
        let mut cs = ConstraintSystem::witness_only();
        populate(
            &mut cs,
            params,
            &statement.batch(),
            &challenge.context(),
            &[CapSlot::from_input(params, &stripped).unwrap()],
        );
        let mut z = cs.finish_assignment(relation.0.shape()).unwrap();
        assert!(!relation.0.shape().is_satisfied(&z));
        qsag_asm::volatile_fill(&mut z, F::ZERO);
    }
}
