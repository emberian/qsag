module
public import Qsag.SeparatedCustodyRelease
public import Qsag.RssProductionProfile
import all Qsag.SeparatedCustodyPolicy
import all Qsag.CompleteMediationBoundary
import all Qsag.SeparatedCustodyCore
import all Qsag.RssProductionProfile
import Qsag.Tactic.AssuranceKit

/-! Contextual approval is an explicit participant input. Initiator authentication
continues to authorize the underlying transaction; the participant additionally
approves the complete signing request and fixed enrolled profile. This is not an
interpretation of old transaction-only certificates as contextual approval. -/
public section
namespace Qsag.Custody.RequestPolicy
set_option autoImplicit false
set_option maxRecDepth 4096

structure Input where
  request : SessionScheduleReq
  transaction : TransactionIntent
  tags : List InitiatorPeerTag
  timestamp : Nat
  round : Nat
  openings : List RoundOpening

def consistent (a : Input) : Bool :=
  decide (a.request.msg = toCanonicalSigningBytes a.transaction ∧
    a.request.sessionId = ofLE a.transaction.session_id.reverse)

/-- Every variable in the production request, including its intended approver
roster and optional randomness, is covered by the actual approval signature. -/
def intent (profile : RssProduction.Profile) (a : Input) : Intent :=
  ⟨a.request.sessionId, a.round, a.request.reqEpoch, a.transaction.amount_units,
    RssProduction.payload profile a.request⟩

def reserve (profile : RssProduction.Profile) (p : RoundPolicy) (cap anchor : Nat)
    (st : PolicyVault) (a : Input) : PolicyVault :=
  if consistent a then
    match authenticatedPolicyGuardStep st.policy a.transaction a.tags a.timestamp with
    | .accepted policy' _ =>
      let r := intent profile a
      ⟨policy', mint p cap anchor (forget st.vault) ⟨r, roundCommitment r, a.openings⟩⟩
    | .rejected _ _ => ⟨st.policy, forget st.vault⟩
  else ⟨st.policy, forget st.vault⟩

def execute (profile : RssProduction.Profile) (cfg : SigningConfig) (sk : PqSecretKey)
    (p : RoundPolicy) (cap anchor : Nat) (st : PolicyVault) (a : Input) :
    PolicyVault × Option Certificate :=
  let v := reserve profile p cap anchor st a
  let result := release cfg sk st.policy.party v.vault.durable.anchor v.vault (intent profile a)
  (⟨v.policy, result.1⟩, result.2)

theorem reserve_safe (profile : RssProduction.Profile) (p : RoundPolicy) (cap anchor : Nat)
    (st : PolicyVault) (a : Input) (h : Safe p cap st.vault) :
    Safe p cap (reserve profile p cap anchor st a).vault := by
  unfold reserve
  split
  · split
    · exact mint_safe p cap anchor (forget st.vault) _ (forget_safe p cap st.vault h)
    · exact forget_safe p cap st.vault h
  · exact forget_safe p cap st.vault h

theorem execute_safe (profile : RssProduction.Profile) (cfg : SigningConfig) (sk : PqSecretKey)
    (p : RoundPolicy) (cap anchor : Nat) (st : PolicyVault) (a : Input)
    (h : Safe p cap st.vault) :
    Safe p cap (execute profile cfg sk p cap anchor st a).1.vault :=
  release_safe cfg sk st.policy.party _ p cap _ _ (reserve_safe profile p cap anchor st a h)

theorem reserve_admitted (profile : RssProduction.Profile) (p : RoundPolicy) (cap anchor : Nat)
    (st : PolicyVault) (a : Input) (r : Intent)
    (h : (reserve profile p cap anchor st a).vault.active = some r) :
    consistent a = true ∧
    policyCheckAdmission st.policy a.transaction a.tags a.timestamp = true ∧
    r = intent profile a ∧ checkRound p r (roundCommitment r) a.openings = true := by
  by_cases hc : consistent a = true
  · by_cases ha : policyCheckAdmission st.policy a.transaction a.tags a.timestamp = true
    · simp only [reserve, hc, authenticatedPolicyGuardStep, ha, ↓reduceIte] at h
      obtain ⟨hg, he⟩ := mint_granted p cap anchor (forget st.vault)
        ⟨intent profile a, roundCommitment (intent profile a), a.openings⟩ r rfl h
      change intent profile a = r at he
      refine ⟨hc, ha, he.symm, ?_⟩
      rw [← he]
      exact (Bool.and_eq_true_iff.mp hg).2
    · simp only [reserve, hc, authenticatedPolicyGuardStep, ha, ↓reduceIte] at h
      cases h
  · simp only [reserve, hc] at h
    cases h

theorem reserve_attempted (profile : RssProduction.Profile) (p : RoundPolicy) (cap anchor : Nat)
    (st : PolicyVault) (a : Input) :
    (reserve profile p cap anchor st a).vault.attempted = st.vault.attempted := by
  unfold reserve
  split
  · split
    · exact mint_attempted p cap anchor (forget st.vault) _
    · rfl
  · rfl

theorem reserve_party (profile : RssProduction.Profile) (p : RoundPolicy) (cap anchor : Nat)
    (st : PolicyVault) (a : Input) :
    (reserve profile p cap anchor st a).policy.party = st.policy.party := by
  by_cases hc : consistent a = true <;>
    by_cases ha : policyCheckAdmission st.policy a.transaction a.tags a.timestamp = true <;>
    simp only [reserve, hc, authenticatedPolicyGuardStep, ha, Bool.false_eq_true, ↓reduceIte]

theorem execute_party (profile : RssProduction.Profile) (cfg : SigningConfig) (sk : PqSecretKey)
    (p : RoundPolicy) (cap anchor : Nat) (st : PolicyVault) (a : Input) :
    (execute profile cfg sk p cap anchor st a).1.policy.party = st.policy.party :=
  reserve_party profile p cap anchor st a

/-- The certificate is produced by the actual partial production signer after
policy admission and durable burn, and binds precisely the participant input. -/
theorem execute_sound (profile : RssProduction.Profile) (cfg : SigningConfig) (sk : PqSecretKey)
    (p : RoundPolicy) (cap anchor : Nat) (st : PolicyVault) (a : Input) (c : Certificate)
    (h : (execute profile cfg sk p cap anchor st a).2 = some c) :
    c.party = st.policy.party ∧ c.intent = intent profile a ∧
    consistent a = true ∧
    policyCheckAdmission st.policy a.transaction a.tags a.timestamp = true ∧
    verify cfg (derivePublicKey cfg.suite cfg.params sk) c.party c.intent c.signature = true := by
  have ho := release_output cfg sk st.policy.party _ _ (intent profile a) c h
  have hv := release_verifies cfg sk st.policy.party _ _ (intent profile a) c h
  have hg : (reserve profile p cap anchor st a).vault.active = some (intent profile a) := by
    change (release cfg sk st.policy.party _ (reserve profile p cap anchor st a).vault (intent profile a)).2 = some c at h
    unfold release at h
    split at h
    · cases h
    · split at h
      next ha => exact ha
      next => cases h
  have ha := reserve_admitted profile p cap anchor st a _ hg
  exact ⟨ho.1, ho.2.1, ha.1, ha.2.1, hv⟩

/-- Context equality is derived from the certificate's complete signed intent;
no provenance or byte-agreement premise is provided by the scheduler. -/
theorem same_intent_same_request (profile other : RssProduction.Profile) (a b : Input)
    (h : intent profile a = intent other b) :
    a.request = b.request ∧ RssProduction.enrolledKey profile = RssProduction.enrolledKey other ∧
    profile.params = other.params ∧ profile.context = other.context ∧
    profile.grindLimit = other.grindLimit := by
  have hm : RssProduction.payload profile a.request = RssProduction.payload other b.request :=
    congrArg Intent.message h
  exact ⟨RssProduction.payload_request_binding hm, RssProduction.payload_enrollment_binding hm,
    RssProduction.payload_profile_binding hm⟩

theorem execute_attempt_origin (profile : RssProduction.Profile) (cfg : SigningConfig)
    (sk : PqSecretKey) (p : RoundPolicy) (cap anchor : Nat) (st : PolicyVault) (a : Input)
    (r : Intent) (hm : r ∈ (execute profile cfg sk p cap anchor st a).1.vault.attempted) :
    r ∈ st.vault.attempted ∨
      (consistent a = true ∧
       policyCheckAdmission st.policy a.transaction a.tags a.timestamp = true ∧
       r = intent profile a ∧
       (execute profile cfg sk p cap anchor st a).2 =
         (sign cfg sk st.policy.party r).map (fun sig => ⟨st.policy.party, r, sig⟩)) := by
  let v := reserve profile p cap anchor st a
  have he : v.vault.attempted = st.vault.attempted := reserve_attempted profile p cap anchor st a
  change r ∈ (release cfg sk st.policy.party v.vault.durable.anchor v.vault (intent profile a)).1.attempted at hm
  change _ ∨ (_ ∧ _ ∧ _ ∧ (release cfg sk st.policy.party v.vault.durable.anchor v.vault (intent profile a)).2 = _)
  unfold release at hm ⊢
  split at hm
  next hp => exact .inl (he ▸ hm)
  next hp =>
    split at hm
    next hg =>
      rcases List.mem_cons.mp hm with hr | hold
      · have ha := reserve_admitted profile p cap anchor st a _ hg
        exact .inr ⟨ha.1, ha.2.1, hr, by simp only [hp, hg, Bool.false_eq_true, ↓reduceIte, hr]⟩
      · exact .inl (he ▸ hold)
    next hg => exact .inl (he ▸ hm)

end Qsag.Custody.RequestPolicy
end
#verify_constructive Qsag.Custody.RequestPolicy.execute_sound
#verify_constructive Qsag.Custody.RequestPolicy.execute_safe
#verify_constructive Qsag.Custody.RequestPolicy.same_intent_same_request
#verify_constructive Qsag.Custody.RequestPolicy.execute_attempt_origin
