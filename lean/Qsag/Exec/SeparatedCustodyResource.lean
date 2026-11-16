module
public import Qsag.Custody.SeparatedCustody
public import Qsag.Exec.RssProductionProfile
public import Qsag.Exec.SeparatedCustodyUc
public import Qsag.Exec.ThresholdIdealService
import all Qsag.Custody.SeparatedCustody
import all Qsag.Exec.RssProductionProfile
import all Qsag.Protocol.Signing.HypertreeEufCma
import all Qsag.Exec.SeparatedCustodyUc
import all Qsag.Exec.ThresholdIdealService
import all Qsag.Protocol.Threshold.ThresholdApproval
import Qsag.Tactic.AssuranceKit

/-! Execution-level module (`Exec/`): the request policy below is stated over the RSS production
profile, the UC engine's `SessionScheduleReq` and the threshold ideal service.

Contextual approval is an explicit participant input. Initiator authentication
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
      ⟨policy', mint p cap anchor (forget st.vault)
        ⟨r, roundCommitment st.vault.identity.deploymentId r, a.openings⟩⟩
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

theorem reserve_identity (profile : RssProduction.Profile) (p : RoundPolicy) (cap anchor : Nat)
    (st : PolicyVault) (a : Input) :
    (reserve profile p cap anchor st a).vault.identity = st.vault.identity := by
  unfold reserve
  split
  · split
    · exact mint_identity p cap anchor (forget st.vault) _
    · rfl
  · rfl

theorem execute_identity (profile : RssProduction.Profile) (cfg : SigningConfig)
    (sk : PqSecretKey) (p : RoundPolicy) (cap anchor : Nat) (st : PolicyVault) (a : Input) :
    (execute profile cfg sk p cap anchor st a).1.vault.identity = st.vault.identity :=
  (release_identity cfg sk st.policy.party _ _ _).trans (reserve_identity profile p cap anchor st a)

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
    r = intent profile a ∧
    checkRound p st.vault.identity.deploymentId r
      (roundCommitment st.vault.identity.deploymentId r) a.openings = true := by
  by_cases hc : consistent a = true
  · by_cases ha : policyCheckAdmission st.policy a.transaction a.tags a.timestamp = true
    · simp only [reserve, hc, authenticatedPolicyGuardStep_eq, ha, ↓reduceIte] at h
      obtain ⟨hg, he⟩ := mint_granted p cap anchor (forget st.vault)
        ⟨intent profile a, roundCommitment st.vault.identity.deploymentId (intent profile a),
          a.openings⟩ r rfl h
      change intent profile a = r at he
      refine ⟨hc, ha, he.symm, ?_⟩
      rw [← he]
      exact (Bool.and_eq_true_iff.mp hg).2
    · simp only [reserve, hc, authenticatedPolicyGuardStep_eq, ha, ↓reduceIte] at h
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
    simp only [reserve, hc, authenticatedPolicyGuardStep_eq, ha, Bool.false_eq_true, ↓reduceIte]

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
    verify cfg (derivePublicKey cfg.suite cfg.params sk) st.vault.identity.deploymentId
      c.party c.intent c.signature = true := by
  have ho := release_output cfg sk st.policy.party _ _ (intent profile a) c h
  have hv := release_verifies cfg sk st.policy.party _ _ (intent profile a) c h
  rw [reserve_identity] at hv
  have hg : (reserve profile p cap anchor st a).vault.active = some (intent profile a) :=
    release_some_active cfg sk st.policy.party _ _ (intent profile a) c h
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
         issue cfg sk st.policy.party st.vault.identity r) := by
  let v := reserve profile p cap anchor st a
  have he : v.vault.attempted = st.vault.attempted := reserve_attempted profile p cap anchor st a
  have hident : v.vault.identity = st.vault.identity := reserve_identity profile p cap anchor st a
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
        exact .inr ⟨ha.1, ha.2.1, hr,
          by simp only [hp, hg, Bool.false_eq_true, ↓reduceIte, hr, hident]⟩
      · exact .inl (he ▸ hold)
    next hg => exact .inl (he ▸ hm)

end Qsag.Custody.RequestPolicy
end
#verify_constructive Qsag.Custody.RequestPolicy.execute_sound
#verify_constructive Qsag.Custody.RequestPolicy.execute_safe
#verify_constructive Qsag.Custody.RequestPolicy.same_intent_same_request
#verify_constructive Qsag.Custody.RequestPolicy.execute_attempt_origin

public section
namespace Qsag.Custody.RequestPolicy
set_option autoImplicit false
set_option maxRecDepth 4096
structure InputRecord where
  party : Nat
  before : AuthenticatedPolicyState
  invocation : Input
  output : Option Certificate

structure HistoryState where
  parties : Nat → PolicyVault
  calls : List InputRecord := []
  shared : SharedHistory

def historyInitial (d : Deployment) : HistoryState :=
  ⟨fun i => ⟨{ d.policies i with party := i }, initial (vaultIdentity d i)⟩, [],
    ⟨{ capacity := d.capacity }, []⟩⟩

def replaceParty (parties : Nat → PolicyVault) (i : Nat) (v : PolicyVault) : Nat → PolicyVault :=
  fun j => if j = i then v else parties j

def invoke (profile : RssProduction.Profile) (d : Deployment) (s : HistoryState) (i anchor : Nat) (a : Input) : HistoryState :=
  let result := execute profile d.signer (d.keys i) (d.rounds i) (d.caps i) anchor
    (s.parties i) a
  ⟨replaceParty s.parties i result.1,
    ⟨i, (s.parties i).policy, a, result.2⟩ :: s.calls, s.shared⟩

inductive HistoryCommand where
  | invoke (party anchor : Nat) (invocation : Input)
  | forget (party : Nat)
  | submit (intent : Intent) (certificates : List Certificate)

def historyStep (profile : RssProduction.Profile) (d : Deployment) (s : HistoryState) : HistoryCommand → HistoryState
  | .invoke i anchor a => invoke profile d s i anchor a
  | .forget i =>
    let cleared : PolicyVault := ⟨(s.parties i).policy, forget (s.parties i).vault⟩
    { s with parties := replaceParty s.parties i cleared }
  | .submit r cs => { s with shared := (submitRecorded d s.shared r cs).1 }

def historyRun (profile : RssProduction.Profile) (d : Deployment) : HistoryState → List HistoryCommand → HistoryState
  | s, [] => s
  | s, c :: cs => historyRun profile d (historyStep profile d s c) cs

/-- This invariant is proved from the initial state and executed commands.
It is never an input to the exported generated-history provenance theorem. -/
structure Generated (profile : RssProduction.Profile) (d : Deployment) (s : HistoryState) : Prop where
  safe : ∀ i, Safe (d.rounds i) (d.caps i) (s.parties i).vault
  identities : ∀ i, (s.parties i).policy.party = i
  vaultIdentities : ∀ i, (s.parties i).vault.identity = vaultIdentity d i
  origin : ∀ i r, r ∈ (s.parties i).vault.attempted →
    ∃ e ∈ s.calls, e.party = i ∧ e.before.party = i ∧
      policyCheckAdmission e.before e.invocation.transaction e.invocation.tags e.invocation.timestamp = true ∧
      intent profile e.invocation = r ∧
      e.output = (sign d.signer (d.keys i) d.deploymentId i r).map (fun sig => ⟨i, r, sig⟩)
  shared : SharedSafe d.capacity s.shared

theorem historyInitial_generated (profile : RssProduction.Profile) (d : Deployment) : Generated profile d (historyInitial d) := by
  refine ⟨(fun i => initial_safe (d.rounds i) (d.caps i) _), (fun _ => rfl), (fun _ => rfl), ?_, ?_⟩
  · intro i r hm; cases hm
  · exact ⟨rfl, rfl, rfl, .nil, Nat.zero_le _⟩

theorem invoke_generated (profile : RssProduction.Profile) (d : Deployment) (s : HistoryState) (i anchor : Nat) (a : Input)
    (h : Generated profile d s) : Generated profile d (invoke profile d s i anchor a) := by
  constructor
  · intro j
    unfold invoke replaceParty
    dsimp only
    split
    next he =>
      subst j
      exact execute_safe profile d.signer (d.keys i) (d.rounds i) (d.caps i) anchor
        (s.parties i) a (h.safe i)
    next => exact h.safe j
  · intro j
    unfold invoke replaceParty
    dsimp only
    split
    next he =>
      subst j
      exact (execute_party profile d.signer (d.keys i) (d.rounds i) (d.caps i) anchor
        (s.parties i) a).trans (h.identities i)
    next => exact h.identities j
  · intro j
    unfold invoke replaceParty
    dsimp only
    split
    next he =>
      subst j
      exact (execute_identity profile d.signer (d.keys i) (d.rounds i) (d.caps i) anchor
        (s.parties i) a).trans (h.vaultIdentities i)
    next => exact h.vaultIdentities j
  · intro j r hm
    unfold invoke replaceParty at hm ⊢
    dsimp only at hm ⊢
    split at hm
    next he =>
      subst j
      rcases execute_attempt_origin profile d.signer (d.keys i) (d.rounds i) (d.caps i) anchor
        (s.parties i) a r hm with hold | hnew
      · obtain ⟨e, he, rest⟩ := h.origin i r hold
        exact ⟨e, List.mem_cons_of_mem _ he, rest⟩
      · obtain ⟨_hc, ha, hr, ho⟩ := hnew
        refine ⟨_, List.mem_cons_self, rfl, h.identities i, ha, hr.symm, ?_⟩
        rw [h.identities i, h.vaultIdentities i, issue_vaultIdentity] at ho
        exact ho
    next =>
      obtain ⟨e, he, rest⟩ := h.origin j r hm
      exact ⟨e, List.mem_cons_of_mem _ he, rest⟩
  · exact h.shared

theorem historyStep_generated (profile : RssProduction.Profile) (d : Deployment) (s : HistoryState) (c : HistoryCommand)
    (h : Generated profile d s) : Generated profile d (historyStep profile d s c) := by
  cases c with
  | invoke i anchor a => exact invoke_generated profile d s i anchor a h
  | submit r cs =>
    exact ⟨h.safe, h.identities, h.vaultIdentities, h.origin,
      submitRecorded_safe d s.shared r cs h.shared⟩
  | forget i =>
    constructor
    · intro j
      unfold historyStep replaceParty
      dsimp only
      split
      next he => subst j; exact forget_safe (d.rounds i) (d.caps i) _ (h.safe i)
      next => exact h.safe j
    · intro j
      unfold historyStep replaceParty
      dsimp only
      split
      next he => subst j; exact h.identities i
      next => exact h.identities j
    · intro j
      unfold historyStep replaceParty
      dsimp only
      split
      next he => subst j; exact h.vaultIdentities i
      next => exact h.vaultIdentities j
    · intro j r hm
      unfold historyStep replaceParty at hm ⊢
      dsimp only at hm ⊢
      split at hm
      next he => subst j; exact h.origin i r hm
      next => exact h.origin j r hm
    · exact h.shared

theorem historyRun_generated (profile : RssProduction.Profile) (d : Deployment) (s : HistoryState) (cs : List HistoryCommand)
    (h : Generated profile d s) : Generated profile d (historyRun profile d s cs) := by
  induction cs generalizing s with
  | nil => exact h
  | cons c cs ih => exact ih _ (historyStep_generated profile d s c h)

def generatedHistory (profile : RssProduction.Profile) (d : Deployment) (cs : List HistoryCommand) : HistoryState :=
  historyRun profile d (historyInitial d) cs

theorem generatedHistory_valid (profile : RssProduction.Profile) (d : Deployment) (cs : List HistoryCommand) :
    Generated profile d (generatedHistory profile d cs) :=
  historyRun_generated profile d _ cs (historyInitial_generated profile d)

/-- A produced approval is a record of an actual invocation with its actual
successful output, not an authorization predicate supplied to the execution. -/
def ProducedPolicyApproval (profile : RssProduction.Profile) (d : Deployment) (s : HistoryState) (i : Nat) (r : Intent) : Prop :=
  ∃ e ∈ s.calls, e.party = i ∧ e.before.party = i ∧
    policyCheckAdmission e.before e.invocation.transaction e.invocation.tags e.invocation.timestamp = true ∧
    intent profile e.invocation = r ∧
    ∃ issued, e.output = some issued ∧ issued.party = i ∧ issued.intent = r ∧
      verify d.signer (publicKeys d i) d.deploymentId i r issued.signature = true

theorem successful_log_produced (profile : RssProduction.Profile) (d : Deployment) (s : HistoryState) (i : Nat) (r : Intent)
    (h : Generated profile d s) (hst : d.signer.params.statefulJorts = true)
    (hm : payload d.deploymentId i r ∈
      (signingLog d.signer (d.keys i) d.deploymentId i (s.parties i).vault).map Prod.fst) :
    ProducedPolicyApproval profile d s i r := by
  obtain ⟨entry, he, hem⟩ := List.mem_map.mp hm
  obtain ⟨q, hq, hmsg, hsign⟩ := productionSigningLog_generated _ _ _ _ entry he
  obtain ⟨requested, hr, hreq⟩ := List.mem_map.mp hq
  have hp : payload d.deploymentId i requested = payload d.deploymentId i r := by
    simpa only [← hreq, query] using hmsg.symm.trans hem
  have heq := (payload_injective hp).2.2
  subst requested
  subst q
  have hs : sign d.signer (d.keys i) d.deploymentId i r = some entry.2 :=
    (sign_eq_query d.signer (d.keys i) d.deploymentId i r hst).trans hsign
  obtain ⟨e, he, hi, hb, ha, hc, ho⟩ := h.origin i r hr
  refine ⟨e, he, hi, hb, ha, hc, ⟨i, r, entry.2⟩, ?_, rfl, rfl, ?_⟩
  · rw [ho, hs]
    rfl
  · exact sign_verifies d.signer (d.keys i) d.deploymentId i r entry.2 hs

/-- At every generated-history prefix, an accepted quorum has an honest
certificate whose full intent was actually produced by an earlier admitted
policy invocation, or the submitted candidate wins the actual signature game.
The histories and all provenance facts are computed/proved from commands.
In particular a failed signing attempt is not counted as a produced output.
-/
theorem generated_submit_provenance (profile : RssProduction.Profile) (d : Deployment) (commands : List HistoryCommand)
    (corrupt : List Nat) (r : Intent) (cs : List Certificate)
    (hw : d.signer.params.w = 4 ∨ d.signer.params.w = 16)
    (hst : d.signer.params.statefulJorts = true) (hc : corrupt.length < d.threshold)
    (ha : (submitRecorded d (generatedHistory profile d commands).shared r cs).2 = true) :
    ∃ c ∈ cs, c.party ∉ corrupt ∧
      (ProducedPolicyApproval profile d (generatedHistory profile d commands) c.party r ∨
       (prodEufCmaWin d.signer.suite d.signer.params
          ⟨d.keys c.party, queries d.signer d.deploymentId c.party ((generatedHistory profile d commands).parties c.party).vault,
            payload d.deploymentId c.party r, c.signature⟩ = true ∧
        (ProdSmTcrBreak d.signer.suite d.signer.params (d.keys c.party)
           (signingLog d.signer (d.keys c.party) d.deploymentId c.party ((generatedHistory profile d commands).parties c.party).vault) ∨
         ProdPreimageBreak d.signer.suite d.signer.params (d.keys c.party)
           (signingLog d.signer (d.keys c.party) d.deploymentId c.party ((generatedHistory profile d commands).parties c.party).vault)
           (payload d.deploymentId c.party r) c.signature))) := by
  let s := generatedHistory profile d commands
  have hs : Generated profile d s := generatedHistory_valid profile d commands
  rw [submitRecorded_verdict] at ha
  obtain ⟨c, hcm, hch, _, hv⟩ := quorum_has_honest d.signer (publicKeys d)
    d.deploymentId d.numParties d.threshold s.shared.coordinator.consumedSessions corrupt r cs hc
    (submit_accepted _ _ _ _ _ _ _ _ ha).1
  refine ⟨c, hcm, hch, ?_⟩
  by_cases hm : payload d.deploymentId c.party r ∈
      (signingLog d.signer (d.keys c.party) d.deploymentId c.party (s.parties c.party).vault).map Prod.fst
  · exact .inl (successful_log_produced profile d s c.party r hs hst hm)
  · have hf : ∀ e ∈ signingLog d.signer (d.keys c.party) d.deploymentId c.party (s.parties c.party).vault,
        e.1 ≠ payload d.deploymentId c.party r := by
      intro e he heq
      exact hm (List.mem_map.mpr ⟨e, he, heq⟩)
    right
    refine ⟨?_, ?_⟩
    · unfold prodEufCmaWin
      exact Bool.and_eq_true_iff.mpr ⟨hv, decide_eq_true hm⟩
    · exact production_stateful_forgery_break d.signer.suite d.signer.params (d.keys c.party)
        (queries d.signer d.deploymentId c.party (s.parties c.party).vault) (payload d.deploymentId c.party r) c.signature hw hst
        (queries_one_time d.signer d.deploymentId c.party _ _ _ (hs.safe c.party)) hf hv

/-- One shared acceptance trace supplies both the spend sum and the unique
session list, including across changing/disjoint signing quorums. -/
theorem generated_shared_accounting (profile : RssProduction.Profile) (d : Deployment) (commands : List HistoryCommand) :
    let s := (generatedHistory profile d commands).shared
    s.coordinator.spent = (s.accepted.map (fun a => a.intent.spend)).sum ∧
    s.coordinator.consumedSessions = s.accepted.map (fun a => a.intent.session) ∧
    s.coordinator.consumedSessions.Nodup ∧ s.coordinator.spent ≤ d.capacity := by
  have hs := (generatedHistory_valid profile d commands).shared
  exact ⟨hs.accounting, hs.sessions, hs.distinct, hs.budget⟩

theorem generated_burn_accounting (profile : RssProduction.Profile) (d : Deployment) (commands : List HistoryCommand) (i : Nat) :
    let v := ((generatedHistory profile d commands).parties i).vault
    (v.durable.burned.map (fun b => b.intent.spend)).sum ≤ d.caps i ∧
      v.attempted.Nodup := by
  have hs := (generatedHistory_valid profile d commands).safe i
  exact ⟨hs.accounting ▸ hs.budget, hs.attemptedNodup⟩

theorem generated_replay_rejected (profile : RssProduction.Profile) (d : Deployment) (commands : List HistoryCommand)
    (r : Intent) (cs : List Certificate)
    (hm : r.session ∈ ((generatedHistory profile d commands).shared.accepted.map (fun a => a.intent.session))) :
    (submitRecorded d (generatedHistory profile d commands).shared r cs).2 = false := by
  have hs := (generatedHistory_valid profile d commands).shared
  have hmem : r.session ∈ (generatedHistory profile d commands).shared.coordinator.consumedSessions :=
    hs.sessions ▸ hm
  rw [submitRecorded_verdict]
  unfold submit
  rw [quorum_replay_rejected _ _ _ _ _ _ _ _ hmem]
  rfl

/-- Input failure/withholding cannot silently add a shared accepted spend.
Local burns, by contrast, are preserved by the generated-state invariant. -/
theorem invoke_shared_unchanged (profile : RssProduction.Profile) (d : Deployment) (s : HistoryState) (i anchor : Nat) (a : Input) :
    (invoke profile d s i anchor a).shared = s.shared := by
  unfold invoke
  rfl

end Qsag.Custody.RequestPolicy
end
#verify_constructive Qsag.Custody.RequestPolicy.generatedHistory_valid
#verify_constructive Qsag.Custody.RequestPolicy.generated_submit_provenance
#verify_constructive Qsag.Custody.RequestPolicy.generated_shared_accounting
#verify_constructive Qsag.Custody.RequestPolicy.generated_burn_accounting
#verify_constructive Qsag.Custody.RequestPolicy.generated_replay_rejected

/-! Executable authenticated request gate and a generation-commit storage hybrid.
The storage resource provides authenticated, monotone, atomic generation commit.
It models generation reservation before production, not four independent WALs.
Its physical POSIX/anchor implementation remains a separate realization task.
Public wire observations are outside recoverable local state. -/
public section
namespace Qsag.Custody.RequestPolicy
set_option autoImplicit false
set_option maxRecDepth 4096

def gate (profile : RssProduction.Profile) (d : Deployment) (corrupt : List Nat)
    (s : HistoryState) (a : Input) (cs : List Certificate) : Bool :=
  decide (a.request.honestApprovers = custodyQuorumHonestApprovers corrupt cs) &&
    (submitRecorded d s.shared (intent profile a) cs).2

theorem gate_accepted (profile : RssProduction.Profile) (d : Deployment) (corrupt : List Nat)
    (s : HistoryState) (a : Input) (cs : List Certificate)
    (h : gate profile d corrupt s a cs = true) :
    a.request.honestApprovers = custodyQuorumHonestApprovers corrupt cs ∧
    (submitRecorded d s.shared (intent profile a) cs).2 = true := by
  exact ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp h).1, (Bool.and_eq_true_iff.mp h).2⟩

/-- Each individual accepted certificate, not merely one quorum member, has
an actual contextual policy origin or is the concrete signature-game candidate.
The resource bound comes from the generated trace's one-time query discipline. -/
theorem candidate_origin (profile : RssProduction.Profile) (d : Deployment)
    (commands : List HistoryCommand) (c : Certificate)
    (hw : d.signer.params.w = 4 ∨ d.signer.params.w = 16)
    (hst : d.signer.params.statefulJorts = true)
    (hv : verify d.signer (publicKeys d c.party) d.deploymentId c.party c.intent c.signature = true) :
    let s := generatedHistory profile d commands
    ProducedPolicyApproval profile d s c.party c.intent ∨
      (prodEufCmaWin d.signer.suite d.signer.params
        ⟨d.keys c.party, queries d.signer d.deploymentId c.party (s.parties c.party).vault,
          payload d.deploymentId c.party c.intent, c.signature⟩ = true ∧
       (ProdSmTcrBreak d.signer.suite d.signer.params (d.keys c.party)
          (signingLog d.signer (d.keys c.party) d.deploymentId c.party (s.parties c.party).vault) ∨
        ProdPreimageBreak d.signer.suite d.signer.params (d.keys c.party)
          (signingLog d.signer (d.keys c.party) d.deploymentId c.party (s.parties c.party).vault)
          (payload d.deploymentId c.party c.intent) c.signature)) := by
  intro s
  have hs := generatedHistory_valid profile d commands
  by_cases hm : payload d.deploymentId c.party c.intent ∈
      (signingLog d.signer (d.keys c.party) d.deploymentId c.party (s.parties c.party).vault).map Prod.fst
  · exact .inl (successful_log_produced profile d s c.party c.intent hs hst hm)
  · have hf : ∀ e ∈ signingLog d.signer (d.keys c.party) d.deploymentId c.party (s.parties c.party).vault,
        e.1 ≠ payload d.deploymentId c.party c.intent := by
      intro e he heq
      exact hm (List.mem_map.mpr ⟨e, he, heq⟩)
    exact .inr ⟨Bool.and_eq_true_iff.mpr ⟨hv, decide_eq_true hm⟩,
      production_stateful_forgery_break d.signer.suite d.signer.params (d.keys c.party)
        (queries d.signer d.deploymentId c.party (s.parties c.party).vault) (payload d.deploymentId c.party c.intent)
        c.signature hw hst (queries_one_time _ _ _ _ _ _ (hs.safe c.party)) hf hv⟩

/-- The engine's structural approval is derived from wire verification and the
certificate roster. Scheduler-provided identities alone cannot enter this port. -/
theorem gate_threshold (profile : RssProduction.Profile) (d : Deployment)
    (st : IdealTsigState PqPublicKey (List UInt8)) (ha : CustodyTsigAligned d st)
    (s : HistoryState) (a : Input) (cs : List Certificate)
    (hq : ∀ c ∈ cs, c.party ∉ st.identifiedCheaters)
    (h : gate profile d st.corruptParties s a cs = true) :
    validThresholdApproval st a.request.honestApprovers = true := by
  obtain ⟨hr, hg⟩ := gate_accepted profile d st.corruptParties s a cs h
  rw [hr]
  rw [submitRecorded_verdict] at hg
  exact (acceptQuorum_implies_validThresholdApproval d st ha _ _ cs hq
    (submit_accepted _ _ _ _ _ _ _ _ hg).1).2

/-- Actual participant input events retained by the executed history. These are
not supplied by scheduling commands. -/
def participantInputs (s : HistoryState) : List (Nat × SessionScheduleReq) :=
  s.calls.map (fun e => (e.party, e.invocation.request))

def CandidateForgery (d : Deployment) (s : HistoryState) (c : Certificate) : Prop :=
  prodEufCmaWin d.signer.suite d.signer.params
    ⟨d.keys c.party, queries d.signer d.deploymentId c.party (s.parties c.party).vault,
      payload d.deploymentId c.party c.intent, c.signature⟩ = true

/-- Every claimed honest approver at the operational gate corresponds to an
actual prior matching participant input, or an accepted certificate itself wins
the concrete one-time signature game. Later inputs cannot justify this prefix. -/
theorem gate_participant_input_or_forgery (profile : RssProduction.Profile)
    (d : Deployment) (corrupt : List Nat) (commands : List HistoryCommand)
    (a : Input) (cs : List Certificate)
    (hw : d.signer.params.w = 4 ∨ d.signer.params.w = 16)
    (hst : d.signer.params.statefulJorts = true)
    (hg : gate profile d corrupt (generatedHistory profile d commands) a cs = true)
    (i : Nat) (hi : i ∈ a.request.honestApprovers) :
    (i, a.request) ∈ participantInputs (generatedHistory profile d commands) ∨
      ∃ c ∈ cs, c.party = i ∧ CandidateForgery d (generatedHistory profile d commands) c := by
  let s := generatedHistory profile d commands
  obtain ⟨hr, ha⟩ := gate_accepted profile d corrupt s a cs hg
  rw [hr] at hi
  obtain ⟨hids, _⟩ := List.mem_filter.mp hi
  obtain ⟨c, hcm, hci⟩ := List.mem_map.mp hids
  rw [submitRecorded_verdict] at ha
  have hq := (submit_accepted _ _ _ _ _ _ _ _ ha).1
  have hvall := (Bool.and_eq_true_iff.mp hq).2
  have hv := List.all_eq_true.mp hvall c hcm
  obtain ⟨hintent, hverify⟩ := Bool.and_eq_true_iff.mp hv
  have he : c.intent = intent profile a := of_decide_eq_true hintent
  rcases candidate_origin profile d commands c hw hst hverify with horigin | hforge
  · obtain ⟨e, hem, hei, _, _, her, _⟩ := horigin
    have heq := (same_intent_same_request profile profile e.invocation a (her.trans he)).1
    left
    apply List.mem_map.mpr
    exact ⟨e, hem, Prod.ext (hei.trans hci) heq⟩
  · exact .inr ⟨c, hcm, hci, hforge.1⟩

/-- Only successful, policy-admitted participant invocations become ideal
approval inputs. Rejected invocations cannot populate the ideal approval ledger. -/
def approvedParticipantInputs (s : HistoryState) : List (Nat × SessionScheduleReq) :=
  (s.calls.filter (fun e => e.output.isSome &&
    policyCheckAdmission e.before e.invocation.transaction e.invocation.tags e.invocation.timestamp)).map
    (fun e => (e.party, e.invocation.request))

