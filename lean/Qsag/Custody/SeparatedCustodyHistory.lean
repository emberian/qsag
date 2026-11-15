module
public import Qsag.Custody.SeparatedCustodyPolicy
import all Qsag.Custody.SeparatedCustodyPolicy
import all Qsag.Custody.SeparatedCustodySpine
import all Qsag.Custody.CompleteMediationBoundary
import all Qsag.Custody.SeparatedCustodyCore
import all Qsag.Protocol.Signing.HypertreeEufCma
import Qsag.Tactic.AssuranceKit

/-! One executed multi-party policy history and one shared acceptance ledger.
Invocation records are semantic audit history, not additional public disclosures
of custodian policy keys. The coordinator sees certificates and its own ledger.
-/
public section
namespace Qsag.Custody
set_option autoImplicit false
set_option maxRecDepth 4096

structure Deployment where
  signer : SigningConfig
  keys : Nat → PqSecretKey
  rounds : Nat → RoundPolicy
  caps : Nat → Nat
  policies : Nat → AuthenticatedPolicyState
  numParties : Nat
  threshold : Nat
  capacity : Nat

def publicKeys (d : Deployment) (i : Nat) : PqPublicKey :=
  derivePublicKey d.signer.suite d.signer.params (d.keys i)

structure Invocation where
  transaction : TransactionIntent
  tags : List InitiatorPeerTag
  timestamp : Nat
  round : Nat
  leaf : Nat
  openings : List RoundOpening

def Invocation.intent (a : Invocation) : Intent :=
  transactionIntent a.transaction a.round a.leaf

structure InvocationRecord where
  party : Nat
  before : AuthenticatedPolicyState
  invocation : Invocation
  output : Option Certificate

structure AcceptedSubmission where
  intent : Intent
  certificates : List Certificate

structure SharedHistory where
  coordinator : Coordinator
  accepted : List AcceptedSubmission := []

structure SharedSafe (cap : Nat) (s : SharedHistory) : Prop where
  capacity : s.coordinator.capacity = cap
  accounting : s.coordinator.spent = (s.accepted.map (fun a => a.intent.spend)).sum
  sessions : s.coordinator.consumedSessions = s.accepted.map (fun a => a.intent.session)
  distinct : s.coordinator.consumedSessions.Nodup
  budget : s.coordinator.spent ≤ cap

/-- This is the sole shared accepted-spend/session transition. -/
def submitRecorded (d : Deployment) (s : SharedHistory) (r : Intent) (cs : List Certificate) :
    SharedHistory × Bool :=
  let result := submit d.signer (publicKeys d) d.numParties d.threshold s.coordinator r cs
  if result.2 then (⟨result.1, ⟨r, cs⟩ :: s.accepted⟩, true)
  else (⟨result.1, s.accepted⟩, false)

private theorem submit_rejected (cfg : SigningConfig) (pks : Nat → PqPublicKey)
    (n t : Nat) (st : Coordinator) (r : Intent) (cs : List Certificate)
    (h : (submit cfg pks n t st r cs).2 = false) :
    (submit cfg pks n t st r cs).1 = st := by
  unfold submit at h ⊢
  split
  next ha =>
    split
    next hb => simp only [ha, hb, ↓reduceIte] at h; cases h
    next => rfl
  next => rfl

theorem submitRecorded_safe (d : Deployment) (s : SharedHistory) (r : Intent)
    (cs : List Certificate) (hs : SharedSafe d.capacity s) :
    SharedSafe d.capacity (submitRecorded d s r cs).1 := by
  unfold submitRecorded
  dsimp only
  split
  next ha =>
    obtain ⟨hc, hb, he⟩ := submit_accepted d.signer (publicKeys d) d.numParties d.threshold
      s.coordinator r cs ha
    rw [he]
    have hf : r.session ∉ s.coordinator.consumedSessions :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).1
    constructor
    · exact hs.capacity
    · change s.coordinator.spent + r.spend =
        ((⟨r, cs⟩ :: s.accepted).map (fun a => a.intent.spend)).sum
      simp only [List.map_cons, List.sum_cons]
      rw [hs.accounting]
      exact Nat.add_comm _ _
    · change r.session :: s.coordinator.consumedSessions = r.session :: _
      rw [hs.sessions]
    · exact List.nodup_cons.mpr ⟨hf, hs.distinct⟩
    · exact hs.capacity ▸ hb
  next ha =>
    have hn : (submit d.signer (publicKeys d) d.numParties d.threshold s.coordinator r cs).2 = false :=
      Bool.eq_false_iff.mpr ha
    rw [submit_rejected _ _ _ _ _ _ _ hn]
    exact hs

structure HistoryState where
  parties : Nat → PolicyVault
  calls : List InvocationRecord := []
  shared : SharedHistory

def historyInitial (d : Deployment) : HistoryState :=
  ⟨fun i => ⟨{ d.policies i with party := i }, initial⟩, [],
    ⟨{ capacity := d.capacity }, []⟩⟩

def replaceParty (parties : Nat → PolicyVault) (i : Nat) (v : PolicyVault) : Nat → PolicyVault :=
  fun j => if j = i then v else parties j

def invoke (d : Deployment) (s : HistoryState) (i anchor : Nat) (a : Invocation) : HistoryState :=
  let result := executeTransaction d.signer (d.keys i) (d.rounds i) (d.caps i) anchor
    (s.parties i) a.transaction a.tags a.timestamp a.round a.leaf a.openings
  ⟨replaceParty s.parties i result.1,
    ⟨i, (s.parties i).policy, a, result.2⟩ :: s.calls, s.shared⟩

inductive HistoryCommand where
  | invoke (party anchor : Nat) (invocation : Invocation)
  | forget (party : Nat)
  | submit (intent : Intent) (certificates : List Certificate)

def historyStep (d : Deployment) (s : HistoryState) : HistoryCommand → HistoryState
  | .invoke i anchor a => invoke d s i anchor a
  | .forget i =>
    let cleared : PolicyVault := ⟨(s.parties i).policy, forget (s.parties i).vault⟩
    { s with parties := replaceParty s.parties i cleared }
  | .submit r cs => { s with shared := (submitRecorded d s.shared r cs).1 }

def historyRun (d : Deployment) : HistoryState → List HistoryCommand → HistoryState
  | s, [] => s
  | s, c :: cs => historyRun d (historyStep d s c) cs

/-- This invariant is proved from the initial state and executed commands.
It is never an input to the exported generated-history provenance theorem. -/
structure Generated (d : Deployment) (s : HistoryState) : Prop where
  safe : ∀ i, Safe (d.rounds i) (d.caps i) (s.parties i).vault
  identities : ∀ i, (s.parties i).policy.party = i
  origin : ∀ i r, r ∈ (s.parties i).vault.attempted →
    ∃ e ∈ s.calls, e.party = i ∧ e.before.party = i ∧
      policyCheckAdmission e.before e.invocation.transaction e.invocation.tags e.invocation.timestamp = true ∧
      e.invocation.intent = r ∧
      e.output = (sign d.signer (d.keys i) i r).map (fun sig => ⟨i, r, sig⟩)
  shared : SharedSafe d.capacity s.shared

theorem historyInitial_generated (d : Deployment) : Generated d (historyInitial d) := by
  refine ⟨(fun i => initial_safe (d.rounds i) (d.caps i)), (fun _ => rfl), ?_, ?_⟩
  · intro i r hm; cases hm
  · exact ⟨rfl, rfl, rfl, .nil, Nat.zero_le _⟩

theorem invoke_generated (d : Deployment) (s : HistoryState) (i anchor : Nat) (a : Invocation)
    (h : Generated d s) : Generated d (invoke d s i anchor a) := by
  constructor
  · intro j
    unfold invoke replaceParty
    dsimp only
    split
    next he =>
      subst j
      exact executeTransaction_safe d.signer (d.keys i) (d.rounds i) (d.caps i) anchor
        (s.parties i) a.transaction a.tags a.timestamp a.round a.leaf a.openings (h.safe i)
    next => exact h.safe j
  · intro j
    unfold invoke replaceParty
    dsimp only
    split
    next he =>
      subst j
      exact (executeTransaction_party d.signer (d.keys i) (d.rounds i) (d.caps i) anchor
        (s.parties i) a.transaction a.tags a.timestamp a.round a.leaf a.openings).trans (h.identities i)
    next => exact h.identities j
  · intro j r hm
    unfold invoke replaceParty at hm ⊢
    dsimp only at hm ⊢
    split at hm
    next he =>
      subst j
      rcases executeTransaction_attempt_origin d.signer (d.keys i) (d.rounds i) (d.caps i) anchor
        (s.parties i) a.transaction a.tags a.timestamp a.round a.leaf a.openings r hm with hold | hnew
      · obtain ⟨e, he, rest⟩ := h.origin i r hold
        exact ⟨e, List.mem_cons_of_mem _ he, rest⟩
      · obtain ⟨ha, hr, ho⟩ := hnew
        refine ⟨_, List.mem_cons_self, rfl, h.identities i, ha, hr.symm, ?_⟩
        rw [h.identities i] at ho
        exact ho
    next =>
      obtain ⟨e, he, rest⟩ := h.origin j r hm
      exact ⟨e, List.mem_cons_of_mem _ he, rest⟩
  · exact h.shared

theorem historyStep_generated (d : Deployment) (s : HistoryState) (c : HistoryCommand)
    (h : Generated d s) : Generated d (historyStep d s c) := by
  cases c with
  | invoke i anchor a => exact invoke_generated d s i anchor a h
  | submit r cs =>
    exact ⟨h.safe, h.identities, h.origin, submitRecorded_safe d s.shared r cs h.shared⟩
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
    · intro j r hm
      unfold historyStep replaceParty at hm ⊢
      dsimp only at hm ⊢
      split at hm
      next he => subst j; exact h.origin i r hm
      next => exact h.origin j r hm
    · exact h.shared

theorem historyRun_generated (d : Deployment) (s : HistoryState) (cs : List HistoryCommand)
    (h : Generated d s) : Generated d (historyRun d s cs) := by
  induction cs generalizing s with
  | nil => exact h
  | cons c cs ih => exact ih _ (historyStep_generated d s c h)

def generatedHistory (d : Deployment) (cs : List HistoryCommand) : HistoryState :=
  historyRun d (historyInitial d) cs

theorem generatedHistory_valid (d : Deployment) (cs : List HistoryCommand) :
    Generated d (generatedHistory d cs) :=
  historyRun_generated d _ cs (historyInitial_generated d)

/-- A produced approval is a record of an actual invocation with its actual
successful output, not an authorization predicate supplied to the execution. -/
def ProducedPolicyApproval (d : Deployment) (s : HistoryState) (i : Nat) (r : Intent) : Prop :=
  ∃ e ∈ s.calls, e.party = i ∧ e.before.party = i ∧
    policyCheckAdmission e.before e.invocation.transaction e.invocation.tags e.invocation.timestamp = true ∧
    e.invocation.intent = r ∧
    ∃ issued, e.output = some issued ∧ issued.party = i ∧ issued.intent = r ∧
      verify d.signer (publicKeys d i) i r issued.signature = true

theorem successful_log_produced (d : Deployment) (s : HistoryState) (i : Nat) (r : Intent)
    (h : Generated d s) (hst : d.signer.params.statefulJorts = true)
    (hm : payload i r ∈ (signingLog d.signer (d.keys i) i (s.parties i).vault).map Prod.fst) :
    ProducedPolicyApproval d s i r := by
  obtain ⟨entry, he, hem⟩ := List.mem_map.mp hm
  obtain ⟨q, hq, hmsg, hsign⟩ := productionSigningLog_generated _ _ _ _ entry he
  obtain ⟨requested, hr, hreq⟩ := List.mem_map.mp hq
  have hp : payload i requested = payload i r := by
    simpa only [← hreq, query] using hmsg.symm.trans hem
  have heq := (payload_injective hp).2
  subst requested
  subst q
  have hs : sign d.signer (d.keys i) i r = some entry.2 :=
    (sign_eq_query d.signer (d.keys i) i r hst).trans hsign
  obtain ⟨e, he, hi, hb, ha, hc, ho⟩ := h.origin i r hr
  refine ⟨e, he, hi, hb, ha, hc, ⟨i, r, entry.2⟩, ?_, rfl, rfl, ?_⟩
  · rw [ho, hs]
    rfl
  · exact sign_verifies d.signer (d.keys i) i r entry.2 hs

theorem submitRecorded_verdict (d : Deployment) (s : SharedHistory) (r : Intent)
    (cs : List Certificate) :
    (submitRecorded d s r cs).2 =
      (submit d.signer (publicKeys d) d.numParties d.threshold s.coordinator r cs).2 := by
  unfold submitRecorded
  dsimp only
  cases h : (submit d.signer (publicKeys d) d.numParties d.threshold s.coordinator r cs).2 <;> rfl

/-- At every generated-history prefix, an accepted quorum has an honest
certificate whose full intent was actually produced by an earlier admitted
policy invocation, or the submitted candidate wins the actual signature game.
The histories and all provenance facts are computed/proved from commands.
In particular a failed signing attempt is not counted as a produced output.
-/
theorem generated_submit_provenance (d : Deployment) (commands : List HistoryCommand)
    (corrupt : List Nat) (r : Intent) (cs : List Certificate)
    (hw : d.signer.params.w = 4 ∨ d.signer.params.w = 16)
    (hst : d.signer.params.statefulJorts = true) (hc : corrupt.length < d.threshold)
    (ha : (submitRecorded d (generatedHistory d commands).shared r cs).2 = true) :
    ∃ c ∈ cs, c.party ∉ corrupt ∧
      (ProducedPolicyApproval d (generatedHistory d commands) c.party r ∨
       (prodEufCmaWin d.signer.suite d.signer.params
          ⟨d.keys c.party, queries d.signer c.party ((generatedHistory d commands).parties c.party).vault,
            payload c.party r, c.signature⟩ = true ∧
        (ProdSmTcrBreak d.signer.suite d.signer.params (d.keys c.party)
           (signingLog d.signer (d.keys c.party) c.party ((generatedHistory d commands).parties c.party).vault) ∨
         ProdPreimageBreak d.signer.suite d.signer.params (d.keys c.party)
           (signingLog d.signer (d.keys c.party) c.party ((generatedHistory d commands).parties c.party).vault)
           (payload c.party r) c.signature))) := by
  let s := generatedHistory d commands
  have hs : Generated d s := generatedHistory_valid d commands
  rw [submitRecorded_verdict] at ha
  obtain ⟨c, hcm, hch, _, hv⟩ := quorum_has_honest d.signer (publicKeys d)
    d.numParties d.threshold s.shared.coordinator.consumedSessions corrupt r cs hc
    (submit_accepted _ _ _ _ _ _ _ ha).1
  refine ⟨c, hcm, hch, ?_⟩
  by_cases hm : payload c.party r ∈
      (signingLog d.signer (d.keys c.party) c.party (s.parties c.party).vault).map Prod.fst
  · exact .inl (successful_log_produced d s c.party r hs hst hm)
  · have hf : ∀ e ∈ signingLog d.signer (d.keys c.party) c.party (s.parties c.party).vault,
        e.1 ≠ payload c.party r := by
      intro e he heq
      exact hm (List.mem_map.mpr ⟨e, he, heq⟩)
    right
    refine ⟨?_, ?_⟩
    · unfold prodEufCmaWin
      exact Bool.and_eq_true_iff.mpr ⟨hv, decide_eq_true hm⟩
    · exact production_stateful_forgery_break d.signer.suite d.signer.params (d.keys c.party)
        (queries d.signer c.party (s.parties c.party).vault) (payload c.party r) c.signature hw hst
        (queries_one_time d.signer c.party _ _ _ (hs.safe c.party)) hf hv

/-- One shared acceptance trace supplies both the spend sum and the unique
session list, including across changing/disjoint signing quorums. -/
theorem generated_shared_accounting (d : Deployment) (commands : List HistoryCommand) :
    let s := (generatedHistory d commands).shared
    s.coordinator.spent = (s.accepted.map (fun a => a.intent.spend)).sum ∧
    s.coordinator.consumedSessions = s.accepted.map (fun a => a.intent.session) ∧
    s.coordinator.consumedSessions.Nodup ∧ s.coordinator.spent ≤ d.capacity := by
  have hs := (generatedHistory_valid d commands).shared
  exact ⟨hs.accounting, hs.sessions, hs.distinct, hs.budget⟩

theorem generated_burn_accounting (d : Deployment) (commands : List HistoryCommand) (i : Nat) :
    let v := ((generatedHistory d commands).parties i).vault
    (v.durable.burned.map (fun b => b.intent.spend)).sum ≤ d.caps i ∧
      v.attempted.Nodup := by
  have hs := (generatedHistory_valid d commands).safe i
  exact ⟨hs.accounting ▸ hs.budget, hs.attemptedNodup⟩

theorem generated_replay_rejected (d : Deployment) (commands : List HistoryCommand)
    (r : Intent) (cs : List Certificate)
    (hm : r.session ∈ ((generatedHistory d commands).shared.accepted.map (fun a => a.intent.session))) :
    (submitRecorded d (generatedHistory d commands).shared r cs).2 = false := by
  have hs := (generatedHistory_valid d commands).shared
  have hmem : r.session ∈ (generatedHistory d commands).shared.coordinator.consumedSessions :=
    hs.sessions ▸ hm
  rw [submitRecorded_verdict]
  unfold submit
  rw [quorum_replay_rejected _ _ _ _ _ _ _ hmem]
  rfl

/-- Invocation failure/withholding cannot silently add a shared accepted spend.
Local burns, by contrast, are preserved by the generated-state invariant. -/
theorem invoke_shared_unchanged (d : Deployment) (s : HistoryState) (i anchor : Nat) (a : Invocation) :
    (invoke d s i anchor a).shared = s.shared := by
  unfold invoke
  rfl

end Qsag.Custody
end
set_option maxRecDepth 4096
#verify_constructive Qsag.Custody.generatedHistory_valid
#verify_constructive Qsag.Custody.submitRecorded_safe
#verify_constructive Qsag.Custody.generated_submit_provenance
#verify_constructive Qsag.Custody.generated_shared_accounting
#verify_constructive Qsag.Custody.generated_burn_accounting
#verify_constructive Qsag.Custody.generated_replay_rejected
