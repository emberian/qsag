module
public import Qsag.SeparatedCustodyRequestHistory
public import Qsag.SeparatedCustodyUcBridge
import all Qsag.SeparatedCustodyRequestHistory
import all Qsag.SeparatedCustodyUcBridge
import all Qsag.SeparatedCustodySpine
import all Qsag.SeparatedCustodyCore
import all Qsag.RssProductionProfile
import Qsag.Tactic.AssuranceKit

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
    (hv : verify d.signer (publicKeys d c.party) c.party c.intent c.signature = true) :
    let s := generatedHistory profile d commands
    ProducedPolicyApproval profile d s c.party c.intent ∨
      (prodEufCmaWin d.signer.suite d.signer.params
        ⟨d.keys c.party, queries d.signer c.party (s.parties c.party).vault,
          payload c.party c.intent, c.signature⟩ = true ∧
       (ProdSmTcrBreak d.signer.suite d.signer.params (d.keys c.party)
          (signingLog d.signer (d.keys c.party) c.party (s.parties c.party).vault) ∨
        ProdPreimageBreak d.signer.suite d.signer.params (d.keys c.party)
          (signingLog d.signer (d.keys c.party) c.party (s.parties c.party).vault)
          (payload c.party c.intent) c.signature)) := by
  intro s
  have hs := generatedHistory_valid profile d commands
  by_cases hm : payload c.party c.intent ∈
      (signingLog d.signer (d.keys c.party) c.party (s.parties c.party).vault).map Prod.fst
  · exact .inl (successful_log_produced profile d s c.party c.intent hs hst hm)
  · have hf : ∀ e ∈ signingLog d.signer (d.keys c.party) c.party (s.parties c.party).vault,
        e.1 ≠ payload c.party c.intent := by
      intro e he heq
      exact hm (List.mem_map.mpr ⟨e, he, heq⟩)
    exact .inr ⟨Bool.and_eq_true_iff.mpr ⟨hv, decide_eq_true hm⟩,
      production_stateful_forgery_break d.signer.suite d.signer.params (d.keys c.party)
        (queries d.signer c.party (s.parties c.party).vault) (payload c.party c.intent)
        c.signature hw hst (queries_one_time _ _ _ _ _ (hs.safe c.party)) hf hv⟩

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
    (submit_accepted _ _ _ _ _ _ _ hg).1).2

/-- Actual participant input events retained by the executed history. These are
not supplied by scheduling commands. -/
def participantInputs (s : HistoryState) : List (Nat × SessionScheduleReq) :=
  s.calls.map (fun e => (e.party, e.invocation.request))

def CandidateForgery (d : Deployment) (s : HistoryState) (c : Certificate) : Prop :=
  prodEufCmaWin d.signer.suite d.signer.params
    ⟨d.keys c.party, queries d.signer c.party (s.parties c.party).vault,
      payload c.party c.intent, c.signature⟩ = true

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
  have hq := (submit_accepted _ _ _ _ _ _ _ ha).1
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

theorem gate_approved_participant_input_or_forgery (profile : RssProduction.Profile)
    (d : Deployment) (corrupt : List Nat) (commands : List HistoryCommand)
    (a : Input) (cs : List Certificate)
    (hw : d.signer.params.w = 4 ∨ d.signer.params.w = 16)
    (hst : d.signer.params.statefulJorts = true)
    (hg : gate profile d corrupt (generatedHistory profile d commands) a cs = true)
    (i : Nat) (hi : i ∈ a.request.honestApprovers) :
    (i, a.request) ∈ approvedParticipantInputs (generatedHistory profile d commands) ∨
      ∃ c ∈ cs, c.party = i ∧ CandidateForgery d (generatedHistory profile d commands) c := by
  let s := generatedHistory profile d commands
  obtain ⟨hr, ha⟩ := gate_accepted profile d corrupt s a cs hg
  rw [hr] at hi
  obtain ⟨hids, _⟩ := List.mem_filter.mp hi
  obtain ⟨c, hcm, hci⟩ := List.mem_map.mp hids
  rw [submitRecorded_verdict] at ha
  have hq := (submit_accepted _ _ _ _ _ _ _ ha).1
  have hvall := (Bool.and_eq_true_iff.mp hq).2
  have hv := List.all_eq_true.mp hvall c hcm
  obtain ⟨hintent, hverify⟩ := Bool.and_eq_true_iff.mp hv
  have he : c.intent = intent profile a := of_decide_eq_true hintent
  rcases candidate_origin profile d commands c hw hst hverify with horigin | hforge
  · obtain ⟨e, hem, hei, _, hpolicy, her, issued, hout, _⟩ := horigin
    have heq := (same_intent_same_request profile profile e.invocation a (her.trans he)).1
    left
    apply List.mem_map.mpr
    exact ⟨e, List.mem_filter.mpr ⟨hem, by simp [hout, hpolicy]⟩,
      Prod.ext (hei.trans hci) heq⟩
  · exact .inr ⟨c, hcm, hci, hforge.1⟩

structure Reservation where
  request : SessionScheduleReq
  leaf : Nat

/-- Durable resource state: immutable committed reservations and retained
successful outputs, protected by an external authenticated generation head. -/
structure Generation where
  number : Nat := 0
  nextLeaf : Nat := 0
  reserved : List Reservation := []
  cached : List (SessionScheduleReq × List UInt8) := []

structure ResourceState where
  history : HistoryState
  durable : Generation := {}
  active : List SessionScheduleReq := []
  buffered : List (SessionScheduleReq × List UInt8) := []
  observed : List (SessionScheduleReq × List UInt8) := []
  returned : List (SessionScheduleReq × List UInt8) := []
  poisoned : Bool := false
  failures : List (SessionScheduleReq × RssProduction.Failure) := []

def resourceInitial (d : Deployment) : ResourceState :=
  { history := historyInitial d }

/-- Authenticated generation commit is the storage hybrid's operation. A lost
activation after commit consumes the leaf/session but never invokes production. -/
def start (profile : RssProduction.Profile) (d : Deployment) (corrupt : List Nat)
    (s : ResourceState) (a : Input) (cs : List Certificate) (activate : Bool) : ResourceState :=
  if s.poisoned || decide (a.request.reqEpoch ≠ s.durable.nextLeaf) then s
  else if gate profile d corrupt s.history a cs then
    { s with
      history := { s.history with shared := (submitRecorded d s.history.shared (intent profile a) cs).1 }
      durable := { s.durable with
        number := s.durable.number + 1
        nextLeaf := s.durable.nextLeaf + 1
        reserved := ⟨a.request, s.durable.nextLeaf⟩ :: s.durable.reserved }
      active := if activate then a.request :: s.active else s.active }
  else s

/-- A participant wire is emitted only for a previously reserved active request.
The wire producer is the participant protocol, not this storage resource. -/
def emit (s : ResourceState) (req : SessionScheduleReq) (wire : List UInt8) : ResourceState :=
  if req ∈ s.active then { s with observed := (req, wire) :: s.observed } else s

/-- Actual shared production, with explicit failure. A computed useful result is
visible immediately, before durable caching and before API return. -/
def produce (profile : RssProduction.Profile) (s : ResourceState)
    (req : SessionScheduleReq) : ResourceState :=
  if req ∈ s.active then
    let consumed := { s with active := s.active.filter (fun a => decide (a ≠ req)) }
    match RssProduction.partialOutput profile req with
    | .error reason => { consumed with failures := (req, reason) :: s.failures }
    | .ok bytes =>
      { consumed with
        buffered := (req, bytes) :: s.buffered
        observed := (req, bytes) :: s.observed }
  else s

/-- Commit the exact buffer to the authenticated generation before returning it.
Returning is independently interruptible; exact retries read this cached result. -/
def commitOutput (s : ResourceState) : ResourceState :=
  { s with
    durable := { s.durable with
      number := s.durable.number + 1
      cached := s.buffered ++ s.durable.cached }
    buffered := [] }

def retry (s : ResourceState) (req : SessionScheduleReq) : ResourceState :=
  match s.durable.cached.find? (fun pair => decide (pair.1 = req)) with
  | none => s
  | some pair => { s with returned := pair :: s.returned }

/-- Power loss clears volatile continuations/buffers, not committed reservations,
policy history, cached results, or anything already observed by the network. -/
def crash (s : ResourceState) : ResourceState :=
  { s with active := [], buffered := [] }

theorem crash_preserves_burn_and_observation (s : ResourceState) :
    (crash s).durable = s.durable ∧ (crash s).history = s.history ∧
    (crash s).observed = s.observed ∧ (crash s).returned = s.returned := ⟨rfl, rfl, rfl, rfl⟩

theorem crash_cannot_produce (profile : RssProduction.Profile) (s : ResourceState)
    (req : SessionScheduleReq) : produce profile (crash s) req = crash s := by
  simp [produce, crash]

theorem committed_lost_return_retry (s : ResourceState) (req : SessionScheduleReq)
    (bytes : List UInt8) (h : s.buffered = [(req, bytes)]) :
    (retry (crash (commitOutput s)) req).returned = (req, bytes) :: s.returned := by
  simp [retry, crash, commitOutput, h]

theorem start_burns_before_activation (profile : RssProduction.Profile) (d : Deployment)
    (corrupt : List Nat) (s : ResourceState) (a : Input) (cs : List Certificate)
    (activate : Bool) (hp : s.poisoned = false) (he : a.request.reqEpoch = s.durable.nextLeaf)
    (hg : gate profile d corrupt s.history a cs = true) :
    (start profile d corrupt s a cs activate).durable.nextLeaf = s.durable.nextLeaf + 1 ∧
    (start profile d corrupt s a cs activate).durable.reserved =
      ⟨a.request, s.durable.nextLeaf⟩ :: s.durable.reserved := by
  simp [start, hp, he, hg]

theorem wrong_epoch_no_producer (profile : RssProduction.Profile) (d : Deployment)
    (corrupt : List Nat) (s : ResourceState) (a : Input) (cs : List Certificate)
    (activate : Bool) (he : a.request.reqEpoch ≠ s.durable.nextLeaf) :
    start profile d corrupt s a cs activate = s := by simp [start, he]

theorem produce_visible_before_return (profile : RssProduction.Profile) (s : ResourceState)
    (req : SessionScheduleReq) (bytes : List UInt8) (ha : req ∈ s.active)
    (ho : RssProduction.partialOutput profile req = .ok bytes) :
    (crash (produce profile s req)).observed = (req, bytes) :: s.observed ∧
    (crash (produce profile s req)).returned = s.returned ∧
    (crash (produce profile s req)).durable = s.durable := by
  simp [produce, crash, ha, ho]

theorem produce_failure_retained (profile : RssProduction.Profile) (s : ResourceState)
    (req : SessionScheduleReq) (reason : RssProduction.Failure) (ha : req ∈ s.active)
    (ho : RssProduction.partialOutput profile req = .error reason) :
    (crash (produce profile s req)).failures = (req, reason) :: s.failures ∧
    (crash (produce profile s req)).durable = s.durable ∧
    (crash (produce profile s req)).observed = s.observed := by
  simp [produce, crash, ha, ho]

theorem consumed_session_rejected (profile : RssProduction.Profile) (d : Deployment)
    (corrupt : List Nat) (s : ResourceState) (a : Input) (cs : List Certificate)
    (activate : Bool) (hm : a.request.sessionId ∈ s.history.shared.coordinator.consumedSessions) :
    start profile d corrupt s a cs activate = s := by
  have hg : gate profile d corrupt s.history a cs = false := by
    unfold gate
    rw [submitRecorded_verdict]
    unfold submit
    rw [quorum_replay_rejected _ _ _ _ _ _ cs hm]
    simp
  simp [start, hg]

/-- Concurrent requests cannot consume one another's continuation. -/
theorem produce_preserves_other_active (profile : RssProduction.Profile) (s : ResourceState)
    (req other : SessionScheduleReq) (hne : other ≠ req) (ha : other ∈ s.active) :
    other ∈ (produce profile s req).active := by
  unfold produce
  split
  · split <;> exact List.mem_filter.mpr ⟨ha, decide_eq_true hne⟩
  · exact ha

/-- The supported input ports keep participant invocation distinct from host
scheduling. The environment supplies `approve`; the host supplies the others. -/
inductive ResourceCommand where
  | approve (party anchor : Nat) (input : Input)
  | schedule (input : Input) (certificates : List Certificate) (activate : Bool)
  | wire (request : SessionScheduleReq) (bytes : List UInt8)
  | produce (request : SessionScheduleReq)
  | commit
  | retry (request : SessionScheduleReq)
  | crash

def resourceStep (profile : RssProduction.Profile) (d : Deployment) (corrupt : List Nat)
    (s : ResourceState) : ResourceCommand → ResourceState
  | .approve i anchor a => { s with history := invoke profile d s.history i anchor a }
  | .schedule a cs activate => start profile d corrupt s a cs activate
  | .wire req bytes => emit s req bytes
  | .produce req => produce profile s req
  | .commit => commitOutput s
  | .retry req => retry s req
  | .crash => crash s

def resourceRun (profile : RssProduction.Profile) (d : Deployment) (corrupt : List Nat) :
    ResourceState → List ResourceCommand → ResourceState
  | s, [] => s
  | s, c :: cs => resourceRun profile d corrupt (resourceStep profile d corrupt s c) cs

/-- All useful observations have a durable reservation in the same execution.
This invariant concerns actual emitted wire bytes, not just completed API calls. -/
structure Accounted (s : ResourceState) : Prop where
  active : ∀ req ∈ s.active, ∃ r ∈ s.durable.reserved, r.request = req
  observed : ∀ e ∈ s.observed, ∃ r ∈ s.durable.reserved, r.request = e.1

theorem initial_accounted (profile : RssProduction.Profile) (d : Deployment) :
    Accounted (resourceInitial d) := by
  constructor <;> intro x hx <;> cases hx

theorem start_accounted (profile : RssProduction.Profile) (d : Deployment)
    (corrupt : List Nat) (s : ResourceState) (a : Input) (cs : List Certificate)
    (activate : Bool) (h : Accounted s) : Accounted (start profile d corrupt s a cs activate) := by
  unfold start
  split
  · exact h
  · split
    · constructor
      · intro req hm
        dsimp only at hm ⊢
        cases activate with
        | false =>
          obtain ⟨r, hr, he⟩ := h.active req hm
          exact ⟨r, List.mem_cons_of_mem _ hr, he⟩
        | true =>
          rcases List.mem_cons.mp hm with he | hm
          · exact ⟨_, List.mem_cons_self, he.symm⟩
          · obtain ⟨r, hr, he⟩ := h.active req hm
            exact ⟨r, List.mem_cons_of_mem _ hr, he⟩
      · intro e he
        obtain ⟨r, hr, heq⟩ := h.observed e he
        exact ⟨r, List.mem_cons_of_mem _ hr, heq⟩
    · exact h

theorem step_accounted (profile : RssProduction.Profile) (d : Deployment)
    (corrupt : List Nat) (s : ResourceState) (c : ResourceCommand) (h : Accounted s) :
    Accounted (resourceStep profile d corrupt s c) := by
  cases c with
  | approve i anchor a => exact ⟨h.active, h.observed⟩
  | schedule a cs activate => exact start_accounted profile d corrupt s a cs activate h
  | wire req bytes =>
    change Accounted (emit s req bytes)
    unfold emit
    split
    next ha =>
      refine ⟨h.active, ?_⟩
      intro e he
      rcases List.mem_cons.mp he with he | he
      · subst e; exact h.active req ha
      · exact h.observed e he
    next => exact h
  | produce req =>
    change Accounted (produce profile s req)
    unfold produce
    split
    next ha =>
      have ha' : ∀ q ∈ s.active.filter (fun a => decide (a ≠ req)),
          ∃ r ∈ s.durable.reserved, r.request = q :=
        fun q hq => h.active q (List.mem_filter.mp hq).1
      split
      · exact ⟨ha', h.observed⟩
      · refine ⟨ha', ?_⟩
        intro e he
        rcases List.mem_cons.mp he with he | he
        · subst e; exact h.active req ha
        · exact h.observed e he
    next => exact h
  | commit => exact ⟨h.active, h.observed⟩
  | retry req =>
    change Accounted (retry s req)
    unfold retry
    split <;> exact ⟨h.active, h.observed⟩
  | crash => exact ⟨(fun _ hx => by cases hx), h.observed⟩

theorem run_accounted (profile : RssProduction.Profile) (d : Deployment)
    (corrupt : List Nat) (s : ResourceState) (cs : List ResourceCommand) (h : Accounted s) :
    Accounted (resourceRun profile d corrupt s cs) := by
  induction cs generalizing s with
  | nil => exact h
  | cons c cs ih => exact ih _ (step_accounted profile d corrupt s c h)

theorem every_observed_wire_has_burn (profile : RssProduction.Profile) (d : Deployment)
    (corrupt : List Nat) (cs : List ResourceCommand) (e : SessionScheduleReq × List UInt8)
    (he : e ∈ (resourceRun profile d corrupt (resourceInitial d) cs).observed) :
    ∃ r ∈ (resourceRun profile d corrupt (resourceInitial d) cs).durable.reserved,
      r.request = e.1 :=
  (run_accounted profile d corrupt _ cs (initial_accounted profile d)).observed e he

end Qsag.Custody.RequestPolicy
end
#verify_constructive Qsag.Custody.RequestPolicy.candidate_origin
#verify_constructive Qsag.Custody.RequestPolicy.gate_threshold
#verify_constructive Qsag.Custody.RequestPolicy.start_burns_before_activation
#verify_constructive Qsag.Custody.RequestPolicy.committed_lost_return_retry
#verify_constructive Qsag.Custody.RequestPolicy.produce_visible_before_return
#verify_constructive Qsag.Custody.RequestPolicy.produce_preserves_other_active

#verify_constructive Qsag.Custody.RequestPolicy.gate_participant_input_or_forgery

#verify_constructive Qsag.Custody.RequestPolicy.every_observed_wire_has_burn

#verify_constructive Qsag.Custody.RequestPolicy.produce_failure_retained
#verify_constructive Qsag.Custody.RequestPolicy.consumed_session_rejected

#verify_constructive Qsag.Custody.RequestPolicy.gate_approved_participant_input_or_forgery
