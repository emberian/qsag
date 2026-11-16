module
public import Qsag.Spec.Sessions

public import Qsag.Exec.InteractiveServiceContext
public import Qsag.Exec.RssProductionProfile
public import Qsag.Exec.InteractiveUcEngine

public section
namespace Qsag.ThresholdIdealService
set_option autoImplicit false

/-- Static enrollment. The profile fixes the key, context, all parameters, and
signing effort. Honest inputs and adversarial scheduling use distinct ports.
This initial slice has static corruption and no refresh/migration operation. -/
structure Config where
  profile : RssProduction.Profile
  parties : Nat
  threshold : Nat
  corrupt : List Nat
  maxAttempts : Nat

/-- Public enrollment given to the environment/simulator. The functionality's
`Config.profile.material` is not part of this exported interface. -/
structure PublicConfig where
  key : PqPublicKey
  parameters : PqHashParams
  context : List UInt8
  grindLimit : Nat
  parties : Nat
  threshold : Nat
  corrupt : List Nat
  maxAttempts : Nat

def publicConfig (c : Config) : PublicConfig :=
  ⟨RssProduction.enrolledKey c.profile, c.profile.params, c.profile.context,
    c.profile.grindLimit, c.parties, c.threshold, c.corrupt, c.maxAttempts⟩

inductive HonestInput where
  | approve (party : Nat) (request : SessionScheduleReq)

inductive Schedule where
  | wait
  | start (request : SessionScheduleReq)
  | execute (slot : Nat)
  | deliver (slot : Nat)
  | abort (slot : Nat)

inductive Input where
  | honest (input : HonestInput)
  | adversary (schedule : Schedule)

inductive Rejection where
  | unauthorized | exhausted | absent | wrongPhase | adversarialAbort
  deriving DecidableEq, Repr

/-- Routed output: only `delivered` is a caller delivery. `disclosed` exposes the
result to the adversary before delivery, including after a later abort. -/
inductive Output where
  | idle
  | approved (party : Nat) (session : Nat)
  | queued (slot : Nat) (request : SessionScheduleReq)
  | disclosed (slot : Nat) (result : Except RssProduction.Failure (List UInt8))
  | delivered (slot : Nat) (request : SessionScheduleReq)
      (result : Except RssProduction.Failure (List UInt8))
  | rejected (reason : Rejection)

inductive Phase where
  | pending
  | ready (result : Except RssProduction.Failure (List UInt8))
  | closed

structure Slot where
  request : SessionScheduleReq
  phase : Phase

structure State where
  approvals : List (Nat × SessionScheduleReq)
  slots : List Slot
  wal : WalLatchState

/-- There is no adversarial command for writing this input ledger. The service
checks complete request equality, including randomness and intended roster. -/
@[expose] def authorized (c : Config) (s : State) (r : SessionScheduleReq) : Bool :=
  decide (0 < c.threshold ∧ c.threshold ≤ c.parties ∧
    c.corrupt.Nodup ∧ (∀ p ∈ c.corrupt, p < c.parties) ∧
    c.corrupt.length < c.threshold ∧ r.honestApprovers ≠ [] ∧
    r.honestApprovers.Nodup ∧
    (∀ p ∈ r.honestApprovers, p < c.parties ∧ p ∉ c.corrupt ∧
      (p, r) ∈ s.approvals) ∧
    c.threshold ≤ c.corrupt.length + r.honestApprovers.length)

def initial (c : Config) : State := ⟨[], [], RssProduction.initial c.profile⟩

/-- Total list update; an invalid index does not change any slot. -/
def updateSlot : List Slot → Nat → Slot → List Slot
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | x :: xs, n + 1, v => x :: updateSlot xs n v

abbrev Release := SessionScheduleReq → WalLatchState →
  WalLatchState × Except RssProduction.Failure (List UInt8)

/-- Slots can interleave freely. Execution commits the WAL before disclosure;
delivery/abort cannot roll back it. Aborting pending work consumes the slot;
aborting ready work cannot erase prior adversarial knowledge. Exact retries
are new slots and use the profile's WAL cache. Attempts count even aborted
slots, so retries cannot bypass the explicit resource bound. -/
def stepWith (c : Config) (release : Release) (s : State) : Input → State × Output
  | .honest (.approve p r) =>
    if p < c.parties ∧ p ∉ c.corrupt then
      ({s with approvals := (p, r) :: s.approvals}, .approved p r.sessionId)
    else (s, .rejected .unauthorized)
  | .adversary .wait => (s, .idle)
  | .adversary (.start r) =>
    if authorized c s r then
      if s.slots.length < c.maxAttempts then
        ({s with slots := s.slots ++ [⟨r, .pending⟩]}, .queued s.slots.length r)
      else (s, .rejected .exhausted)
    else (s, .rejected .unauthorized)
  | .adversary (.execute n) =>
    match s.slots[n]? with
    | none => (s, .rejected .absent)
    | some slot => match slot.phase with
      | .pending =>
        let result := release slot.request s.wal
        ({s with wal := result.1, slots := updateSlot s.slots n ⟨slot.request, .ready result.2⟩},
          .disclosed n result.2)
      | _ => (s, .rejected .wrongPhase)
  | .adversary (.deliver n) =>
    match s.slots[n]? with
    | none => (s, .rejected .absent)
    | some slot => match slot.phase with
      | .ready result =>
        ({s with slots := updateSlot s.slots n ⟨slot.request, .closed⟩},
          .delivered n slot.request result)
      | _ => (s, .rejected .wrongPhase)
  | .adversary (.abort n) =>
    match s.slots[n]? with
    | none => (s, .rejected .absent)
    | some slot =>
      ({s with slots := updateSlot s.slots n ⟨slot.request, .closed⟩},
        .rejected .adversarialAbort)

/-- Ideal computation uses the reference key/signature algorithm. The shared
adapter is an operational correctness comparison, NOT a participant simulator. -/
def ideal (c : Config) : InteractiveService.Machine Input Output State :=
  ⟨stepWith c (RssProduction.referenceRelease c.profile)⟩
def shared (c : Config) : InteractiveService.Machine Input Output State :=
  ⟨stepWith c (RssProduction.release c.profile)⟩

theorem shared_step_eq_ideal (c : Config) (s : State) (i : Input) :
    (shared c).step s i = (ideal c).step s i := by
  have h : RssProduction.release c.profile = RssProduction.referenceRelease c.profile := by
    funext r wal
    exact RssProduction.release_eq_reference c.profile r wal
  simp only [shared, ideal, h]

/-- Actual shared signer correctness survives arbitrary feedback and slot
interleaving at the service boundary. This does not hide its internal messages. -/
theorem shared_ideal_interactive_correctness (c : Config) :
    InteractiveService.PrefixEquivalent (shared c) (ideal c) (initial c) (initial c) := by
  apply InteractiveService.bisimulation_prefixEquivalent _ _ Eq
  · constructor
    intro s t h i
    subst t
    rw [shared_step_eq_ideal]
    exact ⟨rfl, rfl⟩
  · rfl

theorem adversary_preserves_approvals (c : Config) (release : Release)
    (s : State) (a : Schedule) :
    (stepWith c release s (.adversary a)).1.approvals = s.approvals := by
  cases a with
  | wait => rfl
  | start r => simp only [stepWith]; split <;> (try split) <;> rfl
  | execute n =>
    simp only [stepWith]
    split
    · rfl
    · split <;> rfl
  | deliver n =>
    simp only [stepWith]
    split
    · rfl
    · split <;> rfl
  | abort n => simp only [stepWith]; split <;> rfl

theorem authorized_requires_actual_input (c : Config) (s : State)
    (r : SessionScheduleReq) (h : authorized c s r = true) :
    ∀ p ∈ r.honestApprovers, (p, r) ∈ s.approvals := by
  have hp := of_decide_eq_true h
  intro p hm
  exact (hp.2.2.2.2.2.2.2.1 p hm).2.2

/-- No scheduling command can supply the missing honest approvals. -/
theorem empty_ledger_rejects (c : Config) (s : State) (h : s.approvals = [])
    (r : SessionScheduleReq) : authorized c s r = false := by
  cases he : authorized c s r with
  | false => rfl
  | true =>
    have hp := of_decide_eq_true he
    have hn := hp.2.2.2.2.2.1
    cases hr : r.honestApprovers with
    | nil => exact False.elim (hn hr)
    | cons p ps =>
      have hm := authorized_requires_actual_input c s r he p (by simp [hr])
      rw [h] at hm
      cases hm

/-- Delivery and abort are pure scheduling operations: neither rewinds the WAL. -/
theorem delivery_preserves_wal (c : Config) (release : Release) (s : State) (n : Nat) :
    (stepWith c release s (.adversary (.deliver n))).1.wal = s.wal := by
  simp only [stepWith]
  split
  · rfl
  · split <;> rfl

theorem abort_preserves_wal (c : Config) (release : Release) (s : State) (n : Nat) :
    (stepWith c release s (.adversary (.abort n))).1.wal = s.wal := by
  simp only [stepWith]
  split <;> rfl


/-- Concrete request fixture; the profile remains arbitrary and fixed. -/
@[expose] def fixtureRequest : SessionScheduleReq := ⟨7, 0, [11], [], [0]⟩
@[expose] def fixtureConfig (p : RssProduction.Profile) : Config := ⟨p, 3, 2, [2], 2⟩

/-- Positive reachability: an actual honest input enables a 2-of-3 request.
This exercises the authorization/scheduling boundary without asserting a
cryptographic property of arbitrary profile parameters. -/
theorem approved_request_can_start (p : RssProduction.Profile) (release : Release) :
    let c := fixtureConfig p
    let s := (stepWith c release (initial c) (.honest (.approve 0 fixtureRequest))).1
    (stepWith c release s (.adversary (.start fixtureRequest))).2 =
      .queued 0 fixtureRequest := by
  intro c s
  have hs : s = ⟨[(0, fixtureRequest)], [], RssProduction.initial p⟩ := by
    dsimp only [s, c, stepWith, initial, fixtureConfig]
    rw [ite_eq_left ⟨by decide, by decide⟩]
  rw [hs]
  have hAuth : authorized c ⟨[(0, fixtureRequest)], [], RssProduction.initial p⟩ fixtureRequest = true := by
    unfold authorized
    exact decide_eq_true (by
      dsimp only [c, fixtureConfig, fixtureRequest]
      refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_, by decide⟩
      intro q hq
      simp only [List.mem_singleton] at hq
      subst hq
      exact ⟨by decide, by decide, List.mem_singleton.mpr rfl⟩)
  dsimp only [stepWith]
  rw [ite_eq_left hAuth, ite_eq_left (by dsimp only [c, fixtureConfig]; decide)]
  rfl

/-- The same approval cannot be replayed to authorize changed randomness. -/
theorem approval_does_not_authorize_changed_request
    (p : RssProduction.Profile) (release : Release) :
    let c := fixtureConfig p
    let s := (stepWith c release (initial c) (.honest (.approve 0 fixtureRequest))).1
    (stepWith c release s
      (.adversary (.start { fixtureRequest with optRand := [1] }))).2 =
      .rejected .unauthorized := by
  intro c s
  have hs : s = ⟨[(0, fixtureRequest)], [], RssProduction.initial p⟩ := by
    dsimp only [s, c, stepWith, initial, fixtureConfig]
    rw [ite_eq_left ⟨by decide, by decide⟩]
  rw [hs]
  have hNotAuth : ¬ (authorized c ⟨[(0, fixtureRequest)], [], RssProduction.initial p⟩
      { fixtureRequest with optRand := [1] } = true) := by
    unfold authorized
    rw [decide_eq_true_iff]
    intro h
    have h0 := (h.2.2.2.2.2.2.2.1 0 (by simp [fixtureRequest])).2.2
    simp only [List.mem_singleton, Prod.mk.injEq] at h0
    have hOpt := congrArg SessionScheduleReq.optRand h0.2
    simp [fixtureRequest] at hOpt
  dsimp only [stepWith]
  rw [ite_eq_right hNotAuth]

/-- Honest authorization does not override the explicit attempt budget. -/
theorem exhausted_attempts_reject (p : RssProduction.Profile) (release : Release) :
    let c := { fixtureConfig p with maxAttempts := 0 }
    let s := (stepWith c release (initial c) (.honest (.approve 0 fixtureRequest))).1
    (stepWith c release s (.adversary (.start fixtureRequest))).2 =
      .rejected .exhausted := by
  intro c s
  have hs : s = ⟨[(0, fixtureRequest)], [], RssProduction.initial p⟩ := by
    dsimp only [s, c, stepWith, initial, fixtureConfig]
    rw [ite_eq_left ⟨by decide, by decide⟩]
  rw [hs]
  have hAuth : authorized c ⟨[(0, fixtureRequest)], [], RssProduction.initial p⟩ fixtureRequest = true := by
    unfold authorized
    exact decide_eq_true (by
      dsimp only [c, fixtureConfig, fixtureRequest]
      refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_, by decide⟩
      intro q hq
      simp only [List.mem_singleton] at hq
      subst hq
      exact ⟨by decide, by decide, List.mem_singleton.mpr rfl⟩)
  dsimp only [stepWith]
  rw [ite_eq_left hAuth, ite_eq_right (by dsimp only [c, fixtureConfig]; omega)]

theorem fixtureRequest_authorized (p : RssProduction.Profile) (w : WalLatchState) :
    authorized (fixtureConfig p) ⟨[(0, fixtureRequest)], [], w⟩ fixtureRequest = true := by
  unfold authorized
  exact decide_eq_true (by
    dsimp only [fixtureConfig, fixtureRequest]
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_, by decide⟩
    intro q hq
    simp only [List.mem_singleton] at hq
    subst hq
    exact ⟨by decide, by decide, List.mem_singleton.mpr rfl⟩)

end Qsag.ThresholdIdealService
