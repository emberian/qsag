module
public import Qsag.Exec.ThresholdIdealService
public import Qsag.Exec.RssProductionProfile

public section
namespace Qsag.ThresholdIdealDurableService
set_option autoImplicit false
open ThresholdIdealService (Config HonestInput Output Rejection)

inductive Command where
  | honest (input : HonestInput)
  | wait
  | start (request : SessionScheduleReq)
  | execute (slot : Nat)
  | commit (slot : Nat)
  | deliver (slot : Nat)
  | abort (slot : Nat)
  | crash

inductive Phase where
  | reserved
  | replay (bytes : List UInt8)
  | buffered (result : Except RssProduction.Failure (List UInt8))
  | committed (result : Except RssProduction.Failure (List UInt8))
  | closed

structure Slot where
  request : SessionScheduleReq
  phase : Phase

/-- Reservations and cache are durable. Slots are volatile continuations.
Already emitted outputs live in the environment and cannot be erased by crash. -/
structure State where
  approvals : List (Nat × SessionScheduleReq)
  nextLeaf : Nat
  reserved : List SessionScheduleReq
  cached : List (SessionScheduleReq × List UInt8)
  slots : List Slot

def initial : State := ⟨[], 0, [], [], []⟩

def approvalState (c : Config) (s : State) : ThresholdIdealService.State :=
  ⟨s.approvals, [], RssProduction.initial c.profile⟩

def update : List Slot → Nat → Slot → List Slot
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | x :: xs, n + 1, v => x :: update xs n v

def close (slot : Slot) : Slot := ⟨slot.request, .closed⟩

abbrev Compute := SessionScheduleReq → Except RssProduction.Failure (List UInt8)

/-- A reservation is committed before the first protocol output. A signature
may be disclosed before cache commit; crashing then loses the retry result but
never recycles the signing leaf. Exact committed retries bypass computation.
This is an authenticated monotone storage HYBRID, not its POSIX realization. -/
def stepWith (c : Config) (compute : Compute) (s : State) : Command → State × Output
  | .honest (.approve p req) =>
    if p < c.parties ∧ p ∉ c.corrupt then
      ({s with approvals := (p,req) :: s.approvals}, .approved p req.sessionId)
    else (s, .rejected .unauthorized)
  | .wait => (s, .idle)
  | .start req =>
    if ThresholdIdealService.authorized c (approvalState c s) req then
      if s.slots.length < c.maxAttempts then
        match s.cached.find? (fun pair => decide (pair.1 = req)) with
        | some pair =>
          ({s with slots := s.slots ++ [⟨req, .replay pair.2⟩]}, .queued s.slots.length req)
        | none =>
          if req.reqEpoch = s.nextLeaf then
            ({s with nextLeaf := s.nextLeaf + 1, reserved := req :: s.reserved, slots := s.slots ++ [⟨req, .reserved⟩]}, .queued s.slots.length req)
          else (s, .rejected .wrongPhase)
      else (s, .rejected .exhausted)
    else (s, .rejected .unauthorized)
  | .execute n =>
    match s.slots[n]? with
    | none => (s, .rejected .absent)
    | some slot => match slot.phase with
      | .reserved =>
        let result := compute slot.request
        ({s with slots := update s.slots n ⟨slot.request, .buffered result⟩}, .disclosed n result)
      | .replay bytes =>
        ({s with slots := update s.slots n ⟨slot.request, .committed (.ok bytes)⟩},
          .disclosed n (.ok bytes))
      | _ => (s, .rejected .wrongPhase)
  | .commit n =>
    match s.slots[n]? with
    | none => (s, .rejected .absent)
    | some slot => match slot.phase with
      | .buffered result =>
        let cache := match result with
          | .error _ => s.cached
          | .ok bytes => (slot.request,bytes) :: s.cached
        ({s with cached := cache, slots := update s.slots n ⟨slot.request, .committed result⟩}, .idle)
      | _ => (s, .rejected .wrongPhase)
  | .deliver n =>
    match s.slots[n]? with
    | none => (s, .rejected .absent)
    | some slot => match slot.phase with
      | .committed result =>
        ({s with slots := update s.slots n (close slot)}, .delivered n slot.request result)
      | _ => (s, .rejected .wrongPhase)
  | .abort n =>
    match s.slots[n]? with
    | none => (s, .rejected .absent)
    | some slot => ({s with slots := update s.slots n (close slot)}, .rejected .adversarialAbort)
  | .crash => ({s with slots := s.slots.map close}, .idle)

def ideal (c : Config) : InteractiveService.Machine Command Output State :=
  ⟨stepWith c (RssProduction.referenceOutput c.profile)⟩
def shared (c : Config) : InteractiveService.Machine Command Output State :=
  ⟨stepWith c (RssProduction.partialOutput c.profile)⟩

theorem shared_step_eq_ideal (c : Config) (s : State) (i : Command) :
    (shared c).step s i = (ideal c).step s i := by
  have h : RssProduction.partialOutput c.profile = RssProduction.referenceOutput c.profile := by
    funext req
    exact RssProduction.partialOutput_eq_reference c.profile req
  simp only [shared, ideal, h]

/-- Correctness survives arbitrary environment feedback, interleaved requests,
crashes between observation/commit/return, and exact committed retries. Internal
participant transcript privacy is a distinct obligation. -/
theorem shared_ideal_interactive_correctness (c : Config) :
    InteractiveService.PrefixEquivalent (shared c) (ideal c) initial initial := by
  apply InteractiveService.bisimulation_prefixEquivalent _ _ Eq
  · constructor
    intro s t h i
    subst t
    rw [shared_step_eq_ideal]
    exact ⟨rfl,rfl⟩
  · rfl

theorem crash_preserves_durable (c : Config) (compute : Compute) (s : State) :
    (stepWith c compute s .crash).1.nextLeaf = s.nextLeaf ∧
    (stepWith c compute s .crash).1.reserved = s.reserved ∧
    (stepWith c compute s .crash).1.cached = s.cached ∧
    (stepWith c compute s .crash).1.approvals = s.approvals := ⟨rfl,rfl,rfl,rfl⟩

theorem abort_preserves_durable (c : Config) (compute : Compute) (s : State) (n : Nat) :
    (stepWith c compute s (.abort n)).1.nextLeaf = s.nextLeaf ∧
    (stepWith c compute s (.abort n)).1.reserved = s.reserved ∧
    (stepWith c compute s (.abort n)).1.cached = s.cached := by
  simp only [stepWith]
  split <;> exact ⟨rfl,rfl,rfl⟩

/-- Positive boundary witness: the actual honest request reserves leaf zero
before any call of the signing computation, even if immediately crashed. -/
theorem start_then_crash_burns (p : RssProduction.Profile) (compute : Compute) :
    let c := ThresholdIdealService.fixtureConfig p
    let req := ThresholdIdealService.fixtureRequest
    let s := (stepWith c compute initial (.honest (.approve 0 req))).1
    let reserved := (stepWith c compute s (.start req)).1
    (stepWith c compute reserved .crash).1.nextLeaf = 1 ∧
      (stepWith c compute reserved .crash).1.reserved = [req] := by
  intro c req s reserved
  have hs : s = ⟨[(0, req)], 0, [], [], []⟩ := by
    dsimp only [s, c, req, stepWith, initial, ThresholdIdealService.fixtureConfig]
    rw [ite_eq_left ⟨by decide, by decide⟩]
  have hAuth : ThresholdIdealService.authorized c (approvalState c s) req = true := by
    rw [hs]
    exact ThresholdIdealService.fixtureRequest_authorized p (RssProduction.initial p)
  have hRes : reserved = ⟨[(0, req)], 1, [req], [], [⟨req, .reserved⟩]⟩ := by
    dsimp only [reserved]
    rw [hs]
    dsimp only [stepWith]
    rw [ite_eq_left (ThresholdIdealService.fixtureRequest_authorized p (RssProduction.initial p))]
    rw [ite_eq_left (by dsimp only [c, ThresholdIdealService.fixtureConfig]; decide)]
    dsimp only [List.find?]
    rw [ite_eq_left (by dsimp only [req, ThresholdIdealService.fixtureRequest])]
  rw [hRes]
  exact ⟨rfl, rfl⟩

/-- A successful signature cannot be returned before durable caching. -/
theorem buffered_not_deliverable (c : Config) (compute : Compute)
    (req : SessionScheduleReq) (raw : List UInt8) (s : State)
    (h : s.slots = [⟨req, .buffered (.ok raw)⟩]) :
    (stepWith c compute s (.deliver 0)).2 = .rejected .wrongPhase := by
  simp [stepWith, h]

/-- Crash after disclosure but before commit loses the volatile result while
retaining its reservation; prior environment output is not undone. -/
theorem disclosed_uncommitted_not_cached (c : Config) (compute : Compute)
    (req : SessionScheduleReq) (s : State)
    (h : s.slots = [⟨req, .reserved⟩]) :
    (stepWith c compute (stepWith c compute s (.execute 0)).1 .crash).1.cached = s.cached := by
  simp [stepWith, h]

/-- A crash cannot make an uncommitted reserved leaf available again. -/
theorem crash_cannot_reuse_reserved_leaf (p : RssProduction.Profile) (compute : Compute) :
    let c := ThresholdIdealService.fixtureConfig p
    let req := ThresholdIdealService.fixtureRequest
    let s := (stepWith c compute initial (.honest (.approve 0 req))).1
    let reserved := (stepWith c compute s (.start req)).1
    let crashed := (stepWith c compute reserved .crash).1
    (stepWith c compute crashed (.start req)).2 = .rejected .wrongPhase := by
  intro c req s reserved crashed
  have hs : s = ⟨[(0, req)], 0, [], [], []⟩ := by
    dsimp only [s, c, req, stepWith, initial, ThresholdIdealService.fixtureConfig]
    rw [ite_eq_left ⟨by decide, by decide⟩]
  have hRes : reserved = ⟨[(0, req)], 1, [req], [], [⟨req, .reserved⟩]⟩ := by
    dsimp only [reserved]
    rw [hs]
    dsimp only [stepWith]
    rw [ite_eq_left (ThresholdIdealService.fixtureRequest_authorized p (RssProduction.initial p))]
    rw [ite_eq_left (by dsimp only [c, ThresholdIdealService.fixtureConfig]; decide)]
    dsimp only [List.find?]
    rw [ite_eq_left (by dsimp only [req, ThresholdIdealService.fixtureRequest])]
  have hCrash : crashed = ⟨[(0, req)], 1, [req], [], [⟨req, .closed⟩]⟩ := by
    dsimp only [crashed]
    rw [hRes]
    rfl
  rw [hCrash]
  dsimp only [stepWith]
  rw [ite_eq_left (ThresholdIdealService.fixtureRequest_authorized p (RssProduction.initial p))]
  rw [ite_eq_left (by dsimp only [c, ThresholdIdealService.fixtureConfig]; decide)]
  dsimp only [List.find?]
  rw [ite_eq_right (by dsimp only [req, ThresholdIdealService.fixtureRequest]; decide)]

/-- Retry execution is independent of the signing algorithm and its coins. -/
theorem replay_does_not_recompute (c : Config) (first second : Compute)
    (s : State) (req : SessionScheduleReq) (raw : List UInt8)
    (h : s.slots = [⟨req, .replay raw⟩]) :
    stepWith c first s (.execute 0) = stepWith c second s (.execute 0) := by
  simp [stepWith, h]

#verify_constructive shared_step_eq_ideal shared_ideal_interactive_correctness
  crash_preserves_durable abort_preserves_durable start_then_crash_burns
  buffered_not_deliverable disclosed_uncommitted_not_cached
  crash_cannot_reuse_reserved_leaf replay_does_not_recompute

end Qsag.ThresholdIdealDurableService
