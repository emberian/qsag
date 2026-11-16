module
public import Qsag.Exec.RssSigningControl
public import Qsag.Exec.RssSigningProgram
import Qsag.Tactic.AssuranceKit

/-!
Resumable public signer controller. A request index is consumed before issuing a
cut request and never rolls back on abort. A reply port is intended for the actual
active-check/commit-open resource, not directly for the adversary. This controller
does not assert that arbitrary bytes arriving at that port are valid or secret-
independently simulatable. Its honest-reply semantics refines the original signer.
-/
public section
namespace Qsag.RssSigning
set_option autoImplicit false

inductive Phase (α : Type) where
  | ready (program : Program α)
  | waiting (index : Nat) (query : Query) (next : Bytes → Program α)
  | finished (result : α)
  | aborted

structure State (α : Type) where
  nextCut : Nat
  phase : Phase α

inductive Input where
  | advance
  | reply (index : Nat) (bytes : Bytes)
  | abort
  deriving DecidableEq, Repr

inductive Output (α : Type) where
  | request (index : Nat) (query : Query)
  | resumed
  | finished (result : α)
  | aborted
  deriving DecidableEq, Repr

@[expose] def initial {α : Type} (program : Program α) (firstCut : Nat := 0) : State α :=
  ⟨firstCut, .ready program⟩

@[expose] def step {α : Type} (state : State α) (input : Input) : State α × Output α :=
  match input, state.phase with
  | .advance, .ready (.pure result) =>
      (⟨state.nextCut, .finished result⟩, .finished result)
  | .advance, .ready (.query query next) =>
      (⟨state.nextCut + 1, .waiting state.nextCut query next⟩, .request state.nextCut query)
  | .reply index bytes, .waiting expected _ next =>
      if index = expected then (⟨state.nextCut, .ready (next bytes)⟩, .resumed)
      else (⟨state.nextCut, .aborted⟩, .aborted)
  | _, _ => (⟨state.nextCut, .aborted⟩, .aborted)

/-- External reference meaning for a controller state; the controller itself
never receives this oracle or computes the reference interpretation. -/
@[expose] def meaning {α : Type} (o : ProductionPqHashMpcOracles) (state : State α) : Option α :=
  match state.phase with
  | .ready program => some (evaluate o program)
  | .waiting _ query next => some (evaluate o (next (answer o query)))
  | .finished result => some result
  | .aborted => none

theorem advance_refines {α : Type} (o : ProductionPqHashMpcOracles)
    (state : State α) (program : Program α) (h : state.phase = .ready program) :
    meaning o (step state .advance).1 = meaning o state := by
  cases program with
  | pure result => simp [step, meaning, h, evaluate, evalOracleComp]
  | query query next => simp [step, meaning, h, evaluate, evalOracleComp]

theorem honest_reply_refines {α : Type} (o : ProductionPqHashMpcOracles)
    (state : State α) (index : Nat) (query : Query) (next : Bytes → Program α)
    (h : state.phase = .waiting index query next) :
    meaning o (step state (.reply index (answer o query))).1 = meaning o state := by
  simp [step, meaning, h]

theorem request_burns_index {α : Type} (state : State α) (query : Query)
    (next : Bytes → Program α) (h : state.phase = .ready (.query query next)) :
    (step state .advance).1.nextCut = state.nextCut + 1 ∧
    (step state .advance).2 = .request state.nextCut query := by
  simp [step, h]

theorem wrong_reply_aborts {α : Type} (state : State α) (expected index : Nat)
    (query : Query) (next : Bytes → Program α) (bytes : Bytes)
    (h : state.phase = .waiting expected query next) (hne : index ≠ expected) :
    (step state (.reply index bytes)).1.phase = .aborted ∧
    (step state (.reply index bytes)).1.nextCut = state.nextCut := by
  simp [step, h, hne]

theorem abort_retains_index {α : Type} (state : State α) :
    (step state .abort).1.nextCut = state.nextCut ∧
    (step state .abort).1.phase = .aborted := by
  cases state.phase <;> simp [step]

theorem step_counter_monotone {α : Type} (state : State α) (input : Input) :
    state.nextCut ≤ (step state input).1.nextCut := by
  cases input <;> cases hp : state.phase <;> simp only [step, hp]
  all_goals first | exact Nat.le_refl _ | (split <;> simp) | (cases ‹Program α› <;> simp)

#verify_constructive advance_refines honest_reply_refines request_burns_index
  wrong_reply_aborts abort_retains_index step_counter_monotone
end Qsag.RssSigning
