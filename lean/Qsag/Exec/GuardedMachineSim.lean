module

public import Qsag.Tactic.Prelude
public import Qsag.Exec.SimulationSpine
import Qsag.Tactic.AssuranceKit

/-!
# Qsag.Exec.GuardedMachineSim — one guard, one update, one rejection

The custody and signing guards of `Qsag.Exec.MirSpecBridgeCore` (§2 policy guard, §6A velocity
guard, §6B ML-DSA release gate, §6C belt latch kernel) all have one shape: a Boolean guard over
`(state, input)`; on success a state update and an output; otherwise a rejection that leaves
the state alone or poisons it. Each is written there as a chain of nested `if`s returning
`StepOutcome`, and each then proves by hand, with one `split` per `if`, what an accepted step
implies, what a rejected step does to the state, and an induction over `ValidTrace`.

`GuardedMachine` states that shape once.

* `GuardedMachine.Models`: an existing `PartyMachine` computes this guarded machine.
  `models_ofOutcome` and `models_ofOption` discharge it from one equation about the step function.
* `Models.trace_induction`: induction over the valid traces of the existing machine in which
  the accept case receives `guard s i = true` and the reject case `guard s i = false`, with the
  successor state and output already in guarded form.
* `Models.trace_invariant`: a state invariant kept by accepted and rejected steps holds at the
  end of every trace, and every accepted pair was produced under the guard from an invariant state.
* `Models.at_most_one_accept`: a guard that latches accepts at most once per trace.
* `GuardedMachineSim`: guard agreement, update and rejection preservation and output equality
  between two guarded machines. `toForwardSim` is the forward simulation,
  `lift_trace` and `trace_safety` carry traces and trace properties across it, and
  `Models.forwardSim` restates it between the two existing machines.
* `GuardedMachine.forwardSimTo`: the same for an abstract machine that is not guarded.
-/

public section

namespace Qsag.Exec.GuardedMachineSim

open Qsag

set_option autoImplicit false

/-- Guard, then update and emit; otherwise reject. `reject` defaults to leaving the state. -/
structure GuardedMachine (S In Out : Type) where
  guard : S → In → Bool
  next : S → In → S
  out : S → In → Out
  reject : S → In → S := fun s _ => s

variable {S In Out : Type}

/-- The canonical `PartyMachine` of a guarded machine. -/
@[expose] def GuardedMachine.toParty (G : GuardedMachine S In Out) : PartyMachine S In Out where
  step s i := if G.guard s i then some (G.next s i, G.out s i) else none
  errStep := G.reject

theorem GuardedMachine.step_accept (G : GuardedMachine S In Out) {s : S} {i : In}
    (h : G.guard s i = true) : G.toParty.step s i = some (G.next s i, G.out s i) := by
  show (if G.guard s i then some (G.next s i, G.out s i) else none) = _
  rw [h]; rfl

theorem GuardedMachine.step_reject (G : GuardedMachine S In Out) {s : S} {i : In}
    (h : G.guard s i = false) : G.toParty.step s i = none := by
  show (if G.guard s i then some (G.next s i, G.out s i) else none) = _
  rw [h]; rfl

theorem GuardedMachine.step_eq_some (G : GuardedMachine S In Out) {s s' : S} {i : In} {o : Out}
    (h : G.toParty.step s i = some (s', o)) :
    G.guard s i = true ∧ s' = G.next s i ∧ o = G.out s i := by
  cases hg : G.guard s i with
  | false => rw [G.step_reject hg] at h; cases h
  | true =>
    rw [G.step_accept hg] at h
    cases h
    exact ⟨rfl, rfl, rfl⟩

theorem GuardedMachine.step_eq_none (G : GuardedMachine S In Out) {s : S} {i : In}
    (h : G.toParty.step s i = none) : G.guard s i = false := by
  cases hg : G.guard s i with
  | false => rfl
  | true => rw [G.step_accept hg] at h; cases h

/-- `M` computes `G`: same accepted steps, and `G.reject` on every rejected input. `errStep` is
    left free on accepted inputs, where no trace consults it (`PartyMachine.ofOutcome` returns
    the successor there, `PartyMachine.ofOption` the old state). -/
structure GuardedMachine.Models (G : GuardedMachine S In Out) (M : PartyMachine S In Out) :
    Prop where
  step_eq : ∀ s i, M.step s i = G.toParty.step s i
  reject_eq : ∀ s i, G.guard s i = false → M.errStep s i = G.reject s i

theorem GuardedMachine.models_self (G : GuardedMachine S In Out) : G.Models G.toParty :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- A `StepOutcome` function that is `ok` under the guard and `err` at `G.reject` otherwise. -/
theorem GuardedMachine.models_ofOutcome {Err : Type} (G : GuardedMachine S In Out)
    (f : S → In → StepOutcome S Out Err) (e : S → In → Err)
    (hf : ∀ s i, f s i =
      if G.guard s i then .ok (G.next s i) (G.out s i) else .err (G.reject s i) (e s i)) :
    G.Models (PartyMachine.ofOutcome f) := by
  constructor
  · intro s i
    show (match f s i with | .ok s' out => some (s', out) | .err _ _ => none) = G.toParty.step s i
    rw [hf s i]
    cases hg : G.guard s i with
    | false => rw [G.step_reject hg]; rfl
    | true => rw [G.step_accept hg]; rfl
  · intro s i hg
    show (match f s i with | .ok s' _ => s' | .err s' _ => s') = G.reject s i
    rw [hf s i, hg]; rfl

/-- A partial step function that is `some` under the guard; rejection leaves the state. -/
theorem GuardedMachine.models_ofOption (G : GuardedMachine S In Out)
    (f : S → In → Option (S × Out))
    (hf : ∀ s i, f s i = if G.guard s i then some (G.next s i, G.out s i) else none)
    (hr : ∀ s i, G.guard s i = false → G.reject s i = s) :
    G.Models (PartyMachine.ofOption f) :=
  ⟨fun s i => hf s i, fun s i hg => (hr s i hg).symm⟩

namespace GuardedMachine.Models

variable {G : GuardedMachine S In Out} {M : PartyMachine S In Out}

theorem accepted (hM : G.Models M) {s s' : S} {i : In} {o : Out}
    (h : M.step s i = some (s', o)) : G.guard s i = true ∧ s' = G.next s i ∧ o = G.out s i :=
  G.step_eq_some ((hM.step_eq s i).symm.trans h)

theorem rejected (hM : G.Models M) {s : S} {i : In} (h : M.step s i = none) :
    G.guard s i = false ∧ M.errStep s i = G.reject s i :=
  have hg := G.step_eq_none ((hM.step_eq s i).symm.trans h)
  ⟨hg, hM.reject_eq s i hg⟩

theorem step_of_guard (hM : G.Models M) {s : S} {i : In} (h : G.guard s i = true) :
    M.step s i = some (G.next s i, G.out s i) :=
  (hM.step_eq s i).trans (G.step_accept h)

theorem none_of_guard (hM : G.Models M) {s : S} {i : In} (h : G.guard s i = false) :
    M.step s i = none :=
  (hM.step_eq s i).trans (G.step_reject h)

/-- **Trace induction in guarded form.** -/
theorem trace_induction (hM : G.Models M) {motive : S → List (In × Out) → S → Prop}
    (nil : ∀ s, motive s [] s)
    (accept : ∀ s i rest sF, G.guard s i = true → M.ValidTrace (G.next s i) rest sF →
      motive (G.next s i) rest sF → motive s ((i, G.out s i) :: rest) sF)
    (reject : ∀ s i rest sF, G.guard s i = false → M.ValidTrace (G.reject s i) rest sF →
      motive (G.reject s i) rest sF → motive s rest sF)
    {s sF : S} {tr : List (In × Out)} (h : M.ValidTrace s tr sF) : motive s tr sF := by
  induction h with
  | nil s => exact nil s
  | accept hStep hTail ih =>
    obtain ⟨hg, rfl, rfl⟩ := hM.accepted hStep
    exact accept _ _ _ _ hg hTail ih
  | reject inp hNone hTail ih =>
    obtain ⟨hg, he⟩ := hM.rejected hNone
    rw [he] at hTail ih
    exact reject _ inp _ _ hg hTail ih

/-- **Trace safety.** An invariant kept by every accepted and every rejected step holds at the
    end, and each accepted pair was emitted under the guard from a state satisfying it. -/
theorem trace_invariant (hM : G.Models M) (Inv : S → Prop)
    (hAcc : ∀ s i, Inv s → G.guard s i = true → Inv (G.next s i))
    (hRej : ∀ s i, Inv s → G.guard s i = false → Inv (G.reject s i))
    {s sF : S} {tr : List (In × Out)} (h : M.ValidTrace s tr sF) (hInv : Inv s) :
    Inv sF ∧ ∀ p ∈ tr, ∃ s₁, Inv s₁ ∧ G.guard s₁ p.1 = true ∧ p.2 = G.out s₁ p.1 := by
  revert hInv
  refine hM.trace_induction
    (motive := fun s tr sF => Inv s →
      Inv sF ∧ ∀ p ∈ tr, ∃ s₁, Inv s₁ ∧ G.guard s₁ p.1 = true ∧ p.2 = G.out s₁ p.1)
    ?_ ?_ ?_ h
  · intro s hs
    exact ⟨hs, fun p hp => absurd hp List.not_mem_nil⟩
  · intro s i rest sF hg _ ih hs
    obtain ⟨hF, hAll⟩ := ih (hAcc s i hs hg)
    refine ⟨hF, fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨s, hs, hg, rfl⟩
    · exact hAll p hp
  · intro s i rest sF hg _ ih hs
    exact ih (hRej s i hs hg)

/-- **Latching guards accept at most once.** `Dead` holds after any accepted step, blocks the
    guard, and survives rejection. -/
theorem at_most_one_accept (hM : G.Models M) (Dead : S → Prop)
    (hLatch : ∀ s i, G.guard s i = true → Dead (G.next s i))
    (hBlock : ∀ s i, Dead s → G.guard s i = false)
    (hKeep : ∀ s i, Dead s → Dead (G.reject s i))
    {s sF : S} {tr : List (In × Out)} (h : M.ValidTrace s tr sF) : tr.length ≤ 1 := by
  have hDead : ∀ {s sF : S} {tr : List (In × Out)}, M.ValidTrace s tr sF → Dead s → tr = [] := by
    intro s sF tr h
    refine hM.trace_induction (motive := fun s tr _ => Dead s → tr = []) ?_ ?_ ?_ h
    · intro _ _; rfl
    · intro s i rest sF hg _ _ hd
      rw [hBlock s i hd] at hg; cases hg
    · intro s i rest sF _ _ ih hd
      exact ih (hKeep s i hd)
  refine hM.trace_induction (motive := fun _ tr _ => tr.length ≤ 1) ?_ ?_ ?_ h
  · intro _; exact Nat.zero_le 1
  · intro s i rest sF hg hTail _
    rw [hDead hTail (hLatch s i hg)]
    exact Nat.le_refl 1
  · intro s i rest sF _ _ ih
    exact ih

end GuardedMachine.Models

/-! ## Forward simulation -/

/-- Guard agreement, update and rejection preservation, output equality. -/
structure GuardedMachineSim {Sc Sa : Type} (C : GuardedMachine Sc In Out)
    (A : GuardedMachine Sa In Out) : Type 1 where
  Rel : Sc → Sa → Prop
  guard_eq : ∀ {c a} (i : In), Rel c a → C.guard c i = A.guard a i
  next_rel : ∀ {c a} (i : In), Rel c a → C.guard c i = true → Rel (C.next c i) (A.next a i)
  out_eq : ∀ {c a} (i : In), Rel c a → C.guard c i = true → C.out c i = A.out a i
  reject_rel : ∀ {c a} (i : In), Rel c a → C.guard c i = false →
    Rel (C.reject c i) (A.reject a i)

namespace GuardedMachineSim

variable {Sc Sa : Type} {C : GuardedMachine Sc In Out} {A : GuardedMachine Sa In Out}

/-- **The forward simulation**, between any two machines that compute `C` and `A`. -/
def forwardSim (sim : GuardedMachineSim C A) {MC : PartyMachine Sc In Out}
    {MA : PartyMachine Sa In Out} (hC : C.Models MC) (hA : A.Models MA) : ForwardSim MC MA where
  Rel := sim.Rel
  sim_ok {c c' a inp out} hRel hStep := by
    obtain ⟨hg, rfl, rfl⟩ := hC.accepted hStep
    rw [hA.step_of_guard ((sim.guard_eq inp hRel).symm.trans hg)]
    exact ⟨(sim.out_eq inp hRel hg).symm, sim.next_rel inp hRel hg⟩
  sim_err {c a inp} hRel hNone := by
    obtain ⟨hg, he⟩ := hC.rejected hNone
    have hga : A.guard a inp = false := (sim.guard_eq inp hRel).symm.trans hg
    refine ⟨hA.none_of_guard hga, ?_⟩
    rw [he, hA.reject_eq a inp hga]
    exact sim.reject_rel inp hRel hg

def toForwardSim (sim : GuardedMachineSim C A) : ForwardSim C.toParty A.toParty :=
  sim.forwardSim C.models_self A.models_self

/-- Every concrete trace is an abstract trace with the same accepted pairs. -/
theorem lift_trace (sim : GuardedMachineSim C A) {MC : PartyMachine Sc In Out}
    {MA : PartyMachine Sa In Out} (hC : C.Models MC) (hA : A.Models MA)
    {c cF : Sc} {a : Sa} {tr : List (In × Out)} (hRel : sim.Rel c a)
    (hTr : MC.ValidTrace c tr cF) : ∃ aF, MA.ValidTrace a tr aF ∧ sim.Rel cF aF :=
  (sim.forwardSim hC hA).lift_validTrace hRel hTr

/-- **Trace safety across the simulation.** -/
theorem trace_safety (sim : GuardedMachineSim C A) {MC : PartyMachine Sc In Out}
    {MA : PartyMachine Sa In Out} (hC : C.Models MC) (hA : A.Models MA)
    {Safe : List (In × Out) → Prop} {c cF : Sc} {a : Sa} {tr : List (In × Out)}
    (hRel : sim.Rel c a)
    (hSafe : ∀ (tr' : List (In × Out)) (aF : Sa), MA.ValidTrace a tr' aF → Safe tr')
    (hTr : MC.ValidTrace c tr cF) : Safe tr := by
  obtain ⟨aF, hA', _⟩ := sim.lift_trace hC hA hRel hTr
  exact hSafe tr aF hA'

end GuardedMachineSim

/-- Forward simulation from a guarded machine into any abstract machine: accepted steps are
    matched with the same output, rejected steps are rejected. -/
def GuardedMachine.forwardSimTo {Sc Sa : Type} (C : GuardedMachine Sc In Out)
    {MC : PartyMachine Sc In Out} (hC : C.Models MC) (A : PartyMachine Sa In Out)
    (Rel : Sc → Sa → Prop)
    (hAcc : ∀ {c a} (i : In), Rel c a → C.guard c i = true →
      ∃ a', A.step a i = some (a', C.out c i) ∧ Rel (C.next c i) a')
    (hRej : ∀ {c a} (i : In), Rel c a → C.guard c i = false →
      A.step a i = none ∧ Rel (C.reject c i) (A.errStep a i)) : ForwardSim MC A where
  Rel := Rel
  sim_ok {c c' a inp out} hRel hStep := by
    obtain ⟨hg, rfl, rfl⟩ := hC.accepted hStep
    obtain ⟨a', hA, hR⟩ := hAcc inp hRel hg
    rw [hA]
    exact ⟨rfl, hR⟩
  sim_err {c a inp} hRel hNone := by
    obtain ⟨hg, he⟩ := hC.rejected hNone
    obtain ⟨hA, hR⟩ := hRej inp hRel hg
    rw [he]
    exact ⟨hA, hR⟩

#verify_constructive GuardedMachine.step_eq_some GuardedMachine.step_eq_none
#verify_constructive GuardedMachine.models_ofOutcome GuardedMachine.models_ofOption
#verify_constructive GuardedMachine.Models.trace_induction GuardedMachine.Models.trace_invariant
#verify_constructive GuardedMachine.Models.at_most_one_accept
#verify_constructive GuardedMachineSim.lift_trace GuardedMachineSim.trace_safety

end Qsag.Exec.GuardedMachineSim
