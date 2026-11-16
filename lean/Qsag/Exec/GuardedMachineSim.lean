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

/-! ## Composable Guard Algebra: Lenses (`zoom`), Input Adapters (`comapIn`), Sequential Chains (`seq`) & Products (`prod`) -/

/-- State lens focusing a composite state `S` onto a local guard slice `Sub`. -/
structure Lens (S Sub : Type) where
  get : S → Sub
  set : S → Sub → S

/-- Standard Get-Put, Put-Get, and Put-Put lens laws. -/
structure Lens.Lawful {S Sub : Type} (L : Lens S Sub) : Prop where
  get_set : ∀ (s : S) (g : Sub), L.get (L.set s g) = g
  set_get : ∀ (s : S), L.set s (L.get s) = s
  set_set : ∀ (s : S) (g₁ g₂ : Sub), L.set (L.set s g₁) g₂ = L.set s g₂

/-- Identity lens on `S`. -/
def Lens.id (S : Type) : Lens S S where
  get s := s
  set _ s' := s'

theorem Lens.lawful_id (S : Type) : (Lens.id S).Lawful :=
  ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-- Vertical lens composition focusing `S` through `Mid` onto `Sub`. -/
def Lens.comp {S Mid Sub : Type} (L₁ : Lens S Mid) (L₂ : Lens Mid Sub) : Lens S Sub where
  get s := L₂.get (L₁.get s)
  set s g := L₁.set s (L₂.set (L₁.get s) g)

theorem Lens.lawful_comp {S Mid Sub : Type} {L₁ : Lens S Mid} {L₂ : Lens Mid Sub}
    (h₁ : L₁.Lawful) (h₂ : L₂.Lawful) : (L₁.comp L₂).Lawful where
  get_set s g := by
    show L₂.get (L₁.get (L₁.set s (L₂.set (L₁.get s) g))) = g
    rw [h₁.get_set, h₂.get_set]
  set_get s := by
    show L₁.set s (L₂.set (L₁.get s) (L₂.get (L₁.get s))) = s
    rw [h₂.set_get, h₁.set_get]
  set_set s g₁ g₂ := by
    show L₁.set (L₁.set s (L₂.set (L₁.get s) g₁))
      (L₂.set (L₁.get (L₁.set s (L₂.set (L₁.get s) g₁))) g₂) =
      L₁.set s (L₂.set (L₁.get s) g₂)
    rw [h₁.get_set, h₂.set_set, h₁.set_set]

/-- First-projection lens on `S₁ × S₂`. -/
def Lens.fst (S₁ S₂ : Type) : Lens (S₁ × S₂) S₁ where
  get p := p.1
  set p x := (x, p.2)

theorem Lens.lawful_fst (S₁ S₂ : Type) : (Lens.fst S₁ S₂).Lawful :=
  ⟨fun _ _ => rfl, fun ⟨_, _⟩ => rfl, fun _ _ _ => rfl⟩

/-- Second-projection lens on `S₁ × S₂`. -/
def Lens.snd (S₁ S₂ : Type) : Lens (S₁ × S₂) S₂ where
  get p := p.2
  set p y := (p.1, y)

theorem Lens.lawful_snd (S₁ S₂ : Type) : (Lens.snd S₁ S₂).Lawful :=
  ⟨fun _ _ => rfl, fun ⟨_, _⟩ => rfl, fun _ _ _ => rfl⟩

/-- **Lens Zoom (`GuardedMachine.zoom`)**:
    Lift a slice guard `G : GuardedMachine Sub In Out` onto composite state `S` via `L`,
    preserving all frame components outside `L` on both accepted and rejected turns. -/
@[expose] def GuardedMachine.zoom {S Sub In Out : Type}
    (L : Lens S Sub) (G : GuardedMachine Sub In Out) : GuardedMachine S In Out where
  guard s i := G.guard (L.get s) i
  next s i := L.set s (G.next (L.get s) i)
  out s i := G.out (L.get s) i
  reject s i := L.set s (G.reject (L.get s) i)

/-- Any frame predicate preserved by `L.set` survives arbitrary traces of `G.zoom L`. -/
theorem GuardedMachine.zoom_frame_trace {S Sub In Out : Type}
    (L : Lens S Sub) (G : GuardedMachine Sub In Out)
    (Frame : S → Prop) (hFrame : ∀ (s : S) (g : Sub), Frame s → Frame (L.set s g))
    {s sF : S} {tr : List (In × Out)}
    (hTr : (G.zoom L).toParty.ValidTrace s tr sF) (h₀ : Frame s) : Frame sF :=
  ((G.zoom L).models_self.trace_invariant Frame
    (fun s i hs _ => hFrame s (G.next (L.get s) i) hs)
    (fun s i hs _ => hFrame s (G.reject (L.get s) i) hs)
    hTr h₀).1

/-- Under `L.Lawful`, every valid trace of `G.zoom L` projects to a valid trace of `G`! -/
theorem GuardedMachine.zoom_proj_trace {S Sub In Out : Type}
    {L : Lens S Sub} (hL : L.Lawful) (G : GuardedMachine Sub In Out)
    {s sF : S} {tr : List (In × Out)}
    (hTr : (G.zoom L).toParty.ValidTrace s tr sF) :
    G.toParty.ValidTrace (L.get s) tr (L.get sF) := by
  refine (G.zoom L).models_self.trace_induction
    (motive := fun s tr sF => G.toParty.ValidTrace (L.get s) tr (L.get sF))
    ?_ ?_ ?_ hTr
  · intro s
    exact .nil (L.get s)
  · intro s i rest sF hg _ ih
    have hgSub : G.guard (L.get s) i = true := hg
    show G.toParty.ValidTrace (L.get s) ((i, G.out (L.get s) i) :: rest) (L.get sF)
    have ih' : G.toParty.ValidTrace (G.next (L.get s) i) rest (L.get sF) := by
      have hGet : L.get (L.set s (G.next (L.get s) i)) = G.next (L.get s) i :=
        hL.get_set s (G.next (L.get s) i)
      exact hGet ▸ ih
    exact .accept (G.step_accept hgSub) ih'
  · intro s i rest sF hg _ ih
    have hgSub : G.guard (L.get s) i = false := hg
    have ih' : G.toParty.ValidTrace (G.reject (L.get s) i) rest (L.get sF) := by
      have hGet : L.get (L.set s (G.reject (L.get s) i)) = G.reject (L.get s) i :=
        hL.get_set s (G.reject (L.get s) i)
      exact hGet ▸ ih
    exact .reject i (G.step_reject hgSub) ih'

/-- Lift a `GuardedMachineSim` across lenses paired with a relational frame invariant. -/
def GuardedMachineSim.zoom {Sc Sa SubC SubA In Out : Type}
    {C : GuardedMachine SubC In Out} {A : GuardedMachine SubA In Out}
    (sim : GuardedMachineSim C A)
    (Lc : Lens Sc SubC) (La : Lens Sa SubA)
    (FrameRel : Sc → Sa → Prop)
    (hFrameSet : ∀ {c : Sc} {a : Sa} (gc : SubC) (ga : SubA),
      FrameRel c a → FrameRel (Lc.set c gc) (La.set a ga))
    (hLc : Lc.Lawful) (hLa : La.Lawful) :
    GuardedMachineSim (C.zoom Lc) (A.zoom La) where
  Rel c a := FrameRel c a ∧ sim.Rel (Lc.get c) (La.get a)
  guard_eq i hR := sim.guard_eq i hR.2
  next_rel i hR hg := by
    refine ⟨hFrameSet _ _ hR.1, ?_⟩
    dsimp only [GuardedMachine.zoom]
    rw [hLc.get_set, hLa.get_set]
    exact sim.next_rel i hR.2 hg
  out_eq i hR hg := sim.out_eq i hR.2 hg
  reject_rel i hR hg := by
    refine ⟨hFrameSet _ _ hR.1, ?_⟩
    dsimp only [GuardedMachine.zoom]
    rw [hLc.get_set, hLa.get_set]
    exact sim.reject_rel i hR.2 hg

/-- Contravariant input projection for `GuardedMachine`. -/
@[expose] def GuardedMachine.comapIn {S In' In Out : Type}
    (f : In' → In) (G : GuardedMachine S In Out) : GuardedMachine S In' Out where
  guard s i := G.guard s (f i)
  next s i := G.next s (f i)
  out s i := G.out s (f i)
  reject s i := G.reject s (f i)

theorem GuardedMachine.comapIn_proj_trace {S In' In Out : Type}
    (f : In' → In) (G : GuardedMachine S In Out)
    {s sF : S} {tr : List (In' × Out)}
    (hTr : (G.comapIn f).toParty.ValidTrace s tr sF) :
    G.toParty.ValidTrace s (tr.map (fun p => (f p.1, p.2))) sF := by
  refine (G.comapIn f).models_self.trace_induction
    (motive := fun s tr sF => G.toParty.ValidTrace s (tr.map (fun p => (f p.1, p.2))) sF)
    ?_ ?_ ?_ hTr
  · intro s
    exact .nil s
  · intro s i rest sF hg _ ih
    exact .accept (G.step_accept hg) ih
  · intro s i rest sF hg _ ih
    exact .reject (f i) (G.step_reject hg) ih

/-- **Sequential Guard Composition (`GuardedMachine.seq`)**:
    Evaluates `G₁` first; on `G₁` pass, feeds `(G₁.next s i, G₁.out s i)` into `G₂`.
    If `G₂` rejects, runs `G₂.reject (G₁.next s i) (G₁.out s i)` so state burns committed
    by `G₁` (e.g., epoch-latch or HWM burn) are preserved fail-closed! -/
@[expose] def GuardedMachine.seq {S In Mid Out : Type}
    (G₁ : GuardedMachine S In Mid) (G₂ : GuardedMachine S Mid Out) :
    GuardedMachine S In Out where
  guard s i := G₁.guard s i && G₂.guard (G₁.next s i) (G₁.out s i)
  next s i := G₂.next (G₁.next s i) (G₁.out s i)
  out s i := G₂.out (G₁.next s i) (G₁.out s i)
  reject s i :=
    if G₁.guard s i then G₂.reject (G₁.next s i) (G₁.out s i)
    else G₁.reject s i

theorem GuardedMachine.seq_guard_true_iff {S In Mid Out : Type}
    (G₁ : GuardedMachine S In Mid) (G₂ : GuardedMachine S Mid Out) (s : S) (i : In) :
    (G₁.seq G₂).guard s i = true ↔
      G₁.guard s i = true ∧ G₂.guard (G₁.next s i) (G₁.out s i) = true :=
  Bool.and_eq_true_iff

/-- Sequential simulation congruence when `sim₁` and `sim₂` share state relation `Rel`. -/
def GuardedMachineSim.seq {Sc Sa In Mid Out : Type}
    {C₁ : GuardedMachine Sc In Mid} {A₁ : GuardedMachine Sa In Mid}
    {C₂ : GuardedMachine Sc Mid Out} {A₂ : GuardedMachine Sa Mid Out}
    (sim₁ : GuardedMachineSim C₁ A₁) (sim₂ : GuardedMachineSim C₂ A₂)
    (hRelEq : ∀ c a, sim₁.Rel c a ↔ sim₂.Rel c a) :
    GuardedMachineSim (C₁.seq C₂) (A₁.seq A₂) where
  Rel := sim₁.Rel
  guard_eq {c a} i hR := by
    dsimp only [GuardedMachine.seq]
    cases hg₁ : C₁.guard c i with
    | false =>
      have ha₁ : A₁.guard a i = false := (sim₁.guard_eq i hR).symm.trans hg₁
      rw [ha₁]
      rfl
    | true =>
      have ha₁ : A₁.guard a i = true := (sim₁.guard_eq i hR).symm.trans hg₁
      have hNextR : sim₂.Rel (C₁.next c i) (A₁.next a i) :=
        (hRelEq _ _).mp (sim₁.next_rel i hR hg₁)
      have hOutEq : C₁.out c i = A₁.out a i := sim₁.out_eq i hR hg₁
      rw [ha₁, Bool.true_and, Bool.true_and, ← hOutEq]
      exact sim₂.guard_eq (C₁.out c i) hNextR
  next_rel {c a} i hR hg := by
    obtain ⟨hg₁, hg₂⟩ := (C₁.seq_guard_true_iff C₂ c i).mp hg
    have hNextR₂ : sim₂.Rel (C₁.next c i) (A₁.next a i) :=
      (hRelEq _ _).mp (sim₁.next_rel i hR hg₁)
    have hOutEq : C₁.out c i = A₁.out a i := sim₁.out_eq i hR hg₁
    dsimp only [GuardedMachine.seq]
    rw [← hOutEq]
    exact (hRelEq _ _).mpr (sim₂.next_rel (C₁.out c i) hNextR₂ hg₂)
  out_eq {c a} i hR hg := by
    obtain ⟨hg₁, hg₂⟩ := (C₁.seq_guard_true_iff C₂ c i).mp hg
    have hNextR₂ : sim₂.Rel (C₁.next c i) (A₁.next a i) :=
      (hRelEq _ _).mp (sim₁.next_rel i hR hg₁)
    have hOutEq : C₁.out c i = A₁.out a i := sim₁.out_eq i hR hg₁
    dsimp only [GuardedMachine.seq]
    rw [← hOutEq]
    exact sim₂.out_eq (C₁.out c i) hNextR₂ hg₂
  reject_rel {c a} i hR hg := by
    dsimp only [GuardedMachine.seq] at hg ⊢
    cases hg₁ : C₁.guard c i with
    | false =>
      have ha₁ : A₁.guard a i = false := (sim₁.guard_eq i hR).symm.trans hg₁
      rw [ha₁]
      exact sim₁.reject_rel i hR hg₁
    | true =>
      rw [hg₁, Bool.true_and] at hg
      have ha₁ : A₁.guard a i = true := (sim₁.guard_eq i hR).symm.trans hg₁
      have hNextR₂ : sim₂.Rel (C₁.next c i) (A₁.next a i) :=
        (hRelEq _ _).mp (sim₁.next_rel i hR hg₁)
      have hOutEq : C₁.out c i = A₁.out a i := sim₁.out_eq i hR hg₁
      simp only [ha₁, ↓reduceIte, ← hOutEq]
      exact (hRelEq _ _).mpr (sim₂.reject_rel (C₁.out c i) hNextR₂ hg)

/-- Multi-turn invariant transfer across sequential guard pipelines `G₁.seq G₂`. -/
theorem GuardedMachine.seq_trace_invariant {S In Mid Out : Type}
    (G₁ : GuardedMachine S In Mid) (G₂ : GuardedMachine S Mid Out)
    (Inv : S → Prop)
    (hAcc₁ : ∀ s i, Inv s → G₁.guard s i = true → Inv (G₁.next s i))
    (hRej₁ : ∀ s i, Inv s → G₁.guard s i = false → Inv (G₁.reject s i))
    (hAcc₂ : ∀ s m, Inv s → G₂.guard s m = true → Inv (G₂.next s m))
    (hRej₂ : ∀ s m, Inv s → G₂.guard s m = false → Inv (G₂.reject s m))
    {s sF : S} {tr : List (In × Out)}
    (hTr : (G₁.seq G₂).toParty.ValidTrace s tr sF) (h₀ : Inv s) :
    Inv sF ∧ ∀ p ∈ tr, ∃ s₁, Inv s₁ ∧ G₁.guard s₁ p.1 = true ∧
      G₂.guard (G₁.next s₁ p.1) (G₁.out s₁ p.1) = true ∧
      p.2 = G₂.out (G₁.next s₁ p.1) (G₁.out s₁ p.1) := by
  obtain ⟨hF, hAll⟩ := (G₁.seq G₂).models_self.trace_invariant Inv
    (fun s i hs hg => by
      obtain ⟨hg₁, hg₂⟩ := (G₁.seq_guard_true_iff G₂ s i).mp hg
      exact hAcc₂ _ _ (hAcc₁ s i hs hg₁) hg₂)
    (fun s i hs hg => by
      dsimp only [GuardedMachine.seq] at hg ⊢
      cases hg₁ : G₁.guard s i with
      | false => exact hRej₁ s i hs hg₁
      | true =>
        rw [hg₁, Bool.true_and] at hg
        exact hRej₂ _ _ (hAcc₁ s i hs hg₁) hg)
    hTr h₀
  refine ⟨hF, fun p hp => ?_⟩
  obtain ⟨s₁, hs₁, hg, hOut⟩ := hAll p hp
  obtain ⟨hg₁, hg₂⟩ := (G₁.seq_guard_true_iff G₂ s₁ p.1).mp hg
  exact ⟨s₁, hs₁, hg₁, hg₂, hOut⟩

/-- **Conjunctive Product Guard (`GuardedMachine.prod`)**:
    Accepts iff both `G₁` and `G₂` accept. On rejection, each component runs `reject` iff its own
    guard failed and stutters (`s₁` / `s₂` unchanged) if its own guard passed — ensuring that
    every composite trace projects directly to valid traces of BOTH `G₁` and `G₂`! -/
@[expose] def GuardedMachine.prod {S₁ S₂ In Out₁ Out₂ : Type}
    (G₁ : GuardedMachine S₁ In Out₁) (G₂ : GuardedMachine S₂ In Out₂) :
    GuardedMachine (S₁ × S₂) In (Out₁ × Out₂) where
  guard p i := G₁.guard p.1 i && G₂.guard p.2 i
  next p i := (G₁.next p.1 i, G₂.next p.2 i)
  out p i := (G₁.out p.1 i, G₂.out p.2 i)
  reject p i :=
    (if G₁.guard p.1 i then p.1 else G₁.reject p.1 i,
     if G₂.guard p.2 i then p.2 else G₂.reject p.2 i)

/-- Product congruence of `GuardedMachineSim`. -/
def GuardedMachineSim.prod {Sc₁ Sa₁ Sc₂ Sa₂ In Out₁ Out₂ : Type}
    {C₁ : GuardedMachine Sc₁ In Out₁} {A₁ : GuardedMachine Sa₁ In Out₁}
    {C₂ : GuardedMachine Sc₂ In Out₂} {A₂ : GuardedMachine Sa₂ In Out₂}
    (sim₁ : GuardedMachineSim C₁ A₁) (sim₂ : GuardedMachineSim C₂ A₂) :
    GuardedMachineSim (C₁.prod C₂) (A₁.prod A₂) where
  Rel c a := sim₁.Rel c.1 a.1 ∧ sim₂.Rel c.2 a.2
  guard_eq {c a} i hR := by
    dsimp only [GuardedMachine.prod]
    rw [sim₁.guard_eq i hR.1, sim₂.guard_eq i hR.2]
  next_rel {c a} i hR hg := by
    obtain ⟨hg₁, hg₂⟩ := Bool.and_eq_true_iff.mp hg
    exact ⟨sim₁.next_rel i hR.1 hg₁, sim₂.next_rel i hR.2 hg₂⟩
  out_eq {c a} i hR hg := by
    obtain ⟨hg₁, hg₂⟩ := Bool.and_eq_true_iff.mp hg
    dsimp only [GuardedMachine.prod]
    rw [sim₁.out_eq i hR.1 hg₁, sim₂.out_eq i hR.2 hg₂]
  reject_rel {c a} i hR _ := by
    dsimp only [GuardedMachine.prod]
    refine ⟨?_, ?_⟩
    · cases hg₁ : C₁.guard c.1 i with
      | false =>
        have ha₁ : A₁.guard a.1 i = false := (sim₁.guard_eq i hR.1).symm.trans hg₁
        rw [ha₁]
        exact sim₁.reject_rel i hR.1 hg₁
      | true =>
        have ha₁ : A₁.guard a.1 i = true := (sim₁.guard_eq i hR.1).symm.trans hg₁
        simp only [ha₁, ↓reduceIte]
        exact hR.1
    · cases hg₂ : C₂.guard c.2 i with
      | false =>
        have ha₂ : A₂.guard a.2 i = false := (sim₂.guard_eq i hR.2).symm.trans hg₂
        rw [ha₂]
        exact sim₂.reject_rel i hR.2 hg₂
      | true =>
        have ha₂ : A₂.guard a.2 i = true := (sim₂.guard_eq i hR.2).symm.trans hg₂
        simp only [ha₂, ↓reduceIte]
        exact hR.2

/-- **First-component trace projection**: every multi-turn trace of `G₁.prod G₂` projects to a
    multi-turn valid trace of `G₁`, transferring all `G₁` trace invariants and one-shot latches! -/
theorem GuardedMachine.prod_fst_validTrace {S₁ S₂ In Out₁ Out₂ : Type}
    (G₁ : GuardedMachine S₁ In Out₁) (G₂ : GuardedMachine S₂ In Out₂)
    {p pF : S₁ × S₂} {tr : List (In × (Out₁ × Out₂))}
    (hTr : (G₁.prod G₂).toParty.ValidTrace p tr pF) :
    G₁.toParty.ValidTrace p.1 (tr.map (fun x => (x.1, x.2.1))) pF.1 := by
  refine (G₁.prod G₂).models_self.trace_induction
    (motive := fun p tr pF => G₁.toParty.ValidTrace p.1 (tr.map (fun x => (x.1, x.2.1))) pF.1)
    ?_ ?_ ?_ hTr
  · intro p
    exact .nil p.1
  · intro p i rest pF hg _ ih
    obtain ⟨hg₁, _⟩ := Bool.and_eq_true_iff.mp hg
    exact .accept (G₁.step_accept hg₁) ih
  · intro p i rest pF _ _ ih
    dsimp only [GuardedMachine.prod] at ih
    cases hg₁ : G₁.guard p.1 i with
    | true =>
      simp only [hg₁, ↓reduceIte] at ih
      exact ih
    | false =>
      simp only [hg₁, Bool.false_eq_true, ↓reduceIte] at ih
      exact .reject i (G₁.step_reject hg₁) ih

/-- **Second-component trace projection**: every multi-turn trace of `G₁.prod G₂` projects to a
    multi-turn valid trace of `G₂`, transferring all `G₂` trace invariants and one-shot latches! -/
theorem GuardedMachine.prod_snd_validTrace {S₁ S₂ In Out₁ Out₂ : Type}
    (G₁ : GuardedMachine S₁ In Out₁) (G₂ : GuardedMachine S₂ In Out₂)
    {p pF : S₁ × S₂} {tr : List (In × (Out₁ × Out₂))}
    (hTr : (G₁.prod G₂).toParty.ValidTrace p tr pF) :
    G₂.toParty.ValidTrace p.2 (tr.map (fun x => (x.1, x.2.2))) pF.2 := by
  refine (G₁.prod G₂).models_self.trace_induction
    (motive := fun p tr pF => G₂.toParty.ValidTrace p.2 (tr.map (fun x => (x.1, x.2.2))) pF.2)
    ?_ ?_ ?_ hTr
  · intro p
    exact .nil p.2
  · intro p i rest pF hg _ ih
    obtain ⟨_, hg₂⟩ := Bool.and_eq_true_iff.mp hg
    exact .accept (G₂.step_accept hg₂) ih
  · intro p i rest pF _ _ ih
    dsimp only [GuardedMachine.prod] at ih
    cases hg₂ : G₂.guard p.2 i with
    | true =>
      simp only [hg₂, ↓reduceIte] at ih
      exact ih
    | false =>
      simp only [hg₂, Bool.false_eq_true, ↓reduceIte] at ih
      exact .reject i (G₂.step_reject hg₂) ih

#verify_constructive Lens.lawful_id Lens.lawful_comp Lens.lawful_fst Lens.lawful_snd
#verify_constructive GuardedMachine.zoom_frame_trace GuardedMachine.zoom_proj_trace
#verify_constructive GuardedMachine.comapIn_proj_trace GuardedMachine.seq_trace_invariant
#verify_constructive GuardedMachine.prod_fst_validTrace GuardedMachine.prod_snd_validTrace

end Qsag.Exec.GuardedMachineSim
