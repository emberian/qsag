module
/-
# Qsag.Spec.Refines — Constructive State-Machine Forward and Trace Refinement

Universal state-machine refinement framework (`seL4` / `CompCert` style) supporting:
1. Initialized reactive machines (`Machine S In Out`) with explicit accept and error transitions,
2. Constructive witness-carrying forward simulation (`Refines C A`, written `C ⊑ A`) with
   reflexivity, vertical transitivity (`0 Classical.choice`), and multi-turn trace inclusion,
3. Functional lockstep simulation (`LockstepSim`) via an invariant and abstraction function,
4. Hardware leakage-contract refinement (`ExecMode`, `ObsMachine`, `ObsRefines`).

This module imports only `Spec` and `Tactic`. The morphisms to and from `Qsag.PartyMachine` /
`Qsag.ForwardSim`, the `N`-party rushing-network product refinement (`NetworkRefines`) and the
`InteractiveService` bisimulation bridges are in `Qsag.Exec.RefinesBridges`, above both sides.
-/

public import Qsag.Spec.Primitives
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Spec

set_option autoImplicit false

/-! ## 1. Initialized Reactive State Machines (`Machine`) -/

/-- Reactive state machine with initial-state predicate `Init`, partial transition `step`,
    and persistent error-state update `errStep`. -/
structure Machine (S In Out : Type) where
  Init : S → Prop
  step : S → In → Option (S × Out)
  errStep : S → In → S := fun s _ => s

/-- Construct a `Machine` from a deterministic total transition `S → In → S × Out`. -/
@[expose] def Machine.ofTotal {S In Out : Type}
    (initPred : S → Prop) (f : S → In → S × Out) : Machine S In Out where
  Init := initPred
  step s inp := some (f s inp)
  errStep s _ := s

/-- Construct a `Machine` from an initial state `s₀` and partial transition `S → In → Option (S × Out)`. -/
@[expose] def Machine.ofInitOption {S In Out : Type}
    (s₀ : S) (f : S → In → Option (S × Out)) : Machine S In Out where
  Init s := s = s₀
  step := f
  errStep s _ := s

/-- Execute one total step of `M`, emitting `some out` on acceptance or `none` on rejection. -/
@[expose] def Machine.runStep {S In Out : Type} (M : Machine S In Out)
    (s : S) (inp : In) : S × Option Out :=
  match M.step s inp with
  | some (s', out) => (s', some out)
  | none => (M.errStep s inp, none)

/-- Inductive multi-turn valid execution trace of accepted `(In × Out)` pairs from `s₀` to `s_final`,
    threading rejected inputs through `M.errStep`. -/
inductive Machine.ValidTrace {S In Out : Type} (M : Machine S In Out) :
    S → List (In × Out) → S → Prop where
  | nil (s : S) : M.ValidTrace s [] s
  | accept {s s' s_final : S} {inp : In} {out : Out} {rest : List (In × Out)} :
      M.step s inp = some (s', out) →
      M.ValidTrace s' rest s_final →
      M.ValidTrace s ((inp, out) :: rest) s_final
  | reject {s s_final : S} (inp : In) {rest : List (In × Out)} :
      M.step s inp = none →
      M.ValidTrace (M.errStep s inp) rest s_final →
      M.ValidTrace s rest s_final

/-- Multi-turn reachability from an `Init`-satisfying starting state. -/
@[expose] def Machine.Reachable {S In Out : Type} (M : Machine S In Out) (s : S) : Prop :=
  ∃ (s₀ : S) (tr : List (In × Out)), M.Init s₀ ∧ M.ValidTrace s₀ tr s

/-- Observable trace inclusion predicate: `trace` is realizable from some valid initial state of `M`. -/
@[expose] def Machine.AdmitsTrace {S In Out : Type} (M : Machine S In Out) (trace : List (In × Out)) : Prop :=
  ∃ (s₀ s_final : S), M.Init s₀ ∧ M.ValidTrace s₀ trace s_final

/-! ## 2. Constructive Forward Refinement (`Refines`, `C ⊑ A`) -/

/-- Witness-carrying forward simulation from concrete machine `C` to abstract machine `A`.
    Uses constructive initial-state mapping `init_lift` (`0 Classical.choice`) and deterministic
    `match` on `A.step` so vertical composition requires zero choice axioms. -/
structure Refines {S_c S_a In Out : Type}
    (C : Machine S_c In Out) (A : Machine S_a In Out) : Type 1 where
  Rel : S_c → S_a → Prop
  absInit : S_c → S_a
  init_ok : ∀ {c₀ : S_c}, C.Init c₀ → A.Init (absInit c₀) ∧ Rel c₀ (absInit c₀)
  sim_ok : ∀ {c c' : S_c} {a : S_a} {inp : In} {out : Out},
    Rel c a →
    C.step c inp = some (c', out) →
    match A.step a inp with
    | none => False
    | some (a', out_a) => out_a = out ∧ Rel c' a'
  sim_err : ∀ {c : S_c} {a : S_a} {inp : In},
    Rel c a →
    C.step c inp = none →
    A.step a inp = none ∧ Rel (C.errStep c inp) (A.errStep a inp)

scoped infix:50 " ⊑ " => Refines

/-- Functional lockstep simulation via concrete invariant `Inv` and abstraction function `abs`. -/
structure LockstepSim {S_c S_a In Out : Type}
    (C : Machine S_c In Out) (A : Machine S_a In Out) : Type 1 where
  Inv : S_c → Prop
  abs : S_c → S_a
  init_inv : ∀ {c₀ : S_c}, C.Init c₀ → Inv c₀ ∧ A.Init (abs c₀)
  step_eq : ∀ {c : S_c} (inp : In),
    Inv c →
    match C.step c inp with
    | some (c', out) => Inv c' ∧ A.step (abs c) inp = some (abs c', out)
    | none => Inv (C.errStep c inp) ∧ A.step (abs c) inp = none ∧
        abs (C.errStep c inp) = A.errStep (abs c) inp

/-- Every `LockstepSim` canonically induces a `Refines` witness (`C ⊑ A`). -/
def LockstepSim.toRefines {S_c S_a In Out : Type}
    {C : Machine S_c In Out} {A : Machine S_a In Out}
    (L : LockstepSim C A) : C ⊑ A where
  Rel c a := L.Inv c ∧ L.abs c = a
  absInit := L.abs
  init_ok {c₀} hInit := by
    obtain ⟨hInv, hInitA⟩ := L.init_inv hInit
    exact ⟨hInitA, hInv, rfl⟩
  sim_ok {c c' a inp out} hRel hStepC := by
    rcases hRel with ⟨hInv, rfl⟩
    have h := L.step_eq inp hInv
    rw [hStepC] at h
    rcases h with ⟨hInv', hStepA⟩
    rw [hStepA]
    exact ⟨rfl, hInv', rfl⟩
  sim_err {c a inp} hRel hNoneC := by
    rcases hRel with ⟨hInv, rfl⟩
    have h := L.step_eq inp hInv
    rw [hNoneC] at h
    rcases h with ⟨hInv', hNoneA, hErrEq⟩
    exact ⟨hNoneA, hInv', hErrEq⟩

/-- Reflexivity of `Refines` (`M ⊑ M`). -/
def Refines.refl {S In Out : Type} (M : Machine S In Out) : M ⊑ M where
  Rel := Eq
  absInit s := s
  init_ok hInit := ⟨hInit, rfl⟩
  sim_ok hRel hStep := by
    subst hRel
    rw [hStep]
    exact ⟨rfl, rfl⟩
  sim_err hRel hNone := by
    subst hRel
    exact ⟨hNone, rfl⟩

/-- Constructive vertical transitivity of `Refines`: `M₁ ⊑ M₂ → M₂ ⊑ M₃ → M₁ ⊑ M₃`
    (`0 Classical.choice`, composing `absInit` directly). -/
def Refines.trans {S₁ S₂ S₃ In Out : Type}
    {M₁ : Machine S₁ In Out} {M₂ : Machine S₂ In Out} {M₃ : Machine S₃ In Out}
    (r₁₂ : M₁ ⊑ M₂) (r₂₃ : M₂ ⊑ M₃) : M₁ ⊑ M₃ where
  Rel s₁ s₃ := ∃ s₂ : S₂, r₁₂.Rel s₁ s₂ ∧ r₂₃.Rel s₂ s₃
  absInit s₁ := r₂₃.absInit (r₁₂.absInit s₁)
  init_ok {s₁} hInit₁ := by
    obtain ⟨hInit₂, hRel₁₂⟩ := r₁₂.init_ok hInit₁
    obtain ⟨hInit₃, hRel₂₃⟩ := r₂₃.init_ok hInit₂
    exact ⟨hInit₃, ⟨r₁₂.absInit s₁, hRel₁₂, hRel₂₃⟩⟩
  sim_ok {s₁ s₁' s₃ inp out} hRel hStep₁ := by
    rcases hRel with ⟨s₂, h12, h23⟩
    have hMid := r₁₂.sim_ok h12 hStep₁
    cases hStep₂ : M₂.step s₂ inp with
    | none =>
      rw [hStep₂] at hMid
      exact False.elim hMid
    | some pair₂ =>
      rw [hStep₂] at hMid
      rcases pair₂ with ⟨s₂', out₂⟩
      rcases hMid with ⟨rfl, h12'⟩
      have hTop := r₂₃.sim_ok h23 hStep₂
      cases hStep₃ : M₃.step s₃ inp with
      | none =>
        rw [hStep₃] at hTop
        exact False.elim hTop
      | some pair₃ =>
        rw [hStep₃] at hTop
        rcases pair₃ with ⟨s₃', out₃⟩
        rcases hTop with ⟨hOutEq, h23'⟩
        exact ⟨hOutEq, ⟨s₂', h12', h23'⟩⟩
  sim_err {s₁ s₃ inp} hRel hNone₁ := by
    rcases hRel with ⟨s₂, h12, h23⟩
    obtain ⟨hNone₂, h12'⟩ := r₁₂.sim_err h12 hNone₁
    obtain ⟨hNone₃, h23'⟩ := r₂₃.sim_err h23 hNone₂
    exact ⟨hNone₃, ⟨M₂.errStep s₂ inp, h12', h23'⟩⟩

/-- Single-step output and relation preservation under `Machine.runStep`. -/
theorem Refines.preserve_runStep {S_c S_a In Out : Type}
    {C : Machine S_c In Out} {A : Machine S_a In Out}
    (sim : C ⊑ A) {c : S_c} {a : S_a} (inp : In) (hRel : sim.Rel c a) :
    (C.runStep c inp).2 = (A.runStep a inp).2 ∧
      sim.Rel (C.runStep c inp).1 (A.runStep a inp).1 := by
  dsimp only [Machine.runStep]
  cases hStepC : C.step c inp with
  | some pairC =>
    rcases pairC with ⟨c', out⟩
    have hOk := sim.sim_ok hRel hStepC
    cases hStepA : A.step a inp with
    | none => rw [hStepA] at hOk; exact False.elim hOk
    | some pairA =>
      rw [hStepA] at hOk
      rcases pairA with ⟨a', out_a⟩
      rcases hOk with ⟨rfl, hRel'⟩
      exact ⟨rfl, hRel'⟩
  | none =>
    obtain ⟨hNoneA, hRel'⟩ := sim.sim_err hRel hStepC
    rw [hNoneA]
    exact ⟨rfl, hRel'⟩

/-- Lift any multi-turn `Machine.ValidTrace` across `C ⊑ A` (`0 Classical.choice`). -/
theorem Refines.lift_validTrace {S_c S_a In Out : Type}
    {C : Machine S_c In Out} {A : Machine S_a In Out}
    (sim : C ⊑ A) :
    ∀ {c₀ c_final : S_c} {a₀ : S_a} {trace : List (In × Out)},
      sim.Rel c₀ a₀ →
      C.ValidTrace c₀ trace c_final →
      ∃ a_final : S_a, A.ValidTrace a₀ trace a_final ∧ sim.Rel c_final a_final
  | _, _, a₀, _, hRel, .nil _ => ⟨a₀, .nil a₀, hRel⟩
  | _, _, a₀, _, hRel, .accept hStepC hRest => by
    have hOk := sim.sim_ok hRel hStepC
    cases hStepA : A.step a₀ _ with
    | none => rw [hStepA] at hOk; exact False.elim hOk
    | some pairA =>
      rw [hStepA] at hOk
      rcases pairA with ⟨a', out_a⟩
      rcases hOk with ⟨rfl, hRel'⟩
      obtain ⟨a_final, hTrA, hRelFinal⟩ := sim.lift_validTrace hRel' hRest
      exact ⟨a_final, .accept hStepA hTrA, hRelFinal⟩
  | _, _, _, _, hRel, .reject inp hNoneC hRest => by
    obtain ⟨hNoneA, hRel'⟩ := sim.sim_err hRel hNoneC
    obtain ⟨a_final, hTrA, hRelFinal⟩ := sim.lift_validTrace hRel' hRest
    exact ⟨a_final, .reject inp hNoneA hTrA, hRelFinal⟩

/-- Observable trace inclusion: if `C ⊑ A`, every initialized trace of `C` is admitted by `A`. -/
theorem Refines.preserve_admitsTrace {S_c S_a In Out : Type}
    {C : Machine S_c In Out} {A : Machine S_a In Out}
    (sim : C ⊑ A) {trace : List (In × Out)}
    (hAdmitsC : C.AdmitsTrace trace) :
    A.AdmitsTrace trace := by
  rcases hAdmitsC with ⟨c₀, c_final, hInitC, hTraceC⟩
  obtain ⟨hInitA, hRel₀⟩ := sim.init_ok hInitC
  obtain ⟨a_final, hTraceA, _⟩ := sim.lift_validTrace hRel₀ hTraceC
  exact ⟨sim.absInit c₀, a_final, hInitA, hTraceA⟩

/-- Trace-safety preservation: any trace predicate `Safe` satisfied by all initialized traces of `A`
    automatically holds for all initialized traces of `C` whenever `C ⊑ A`. -/
theorem Refines.preserve_trace_safety {S_c S_a In Out : Type}
    {C : Machine S_c In Out} {A : Machine S_a In Out}
    (sim : C ⊑ A) (Safe : List (In × Out) → Prop)
    (hSafeA : ∀ {tr : List (In × Out)}, A.AdmitsTrace tr → Safe tr)
    {tr : List (In × Out)} (hAdmitsC : C.AdmitsTrace tr) :
    Safe tr :=
  hSafeA (sim.preserve_admitsTrace hAdmitsC)

/-! ## 3. Hardware Execution Mode & Constant-Time Observation Refinement -/

/-- Architectural execution-mode contract governing constant-time side-channel guarantees
    (e.g., x86-64 `DOIT` / AArch64 `DIT`, clean upper YMM state, and speculation barriers). -/
structure ExecMode where
  ditEnabled : Bool
  cleanSimdUpper : Bool
  speculationFence : Bool
  deriving DecidableEq, Repr

/-- Canonical safe hardware execution mode required for constant-time secret-bearing kernels. -/
@[expose] def ExecMode.constantTimeSafe : ExecMode :=
  { ditEnabled := true, cleanSimdUpper := true, speculationFence := true }

/-- Observation-emitting concrete transition parameterized by `ExecMode` and leakage event `Obs`. -/
structure ObsMachine (S In Out Obs : Type) where
  base : Machine S In Out
  observe : ExecMode → S → In → Obs

/-- Constant-time observational non-interference paired with functional refinement `O.base ⊑ A`:
    under `mode = ExecMode.constantTimeSafe`, any two low-equivalent concrete states emit identical
    leakage observations `Obs` while functionally refining `A`. -/
structure ObsRefines {S_c S_a In Out Obs : Type}
    (O : ObsMachine S_c In Out Obs) (A : Machine S_a In Out)
    (LowEq : S_c → S_c → Prop) : Type 1 where
  functional : O.base ⊑ A
  obs_noninterference : ∀ {s₁ s₂ : S_c} (inp : In),
    LowEq s₁ s₂ →
    O.observe ExecMode.constantTimeSafe s₁ inp = O.observe ExecMode.constantTimeSafe s₂ inp

theorem ObsRefines.preserve_admitsTrace {S_c S_a In Out Obs : Type}
    {O : ObsMachine S_c In Out Obs} {A : Machine S_a In Out} {LowEq : S_c → S_c → Prop}
    (r : ObsRefines O A LowEq) {tr : List (In × Out)}
    (hAdmits : O.base.AdmitsTrace tr) :
    A.AdmitsTrace tr :=
  r.functional.preserve_admitsTrace hAdmits

#verify_constructive
  Qsag.Spec.Refines.preserve_runStep
  Qsag.Spec.Refines.lift_validTrace
  Qsag.Spec.Refines.preserve_admitsTrace
  Qsag.Spec.Refines.preserve_trace_safety
  Qsag.Spec.ObsRefines.preserve_admitsTrace

end Qsag.Spec
end
