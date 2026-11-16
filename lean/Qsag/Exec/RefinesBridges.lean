module
/-
# Qsag.Exec.RefinesBridges — `Spec.Refines` Morphisms to the Execution Layer

Bridges between the Layer-0 refinement framework (`Qsag.Spec.Machine`, `Qsag.Spec.Refines`) and
the execution-layer machines:
1. forgetful and lifting maps with `Qsag.PartyMachine` / `Qsag.ForwardSim` (`SimulationSpine`),
2. horizontal `N`-party rushing-network product refinement (`NetworkRefines`), and
3. morphisms with `InteractiveService` machines, bisimulations and observers.
-/

public import Qsag.Spec.Refines
public import Qsag.Spec.Assumptions
public import Qsag.Exec.SimulationSpine
public import Qsag.Exec.InteractiveServiceContext
public import Qsag.Exec.InteractiveSecurityContract
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Spec
open scoped Qsag.Spec

set_option autoImplicit false

/-! ## 1. Morphisms With `Qsag.PartyMachine` / `Qsag.ForwardSim` -/

/-- Forgetful projection to `Qsag.PartyMachine`. -/
@[expose] def Machine.toPartyMachine {S In Out : Type}
    (M : Machine S In Out) : Qsag.PartyMachine S In Out where
  step := M.step
  errStep := M.errStep

/-- Lift any `Qsag.PartyMachine` with an initial-state predicate to `Spec.Machine`. -/
@[expose] def Machine.ofPartyMachine {S In Out : Type}
    (initPred : S → Prop) (M : Qsag.PartyMachine S In Out) : Machine S In Out where
  Init := initPred
  step := M.step
  errStep := M.errStep

/-- Project `C ⊑ A` to `Qsag.ForwardSim C.toPartyMachine A.toPartyMachine`. -/
@[expose] def Refines.toPartyForwardSim {S_c S_a In Out : Type}
    {C : Machine S_c In Out} {A : Machine S_a In Out}
    (sim : C ⊑ A) : Qsag.ForwardSim C.toPartyMachine A.toPartyMachine where
  Rel := sim.Rel
  sim_ok := sim.sim_ok
  sim_err := sim.sim_err

/-- Lift a `Qsag.ForwardSim` together with an initial-state abstraction map to `C ⊑ A`. -/
@[expose] def Refines.ofPartyForwardSim {S_c S_a In Out : Type}
    {initC : S_c → Prop} {initA : S_a → Prop}
    {C : Qsag.PartyMachine S_c In Out} {A : Qsag.PartyMachine S_a In Out}
    (sim : Qsag.ForwardSim C A)
    (absInit : S_c → S_a)
    (hInit : ∀ {c₀ : S_c}, initC c₀ → initA (absInit c₀) ∧ sim.Rel c₀ (absInit c₀)) :
    Machine.ofPartyMachine initC C ⊑ Machine.ofPartyMachine initA A where
  Rel := sim.Rel
  absInit := absInit
  init_ok := hInit
  sim_ok := sim.sim_ok
  sim_err := sim.sim_err

/-! ## 2. Horizontal `N`-Party Rushing-Network Product Refinement (`NetworkRefines`) -/

/-- Composite `N`-party rushing-network `Machine` wrapping per-party `Machine` instances under
    arbitrary rushing adversary `Adv` and static/adaptive `corruptSet`. -/
def networkMachine {N : Nat} {PartySt Meta In Out CorruptOut AdvSt : Type}
    (corruptSet : List (Fin N))
    (machines : Fin N → Machine PartySt In Out)
    (Adv : Qsag.RushingAdversary N Meta In Out CorruptOut AdvSt)
    (advInit : AdvSt → Prop) :
    Machine ((Fin N → PartySt) × AdvSt) (Qsag.RoundSchedule N Meta)
      (Qsag.RoundTranscript N Out CorruptOut) :=
  Machine.ofPartyMachine
    (fun ca => advInit ca.2 ∧ ∀ (i : Fin N), i ∉ corruptSet → (machines i).Init (ca.1 i))
    (Qsag.rushingNetworkMachine corruptSet (fun i => (machines i).toPartyMachine) Adv)

/-- **Horizontal `N`-Party Product Refinement (`NetworkRefines`)**:
    If every honest party `i ∉ corruptSet` satisfies `C i ⊑ A i`, and `defaultAbs` supplies default
    initial states for corrupt slots, then the composite rushing network `networkMachine` of `C`
    refines the composite rushing network of `A` (`networkMachine ... C ... ⊑ networkMachine ... A ...`)! -/
def NetworkRefines {N : Nat} {S_c S_a Meta In Out CorruptOut AdvSt : Type}
    (corruptSet : List (Fin N))
    (C : Fin N → Machine S_c In Out)
    (A : Fin N → Machine S_a In Out)
    (Adv : Qsag.RushingAdversary N Meta In Out CorruptOut AdvSt)
    (advInit : AdvSt → Prop)
    (defaultAbs : Fin N → S_c → S_a)
    (sims : ∀ (i : Fin N), i ∉ corruptSet → C i ⊑ A i) :
    networkMachine corruptSet C Adv advInit ⊑ networkMachine corruptSet A Adv advInit := by
  let partySims : ∀ (i : Fin N), i ∉ corruptSet →
      Qsag.ForwardSim (C i).toPartyMachine (A i).toPartyMachine :=
    fun i hi => (sims i hi).toPartyForwardSim
  refine Refines.ofPartyForwardSim
    (Qsag.network_forward_sim corruptSet
      (fun i => (C i).toPartyMachine) (fun i => (A i).toPartyMachine) Adv partySims)
    (fun ca =>
      (fun i =>
        if h : Qsag.isCorruptParty i corruptSet = false then
          (sims i ((Qsag.isCorruptParty_eq_false_iff i corruptSet).mp h)).absInit (ca.1 i)
        else
          defaultAbs i (ca.1 i),
       ca.2))
    ?_
  intro ca hInitC
  rcases hInitC with ⟨hAdvInit, hPartiesInit⟩
  refine ⟨⟨hAdvInit, ?_⟩, ?_⟩
  · intro i hiNotCorr
    have hFalse : Qsag.isCorruptParty i corruptSet = false :=
      (Qsag.isCorruptParty_eq_false_iff i corruptSet).mpr hiNotCorr
    dsimp only
    split
    · exact ((sims i _).init_ok (hPartiesInit i hiNotCorr)).1
    · rename_i hNot
      exact False.elim (hNot hFalse)
  · rw [Qsag.network_forward_sim_rel]
    refine ⟨rfl, ?_⟩
    intro i hiNotCorr
    have hFalse : Qsag.isCorruptParty i corruptSet = false :=
      (Qsag.isCorruptParty_eq_false_iff i corruptSet).mpr hiNotCorr
    dsimp only [partySims, Refines.toPartyForwardSim]
    split
    · rename_i hCond
      have hSub : (Qsag.isCorruptParty_eq_false_iff i corruptSet).mp hCond = hiNotCorr :=
        Subsingleton.elim _ _
      rw [hSub]
      exact ((sims i hiNotCorr).init_ok (hPartiesInit i hiNotCorr)).2
    · rename_i hNot
      exact False.elim (hNot hFalse)

/-! ## 3. Bidirectional Morphisms With `InteractiveService` Stateful Feedback Composition -/

/-- Lift a deterministic total `Qsag.InteractiveService.Machine` with an initial-state predicate
    into `Qsag.Spec.Machine`. -/
@[expose] def Machine.ofInteractive {S In Out : Type}
    (initPred : S → Prop) (m : Qsag.InteractiveService.Machine In Out S) : Machine S In Out :=
  Machine.ofTotal initPred m.step

/-- Lift an `InteractiveService.Bisimulation` together with an initial-state abstraction map
    into a constructive `Spec.Refines` witness (`⊑`). -/
def Refines.ofInteractiveBisimulation {S_c S_a In Out : Type}
    {initC : S_c → Prop} {initA : S_a → Prop}
    {m : Qsag.InteractiveService.Machine In Out S_c}
    {n : Qsag.InteractiveService.Machine In Out S_a}
    {R : S_c → S_a → Prop}
    (hBisim : Qsag.InteractiveService.Bisimulation m n R)
    (absInit : S_c → S_a)
    (hInit : ∀ {c₀ : S_c}, initC c₀ → initA (absInit c₀) ∧ R c₀ (absInit c₀)) :
    Machine.ofInteractive initC m ⊑ Machine.ofInteractive initA n where
  Rel := R
  absInit := absInit
  init_ok := hInit
  sim_ok {c c' a inp out} hRel hStepC := by
    dsimp only [Machine.ofInteractive, Machine.ofTotal] at hStepC ⊢
    injection hStepC with hPair
    have hc' : (m.step c inp).1 = c' := congrArg Prod.fst hPair
    have hout : (m.step c inp).2 = out := congrArg Prod.snd hPair
    obtain ⟨hRel', hOutEq⟩ := hBisim.step c a hRel inp
    exact ⟨hOutEq.symm.trans hout, hc' ▸ hRel'⟩
  sim_err {_ _ _} _ hNoneC := by
    dsimp only [Machine.ofInteractive, Machine.ofTotal] at hNoneC
    cases hNoneC

/-- Converse morphism: every `Spec.Refines` witness between lifted `InteractiveService.Machine`s
    canonically induces an `InteractiveService.Bisimulation` under arbitrary adaptive feedback. -/
theorem Refines.toInteractiveBisimulation {S_c S_a In Out : Type}
    {initC : S_c → Prop} {initA : S_a → Prop}
    {m : Qsag.InteractiveService.Machine In Out S_c}
    {n : Qsag.InteractiveService.Machine In Out S_a}
    (sim : Machine.ofInteractive initC m ⊑ Machine.ofInteractive initA n) :
    Qsag.InteractiveService.Bisimulation m n sim.Rel := by
  refine ⟨fun c a hRel inp => ?_⟩
  have hOk := sim.sim_ok hRel (rfl : (Machine.ofInteractive initC m).step c inp = some (m.step c inp))
  dsimp only [Machine.ofInteractive, Machine.ofTotal] at hOk
  exact ⟨hOk.2, hOk.1.symm⟩

/-- Every `Spec.Refines` witness between lifted `InteractiveService.Machine`s implies
    `InteractiveService.PrefixEquivalent` across all stateful feedback `Environment`s `Z` and
    arbitrary activation horizons `fuel : Nat`. -/
theorem Refines.toInteractivePrefixEquivalent {S_c S_a In Out : Type}
    {initC : S_c → Prop} {initA : S_a → Prop}
    {m : Qsag.InteractiveService.Machine In Out S_c}
    {n : Qsag.InteractiveService.Machine In Out S_a}
    (sim : Machine.ofInteractive initC m ⊑ Machine.ofInteractive initA n)
    {c₀ : S_c} (hInitC : initC c₀) :
    Qsag.InteractiveService.PrefixEquivalent m n c₀ (sim.absInit c₀) :=
  Qsag.InteractiveService.bisimulation_prefixEquivalent
    m n sim.Rel sim.toInteractiveBisimulation c₀ (sim.absInit c₀) (sim.init_ok hInitC).2

/-- Every `Spec.Refines` witness between lifted `InteractiveService.Machine`s transfers online
    adaptive `Observer` acceptance bits across coupled sample tapes (`coupled_accept_bits`). -/
theorem Refines.toInteractiveCoupledAcceptBits {S_c S_a In Out E : Type}
    {initC : S_c → Prop} {initA : S_a → Prop}
    {m : Qsag.InteractiveService.Machine In Out S_c}
    {n : Qsag.InteractiveService.Machine In Out S_a}
    (sim : Machine.ofInteractive initC m ⊑ Machine.ofInteractive initA n)
    (z : Qsag.InteractiveService.Observer In Out E)
    (coins : List ((S_c × S_a) × E))
    (hc : ∀ st ∈ coins, sim.Rel st.1.1 st.1.2) :
    coins.map (fun st => z.accept (Qsag.InteractiveService.run m z.environment z.fuel st.1.1 st.2).2) =
      coins.map (fun st => z.accept (Qsag.InteractiveService.run n z.environment z.fuel st.1.2 st.2).2) :=
  Qsag.InteractiveService.coupled_accept_bits m n sim.Rel sim.toInteractiveBisimulation z coins hc

#verify_constructive
  Qsag.Spec.Refines.toInteractiveBisimulation
  Qsag.Spec.Refines.toInteractivePrefixEquivalent
  Qsag.Spec.Refines.toInteractiveCoupledAcceptBits

end Qsag.Spec
end

public section
namespace Qsag.Spec

/-- Postcomposition preserves the stuttering behavior of an interface abstraction.
Rejected and internal concrete steps retain the same intermediate and final abstract states. -/
def DataRefines.postcompose {Sc Sm Sa Ic Ia Oc Oa : Type}
    {C : Machine Sc Ic Oc} {M : Machine Sm Ia Oa} {A : Machine Sa Ia Oa}
    {visIn : Ic → Option Ia} {visOut : Oc → Oa}
    (cm : DataRefines C M visIn visOut) (ma : M ⊑ A) :
    DataRefines C A visIn visOut where
  Rel c a := ∃ m, cm.Rel c m ∧ ma.Rel m a
  absInit c := ma.absInit (cm.absInit c)
  init_ok hc := by
    obtain ⟨hm, hcm⟩ := cm.init_ok hc
    obtain ⟨ha, hma⟩ := ma.init_ok hm
    exact ⟨ha, cm.absInit _, hcm, hma⟩
  sim_visible hrel hstep hvis := by
    obtain ⟨m, hcm, hma⟩ := hrel
    obtain ⟨m', hmstep, hcm'⟩ := cm.sim_visible hcm hstep hvis
    have h := ma.sim_ok hma hmstep
    split at h
    · contradiction
    · rename_i a' out he
      obtain ⟨hout, hma'⟩ := h
      subst out
      exact ⟨a', he, m', hcm', hma'⟩
  sim_internal hrel hstep hvis := by
    obtain ⟨m, hcm, hma⟩ := hrel
    exact ⟨m, cm.sim_internal hcm hstep hvis, hma⟩
  sim_reject hrel hstep := by
    obtain ⟨m, hcm, hma⟩ := hrel
    exact ⟨m, cm.sim_reject hcm hstep, hma⟩

/-- The composed simulation carries every projected accepted trace to the final machine. -/
theorem DataRefines.postcompose_admits {Sc Sm Sa Ic Ia Oc Oa : Type}
    {C : Machine Sc Ic Oc} {M : Machine Sm Ia Oa} {A : Machine Sa Ia Oa}
    {visIn : Ic → Option Ia} {visOut : Oc → Oa}
    (cm : DataRefines C M visIn visOut) (ma : M ⊑ A)
    {tr : List (Ic × Oc)} (h : C.AdmitsTrace tr) :
    A.AdmitsTrace (projectTrace visIn visOut tr) :=
  (cm.postcompose ma).preserve_admitsTrace h

#verify_constructive DataRefines.postcompose_admits
end Qsag.Spec
end

/-! ## 5. Error-Synchronized & Bounded-Stuttering Refinement (`ErrSyncDataRefines`, `IndexedSim`) -/

public section
namespace Qsag.Spec
open scoped Qsag.Spec

set_option autoImplicit false

/-- Transitivity (concatenation) of `Machine.ValidTrace` (`0 Classical.choice`). -/
theorem Machine.ValidTrace.append {S In Out : Type} {M : Machine S In Out}
    {s₀ s₁ s₂ : S} {tr₁ tr₂ : List (In × Out)}
    (h₁ : M.ValidTrace s₀ tr₁ s₁) (h₂ : M.ValidTrace s₁ tr₂ s₂) :
    M.ValidTrace s₀ (tr₁ ++ tr₂) s₂ := by
  induction h₁ with
  | nil _ => exact h₂
  | accept hStep _ ih => exact .accept hStep (ih h₂)
  | reject inp hNone _ ih => exact .reject inp hNone (ih h₂)

/-- **Error-Synchronized Interface-Abstracting Simulation (`ErrSyncDataRefines`)**:
    Generalizes `Spec.DataRefines` so that a rejected concrete step (`C.step c inp = none`)
    may either:
    - **stutter** (`errVis c inp = none`), keeping the abstract state at `a` (`Rel (C.errStep c inp) a`), or
    - **synchronize** (`errVis c inp = some j`), stepping the abstract state to `A.errStep a j`
      under `A.step a j = none` (`Rel (C.errStep c inp) (A.errStep a j)`).
    Because `Machine.ValidTrace.reject` transitions `a ↦ A.errStep a j` silently without
    emitting observable I/O pairs, `ErrSyncDataRefines` preserves `AdmitsTrace (projectTrace ...)`
    while keeping concrete and abstract error-burned state (such as epoch-latch counters burned
    before a failed signing attempt!) in exact lockstep. -/
structure ErrSyncDataRefines {S_c S_a In_c In_a Out_c Out_a : Type}
    (C : Machine S_c In_c Out_c) (A : Machine S_a In_a Out_a)
    (visIn : In_c → Option In_a) (visOut : Out_c → Out_a) : Type 1 where
  Rel : S_c → S_a → Prop
  absInit : S_c → S_a
  errVis : S_c → In_c → Option In_a
  init_ok : ∀ {c₀ : S_c}, C.Init c₀ → A.Init (absInit c₀) ∧ Rel c₀ (absInit c₀)
  sim_visible : ∀ {c c' : S_c} {a : S_a} {inp : In_c} {out : Out_c} {j : In_a},
    Rel c a → C.step c inp = some (c', out) → visIn inp = some j →
    ∃ a' : S_a, A.step a j = some (a', visOut out) ∧ Rel c' a'
  sim_internal : ∀ {c c' : S_c} {a : S_a} {inp : In_c} {out : Out_c},
    Rel c a → C.step c inp = some (c', out) → visIn inp = none → Rel c' a
  sim_reject_stutter : ∀ {c : S_c} {a : S_a} {inp : In_c},
    Rel c a → C.step c inp = none → errVis c inp = none → Rel (C.errStep c inp) a
  sim_reject_sync : ∀ {c : S_c} {a : S_a} {inp : In_c} {j : In_a},
    Rel c a → C.step c inp = none → errVis c inp = some j →
    A.step a j = none ∧ Rel (C.errStep c inp) (A.errStep a j)

/-- Lift any multi-turn concrete execution across `ErrSyncDataRefines` (`0 Classical.choice`). -/
theorem ErrSyncDataRefines.lift_validTrace {S_c S_a In_c In_a Out_c Out_a : Type}
    {C : Machine S_c In_c Out_c} {A : Machine S_a In_a Out_a}
    {visIn : In_c → Option In_a} {visOut : Out_c → Out_a}
    (sim : ErrSyncDataRefines C A visIn visOut)
    {c₀ c_final : S_c} {a₀ : S_a} {trace : List (In_c × Out_c)}
    (hRel₀ : sim.Rel c₀ a₀) (hTrC : C.ValidTrace c₀ trace c_final) :
    ∃ a_final : S_a,
      A.ValidTrace a₀ (projectTrace visIn visOut trace) a_final ∧ sim.Rel c_final a_final := by
  induction hTrC generalizing a₀ with
  | nil _ => exact ⟨a₀, .nil a₀, hRel₀⟩
  | @accept s s' _ inp out rest hStepC _ ih =>
    cases hVis : visIn inp with
    | some j =>
      obtain ⟨a', hStepA, hRel'⟩ := sim.sim_visible hRel₀ hStepC hVis
      obtain ⟨a_final, hTrA, hRelFinal⟩ := ih hRel'
      refine ⟨a_final, ?_, hRelFinal⟩
      simp only [projectTrace, hVis]
      exact .accept hStepA hTrA
    | none =>
      obtain ⟨a_final, hTrA, hRelFinal⟩ := ih (sim.sim_internal hRel₀ hStepC hVis)
      refine ⟨a_final, ?_, hRelFinal⟩
      simp only [projectTrace, hVis]
      exact hTrA
  | @reject s _ inp rest hNoneC _ ih =>
    cases hEv : sim.errVis s inp with
    | none =>
      exact ih (sim.sim_reject_stutter hRel₀ hNoneC hEv)
    | some j =>
      obtain ⟨hNoneA, hRel'⟩ := sim.sim_reject_sync hRel₀ hNoneC hEv
      obtain ⟨a_final, hTrA, hRelFinal⟩ := ih hRel'
      exact ⟨a_final, .reject j hNoneA hTrA, hRelFinal⟩

/-- Observable trace inclusion up to `projectTrace` under `ErrSyncDataRefines`. -/
theorem ErrSyncDataRefines.preserve_admitsTrace {S_c S_a In_c In_a Out_c Out_a : Type}
    {C : Machine S_c In_c Out_c} {A : Machine S_a In_a Out_a}
    {visIn : In_c → Option In_a} {visOut : Out_c → Out_a}
    (sim : ErrSyncDataRefines C A visIn visOut) {trace : List (In_c × Out_c)}
    (hAdmitsC : C.AdmitsTrace trace) :
    A.AdmitsTrace (projectTrace visIn visOut trace) := by
  rcases hAdmitsC with ⟨c₀, c_final, hInitC, hTraceC⟩
  obtain ⟨hInitA, hRel₀⟩ := sim.init_ok hInitC
  obtain ⟨a_final, hTraceA, _⟩ := sim.lift_validTrace hRel₀ hTraceC
  exact ⟨sim.absInit c₀, a_final, hInitA, hTraceA⟩

/-- Reachability transfer across `ErrSyncDataRefines`. -/
theorem ErrSyncDataRefines.reachable_rel {S_c S_a In_c In_a Out_c Out_a : Type}
    {C : Machine S_c In_c Out_c} {A : Machine S_a In_a Out_a}
    {visIn : In_c → Option In_a} {visOut : Out_c → Out_a}
    (sim : ErrSyncDataRefines C A visIn visOut) {c : S_c} (hReach : C.Reachable c) :
    ∃ a : S_a, A.Reachable a ∧ sim.Rel c a := by
  rcases hReach with ⟨c₀, tr, hInitC, hTraceC⟩
  obtain ⟨hInitA, hRel₀⟩ := sim.init_ok hInitC
  obtain ⟨a, hTraceA, hRel⟩ := sim.lift_validTrace hRel₀ hTraceC
  exact ⟨a, ⟨sim.absInit c₀, _, hInitA, hTraceA⟩, hRel⟩

/-- Trace-safety transfer across `ErrSyncDataRefines`. -/
theorem ErrSyncDataRefines.preserve_trace_safety {S_c S_a In_c In_a Out_c Out_a : Type}
    {C : Machine S_c In_c Out_c} {A : Machine S_a In_a Out_a}
    {visIn : In_c → Option In_a} {visOut : Out_c → Out_a}
    (sim : ErrSyncDataRefines C A visIn visOut)
    (Safe : List (In_a × Out_a) → Prop)
    (hSafeA : ∀ {tr_a : List (In_a × Out_a)}, A.AdmitsTrace tr_a → Safe tr_a)
    {tr_c : List (In_c × Out_c)} (hAdmitsC : C.AdmitsTrace tr_c) :
    Safe (projectTrace visIn visOut tr_c) :=
  hSafeA (sim.preserve_admitsTrace hAdmitsC)

/-- Every `DataRefines` embeds canonically into `ErrSyncDataRefines` (`errVis := fun _ _ => none`). -/
def DataRefines.toErrSync {S_c S_a In_c In_a Out_c Out_a : Type}
    {C : Machine S_c In_c Out_c} {A : Machine S_a In_a Out_a}
    {visIn : In_c → Option In_a} {visOut : Out_c → Out_a}
    (sim : DataRefines C A visIn visOut) :
    ErrSyncDataRefines C A visIn visOut where
  Rel := sim.Rel
  absInit := sim.absInit
  errVis _ _ := none
  init_ok := sim.init_ok
  sim_visible := sim.sim_visible
  sim_internal := sim.sim_internal
  sim_reject_stutter hRel hNone _ := sim.sim_reject hRel hNone
  sim_reject_sync _ _ hEv := by cases hEv

/-- Every same-alphabet `Refines` (`C ⊑ A`) embeds unconditionally into `ErrSyncDataRefines`
    (`errVis := fun _ inp => some inp`), even when `A.errStep` mutates persistent state! -/
def Refines.toErrSync {S_c S_a In Out : Type}
    {C : Machine S_c In Out} {A : Machine S_a In Out}
    (sim : C ⊑ A) : ErrSyncDataRefines C A some id where
  Rel := sim.Rel
  absInit := sim.absInit
  errVis _ inp := some inp
  init_ok := sim.init_ok
  sim_visible {c c' a inp out j} hRel hStepC hVis := by
    cases hVis
    have hOk := sim.sim_ok hRel hStepC
    cases hStepA : A.step a inp with
    | none => rw [hStepA] at hOk; exact False.elim hOk
    | some pairA =>
      rw [hStepA] at hOk
      rcases pairA with ⟨a', out_a⟩
      rcases hOk with ⟨rfl, hRel'⟩
      exact ⟨a', rfl, hRel'⟩
  sim_internal _ _ hVis := by cases hVis
  sim_reject_stutter _ _ hEv := by cases hEv
  sim_reject_sync {_ _ _ _} hRel hNoneC hEv := by
    cases hEv
    exact sim.sim_err hRel hNoneC

/-- Converse projection: a fully synchronized same-alphabet `ErrSyncDataRefines` is a `Refines` (`⊑`). -/
def ErrSyncDataRefines.toRefines {S_c S_a In Out : Type}
    {C : Machine S_c In Out} {A : Machine S_a In Out}
    (sim : ErrSyncDataRefines C A some id)
    (hSyncAll : ∀ (c : S_c) (inp : In), sim.errVis c inp = some inp) :
    C ⊑ A where
  Rel := sim.Rel
  absInit := sim.absInit
  init_ok := sim.init_ok
  sim_ok {c c' a inp out} hRel hStepC := by
    obtain ⟨a', hStepA, hRel'⟩ := sim.sim_visible hRel hStepC rfl
    rw [hStepA]
    exact ⟨rfl, hRel'⟩
  sim_err {c a inp} hRel hNoneC :=
    sim.sim_reject_sync hRel hNoneC (hSyncAll c inp)

/-- Right composition of `ErrSyncDataRefines` with `M ⊑ A` (`0 Classical.choice`). -/
def ErrSyncDataRefines.postcompose {Sc Sm Sa Ic Ia Oc Oa : Type}
    {C : Machine Sc Ic Oc} {M : Machine Sm Ia Oa} {A : Machine Sa Ia Oa}
    {visIn : Ic → Option Ia} {visOut : Oc → Oa}
    (cm : ErrSyncDataRefines C M visIn visOut) (ma : M ⊑ A) :
    ErrSyncDataRefines C A visIn visOut where
  Rel c a := ∃ m, cm.Rel c m ∧ ma.Rel m a
  absInit c := ma.absInit (cm.absInit c)
  errVis := cm.errVis
  init_ok hc := by
    obtain ⟨hm, hcm⟩ := cm.init_ok hc
    obtain ⟨ha, hma⟩ := ma.init_ok hm
    exact ⟨ha, cm.absInit _, hcm, hma⟩
  sim_visible hrel hstep hvis := by
    obtain ⟨m, hcm, hma⟩ := hrel
    obtain ⟨m', hmstep, hcm'⟩ := cm.sim_visible hcm hstep hvis
    have h := ma.sim_ok hma hmstep
    split at h
    · contradiction
    · rename_i a' out he
      obtain ⟨hout, hma'⟩ := h
      subst out
      exact ⟨a', he, m', hcm', hma'⟩
  sim_internal hrel hstep hvis := by
    obtain ⟨m, hcm, hma⟩ := hrel
    exact ⟨m, cm.sim_internal hcm hstep hvis, hma⟩
  sim_reject_stutter hrel hnone hev := by
    obtain ⟨m, hcm, hma⟩ := hrel
    exact ⟨m, cm.sim_reject_stutter hcm hnone hev, hma⟩
  sim_reject_sync hrel hnone hev := by
    obtain ⟨m, hcm, hma⟩ := hrel
    obtain ⟨hmnone, hcm'⟩ := cm.sim_reject_sync hcm hnone hev
    obtain ⟨hanone, hma'⟩ := ma.sim_err hma hmnone
    exact ⟨hanone, M.errStep m _, hcm', hma'⟩

theorem ErrSyncDataRefines.postcompose_admits {Sc Sm Sa Ic Ia Oc Oa : Type}
    {C : Machine Sc Ic Oc} {M : Machine Sm Ia Oa} {A : Machine Sa Ia Oa}
    {visIn : Ic → Option Ia} {visOut : Oc → Oa}
    (cm : ErrSyncDataRefines C M visIn visOut) (ma : M ⊑ A)
    {tr : List (Ic × Oc)} (h : C.AdmitsTrace tr) :
    A.AdmitsTrace (projectTrace visIn visOut tr) :=
  (cm.postcompose ma).preserve_admitsTrace h

/-- Left precomposition of `ErrSyncDataRefines` along a functional lockstep abstraction map
    (`absState : S₀ → S_c`, `absIn : In₀ → In_c`, `0 Classical.choice`). -/
def ErrSyncDataRefines.precomposeMap {S₀ Sc Sa In₀ Ic Ia Out Oa : Type}
    {C₀ : Machine S₀ In₀ Out} {C : Machine Sc Ic Out} {A : Machine Sa Ia Oa}
    {visIn : Ic → Option Ia} {visOut : Out → Oa}
    (absState : S₀ → Sc) (absIn : In₀ → Ic)
    (hInit : ∀ {s₀ : S₀}, C₀.Init s₀ → C.Init (absState s₀))
    (hStep : ∀ (s₀ : S₀) (i₀ : In₀),
      match C₀.step s₀ i₀ with
      | some (s₀', out) => C.step (absState s₀) (absIn i₀) = some (absState s₀', out)
      | none => C.step (absState s₀) (absIn i₀) = none ∧
          absState (C₀.errStep s₀ i₀) = C.errStep (absState s₀) (absIn i₀))
    (sim : ErrSyncDataRefines C A visIn visOut) :
    ErrSyncDataRefines C₀ A (fun i₀ => visIn (absIn i₀)) visOut where
  Rel s₀ a := sim.Rel (absState s₀) a
  absInit s₀ := sim.absInit (absState s₀)
  errVis s₀ i₀ := sim.errVis (absState s₀) (absIn i₀)
  init_ok hs₀ := sim.init_ok (hInit hs₀)
  sim_visible {s₀ s₀' a i₀ out j} hRel hStep₀ hVis := by
    have hEq := hStep s₀ i₀
    rw [hStep₀] at hEq
    exact sim.sim_visible hRel hEq hVis
  sim_internal {s₀ s₀' a i₀ out} hRel hStep₀ hVis := by
    have hEq := hStep s₀ i₀
    rw [hStep₀] at hEq
    exact sim.sim_internal hRel hEq hVis
  sim_reject_stutter {s₀ a i₀} hRel hNone₀ hEv := by
    have hEq := hStep s₀ i₀
    rw [hNone₀] at hEq
    rcases hEq with ⟨hNoneC, hErrEq⟩
    change sim.Rel (absState (C₀.errStep s₀ i₀)) a
    rw [hErrEq]
    exact sim.sim_reject_stutter hRel hNoneC hEv
  sim_reject_sync {s₀ a i₀ j} hRel hNone₀ hEv := by
    have hEq := hStep s₀ i₀
    rw [hNone₀] at hEq
    rcases hEq with ⟨hNoneC, hErrEq⟩
    obtain ⟨hNoneA, hRel'⟩ := sim.sim_reject_sync hRel hNoneC hEv
    refine ⟨hNoneA, ?_⟩
    change sim.Rel (absState (C₀.errStep s₀ i₀)) (A.errStep a j)
    rw [hErrEq]
    exact hRel'

/-- **General Multi-Step Stuttering Simulation (`IndexedSim`)**:
    Each concrete transition matches a finite `Machine.ValidTrace` segment of `A` (`0`, `1`, or `k`
    silent error steps plus the projected visible event). Closed under vertical transitivity! -/
structure IndexedSim {S_c S_a In_c In_a Out_c Out_a : Type}
    (C : Machine S_c In_c Out_c) (A : Machine S_a In_a Out_a)
    (visIn : In_c → Option In_a) (visOut : Out_c → Out_a) : Type 1 where
  Rel : S_c → S_a → Prop
  absInit : S_c → S_a
  init_ok : ∀ {c₀ : S_c}, C.Init c₀ → A.Init (absInit c₀) ∧ Rel c₀ (absInit c₀)
  sim_accept : ∀ {c c' : S_c} {a : S_a} {inp : In_c} {out : Out_c},
    Rel c a → C.step c inp = some (c', out) →
    ∃ a' : S_a,
      A.ValidTrace a (match visIn inp with | some j => [(j, visOut out)] | none => []) a' ∧
      Rel c' a'
  sim_reject : ∀ {c : S_c} {a : S_a} {inp : In_c},
    Rel c a → C.step c inp = none →
    ∃ a' : S_a, A.ValidTrace a [] a' ∧ Rel (C.errStep c inp) a'

/-- Every `ErrSyncDataRefines` embeds canonically into `IndexedSim`. -/
def ErrSyncDataRefines.toIndexedSim {S_c S_a In_c In_a Out_c Out_a : Type}
    {C : Machine S_c In_c Out_c} {A : Machine S_a In_a Out_a}
    {visIn : In_c → Option In_a} {visOut : Out_c → Out_a}
    (sim : ErrSyncDataRefines C A visIn visOut) :
    IndexedSim C A visIn visOut where
  Rel := sim.Rel
  absInit := sim.absInit
  init_ok := sim.init_ok
  sim_accept {c c' a inp out} hRel hStepC := by
    cases hVis : visIn inp with
    | some j =>
      obtain ⟨a', hStepA, hRel'⟩ := sim.sim_visible hRel hStepC hVis
      exact ⟨a', .accept hStepA (.nil a'), hRel'⟩
    | none =>
      exact ⟨a, .nil a, sim.sim_internal hRel hStepC hVis⟩
  sim_reject {c a inp} hRel hNoneC := by
    cases hEv : sim.errVis c inp with
    | none =>
      exact ⟨a, .nil a, sim.sim_reject_stutter hRel hNoneC hEv⟩
    | some j =>
      obtain ⟨hNoneA, hRel'⟩ := sim.sim_reject_sync hRel hNoneC hEv
      exact ⟨A.errStep a j, .reject j hNoneA (.nil _), hRel'⟩

theorem IndexedSim.lift_validTrace {S_c S_a In_c In_a Out_c Out_a : Type}
    {C : Machine S_c In_c Out_c} {A : Machine S_a In_a Out_a}
    {visIn : In_c → Option In_a} {visOut : Out_c → Out_a}
    (sim : IndexedSim C A visIn visOut)
    {c₀ c_final : S_c} {a₀ : S_a} {trace : List (In_c × Out_c)}
    (hRel₀ : sim.Rel c₀ a₀) (hTrC : C.ValidTrace c₀ trace c_final) :
    ∃ a_final : S_a,
      A.ValidTrace a₀ (projectTrace visIn visOut trace) a_final ∧ sim.Rel c_final a_final := by
  induction hTrC generalizing a₀ with
  | nil _ => exact ⟨a₀, .nil a₀, hRel₀⟩
  | @accept _ _ _ inp out _ hStepC _ ih =>
    obtain ⟨a', hSeg, hRel'⟩ := sim.sim_accept hRel₀ hStepC
    obtain ⟨a_final, hTrA, hRelFinal⟩ := ih hRel'
    refine ⟨a_final, ?_, hRelFinal⟩
    cases hVis : visIn inp with
    | some j =>
      rw [hVis] at hSeg
      simp only [projectTrace, hVis]
      exact Machine.ValidTrace.append hSeg hTrA
    | none =>
      rw [hVis] at hSeg
      simp only [projectTrace, hVis]
      exact Machine.ValidTrace.append hSeg hTrA
  | reject _ hNoneC _ ih =>
    obtain ⟨a', hSeg, hRel'⟩ := sim.sim_reject hRel₀ hNoneC
    obtain ⟨a_final, hTrA, hRelFinal⟩ := ih hRel'
    exact ⟨a_final, Machine.ValidTrace.append hSeg hTrA, hRelFinal⟩

theorem IndexedSim.preserve_admitsTrace {S_c S_a In_c In_a Out_c Out_a : Type}
    {C : Machine S_c In_c Out_c} {A : Machine S_a In_a Out_a}
    {visIn : In_c → Option In_a} {visOut : Out_c → Out_a}
    (sim : IndexedSim C A visIn visOut) {trace : List (In_c × Out_c)}
    (hAdmitsC : C.AdmitsTrace trace) :
    A.AdmitsTrace (projectTrace visIn visOut trace) := by
  rcases hAdmitsC with ⟨c₀, c_final, hInitC, hTraceC⟩
  obtain ⟨hInitA, hRel₀⟩ := sim.init_ok hInitC
  obtain ⟨a_final, hTraceA, _⟩ := sim.lift_validTrace hRel₀ hTraceC
  exact ⟨sim.absInit c₀, a_final, hInitA, hTraceA⟩

/-- Vertical transitivity of `IndexedSim` (`0 Classical.choice`). -/
def IndexedSim.trans {S₁ S₂ S₃ I₁ I₂ I₃ O₁ O₂ O₃ : Type}
    {M₁ : Machine S₁ I₁ O₁} {M₂ : Machine S₂ I₂ O₂} {M₃ : Machine S₃ I₃ O₃}
    {vIn₁₂ : I₁ → Option I₂} {vOut₁₂ : O₁ → O₂}
    {vIn₂₃ : I₂ → Option I₃} {vOut₂₃ : O₂ → O₃}
    (r₁₂ : IndexedSim M₁ M₂ vIn₁₂ vOut₁₂)
    (r₂₃ : IndexedSim M₂ M₃ vIn₂₃ vOut₂₃) :
    IndexedSim M₁ M₃ (fun i₁ => (vIn₁₂ i₁).bind vIn₂₃) (vOut₂₃ ∘ vOut₁₂) where
  Rel s₁ s₃ := ∃ s₂, r₁₂.Rel s₁ s₂ ∧ r₂₃.Rel s₂ s₃
  absInit s₁ := r₂₃.absInit (r₁₂.absInit s₁)
  init_ok hs₁ := by
    obtain ⟨hInit₂, h12⟩ := r₁₂.init_ok hs₁
    obtain ⟨hInit₃, h23⟩ := r₂₃.init_ok hInit₂
    exact ⟨hInit₃, r₁₂.absInit _, h12, h23⟩
  sim_accept {s₁ s₁' s₃ inp out} hRel hStep₁ := by
    rcases hRel with ⟨s₂, h12, h23⟩
    obtain ⟨s₂', hSeg₂, h12'⟩ := r₁₂.sim_accept h12 hStep₁
    obtain ⟨s₃', hSeg₃, h23'⟩ := r₂₃.lift_validTrace h23 hSeg₂
    refine ⟨s₃', ?_, s₂', h12', h23'⟩
    cases hv12 : vIn₁₂ inp with
    | none =>
      rw [hv12] at hSeg₃
      simpa only [Option.bind, projectTrace] using hSeg₃
    | some i₂ =>
      rw [hv12] at hSeg₃
      simp only [Option.bind]
      cases hv23 : vIn₂₃ i₂ with
      | none =>
        simpa only [projectTrace, hv23] using hSeg₃
      | some i₃ =>
        simp only [projectTrace, hv23] at hSeg₃
        exact hSeg₃
  sim_reject {s₁ s₃ inp} hRel hNone₁ := by
    rcases hRel with ⟨s₂, h12, h23⟩
    obtain ⟨s₂', hSeg₂, h12'⟩ := r₁₂.sim_reject h12 hNone₁
    obtain ⟨s₃', hSeg₃, h23'⟩ := r₂₃.lift_validTrace h23 hSeg₂
    exact ⟨s₃', hSeg₃, s₂', h12', h23'⟩

#verify_constructive
  Qsag.Spec.Machine.ValidTrace.append
  Qsag.Spec.ErrSyncDataRefines.lift_validTrace
  Qsag.Spec.ErrSyncDataRefines.preserve_admitsTrace
  Qsag.Spec.ErrSyncDataRefines.reachable_rel
  Qsag.Spec.ErrSyncDataRefines.preserve_trace_safety
  Qsag.Spec.ErrSyncDataRefines.postcompose_admits
  Qsag.Spec.IndexedSim.lift_validTrace
  Qsag.Spec.IndexedSim.preserve_admitsTrace

/-! ## 6. Anti-Replay Authenticated Network Transport Combinator (`NetworkChannelSim`) -/

/-- State of an `N`-party network communicating over a sender-authenticated, sequence-numbered,
    replay-protected point-to-point channel (`Spec.ChannelMsg` / `Spec.ChannelEvent`). -/
structure AuthChannelNetState (N : Nat) (PartySt : Type) where
  parties : Fin N → PartySt
  sent : List ChannelMsg
  delivered : List ChannelMsg

/-- Constructive point update on `Fin N → PartySt` (`0 Classical.choice`). -/
@[expose] def setPartySlot {N : Nat} {PartySt : Type}
    (ps : Fin N → PartySt) (r : Fin N) (v : PartySt) (i : Fin N) : PartySt :=
  if i = r then v else ps i

theorem setPartySlot_self {N : Nat} {PartySt : Type}
    (ps : Fin N → PartySt) (r : Fin N) (v : PartySt) :
    setPartySlot ps r v r = v := by
  simp [setPartySlot]

theorem setPartySlot_ne {N : Nat} {PartySt : Type}
    (ps : Fin N → PartySt) (r i : Fin N) (v : PartySt) (hNe : i ≠ r) :
    setPartySlot ps r v i = ps i := by
  simp [setPartySlot, hNe]

/-- **`N`-Party Authenticated Anti-Replay Transport Machine (`authChannelNetworkMachine`)**:
    Wraps per-party `Machine PartySt ChannelMsg Out` instances inside a transport layer that
    enforces `m ∈ sent ∧ m ∉ delivered` on every `.deliver m` event before invoking the
    destination party's `step` / `errStep`. -/
@[expose] def authChannelNetworkMachine {N : Nat} {PartySt Out : Type}
    (corruptSet : List (Fin N))
    (machines : Fin N → Machine PartySt ChannelMsg Out) :
    Machine (AuthChannelNetState N PartySt) ChannelEvent (Option Out) where
  Init s := s.sent = [] ∧ s.delivered = [] ∧
    ∀ (i : Fin N), i ∉ corruptSet → (machines i).Init (s.parties i)
  step s ev :=
    match ev with
    | .send m => some ({ s with sent := m :: s.sent }, none)
    | .deliver m =>
      if decide (m ∈ s.sent) && !decide (m ∈ s.delivered) then
        if h : m.receiver < N then
          let r : Fin N := ⟨m.receiver, h⟩
          if Qsag.isCorruptParty r corruptSet = false then
            match (machines r).step (s.parties r) m with
            | some (p', out) =>
              some ({ s with parties := setPartySlot s.parties r p',
                             delivered := m :: s.delivered }, some out)
            | none => none
          else
            some ({ s with delivered := m :: s.delivered }, none)
        else
          some ({ s with delivered := m :: s.delivered }, none)
      else
        none
  errStep s ev :=
    match ev with
    | .send _ => s
    | .deliver m =>
      if decide (m ∈ s.sent) && !decide (m ∈ s.delivered) then
        if h : m.receiver < N then
          let r : Fin N := ⟨m.receiver, h⟩
          if Qsag.isCorruptParty r corruptSet = false then
            match (machines r).step (s.parties r) m with
            | some _ => s
            | none => { s with parties := setPartySlot s.parties r ((machines r).errStep (s.parties r) m) }
          else s
        else s
      else s

/-- **Anti-Replay Tooth (`tooth_authChannelNetwork_replay_rejected`)**:
    Any second `.deliver m` for an already-delivered envelope `m ∈ s.delivered` is rejected
    at the transport boundary regardless of `machines` or `corruptSet`. -/
theorem tooth_authChannelNetwork_replay_rejected {N : Nat} {PartySt Out : Type}
    (corruptSet : List (Fin N))
    (machines : Fin N → Machine PartySt ChannelMsg Out)
    (s : AuthChannelNetState N PartySt) (m : ChannelMsg)
    (hReplay : m ∈ s.delivered) :
    (authChannelNetworkMachine corruptSet machines).step s (.deliver m) = none := by
  dsimp only [authChannelNetworkMachine]
  rw [decide_eq_true hReplay]
  simp

/-- **Unauthenticated Injection Tooth (`tooth_authChannelNetwork_unauthenticated_rejected`)**:
    Any `.deliver m` for an unsent envelope `m ∉ s.sent` is rejected at the transport boundary. -/
theorem tooth_authChannelNetwork_unauthenticated_rejected {N : Nat} {PartySt Out : Type}
    (corruptSet : List (Fin N))
    (machines : Fin N → Machine PartySt ChannelMsg Out)
    (s : AuthChannelNetState N PartySt) (m : ChannelMsg)
    (hUnsent : m ∉ s.sent) :
    (authChannelNetworkMachine corruptSet machines).step s (.deliver m) = none := by
  dsimp only [authChannelNetworkMachine]
  rw [decide_eq_false hUnsent]
  simp

/-- **Horizontal `N`-Party Anti-Replay Network Refinement (`NetworkChannelSim`)**:
    Lifts per-party refinements `∀ i ∉ corruptSet, C i ⊑ A i` across the sequence-numbered
    authenticated anti-replay transport layer (`authChannelNetworkMachine ... C ⊑ ... A`)! -/
def NetworkChannelSim {N : Nat} {S_c S_a Out : Type}
    (corruptSet : List (Fin N))
    (C : Fin N → Machine S_c ChannelMsg Out)
    (A : Fin N → Machine S_a ChannelMsg Out)
    (defaultAbs : Fin N → S_c → S_a)
    (sims : ∀ (i : Fin N), i ∉ corruptSet → C i ⊑ A i) :
    authChannelNetworkMachine corruptSet C ⊑ authChannelNetworkMachine corruptSet A where
  Rel sc sa :=
    sa.sent = sc.sent ∧
    sa.delivered = sc.delivered ∧
    ∀ (i : Fin N) (hi : i ∉ corruptSet), (sims i hi).Rel (sc.parties i) (sa.parties i)
  absInit sc :=
    { parties := fun i =>
        if h : Qsag.isCorruptParty i corruptSet = false then
          (sims i ((Qsag.isCorruptParty_eq_false_iff i corruptSet).mp h)).absInit (sc.parties i)
        else
          defaultAbs i (sc.parties i)
      sent := sc.sent
      delivered := sc.delivered }
  init_ok {sc} hInit := by
    rcases hInit with ⟨hSent, hDel, hParties⟩
    refine ⟨⟨hSent, hDel, ?_⟩, rfl, rfl, ?_⟩
    · intro i hiNotCorr
      have hFalse : Qsag.isCorruptParty i corruptSet = false :=
        (Qsag.isCorruptParty_eq_false_iff i corruptSet).mpr hiNotCorr
      dsimp only
      split
      · exact ((sims i _).init_ok (hParties i hiNotCorr)).1
      · rename_i hNot; exact False.elim (hNot hFalse)
    · intro i hiNotCorr
      have hFalse : Qsag.isCorruptParty i corruptSet = false :=
        (Qsag.isCorruptParty_eq_false_iff i corruptSet).mpr hiNotCorr
      dsimp only
      split
      · rename_i hCond
        have hSub : (Qsag.isCorruptParty_eq_false_iff i corruptSet).mp hCond = hiNotCorr :=
          Subsingleton.elim _ _
        rw [hSub]
        exact ((sims i hiNotCorr).init_ok (hParties i hiNotCorr)).2
      · rename_i hNot; exact False.elim (hNot hFalse)
  sim_ok {sc sc' sa ev out} hRel hStepC := by
    rcases hRel with ⟨hSent, hDel, hPRel⟩
    cases ev with
    | send m =>
      dsimp only [authChannelNetworkMachine] at hStepC ⊢
      injection hStepC with hPair
      rcases Prod.mk.inj hPair with ⟨rfl, rfl⟩
      exact ⟨rfl, congrArg (m :: ·) hSent, hDel, hPRel⟩
    | deliver m =>
      dsimp only [authChannelNetworkMachine] at hStepC ⊢
      rw [hSent, hDel]
      cases hChk : (decide (m ∈ sc.sent) && !decide (m ∈ sc.delivered)) with
      | false => rw [hChk] at hStepC; cases hStepC
      | true =>
        rw [hChk] at hStepC
        simp only [↓reduceIte] at hStepC ⊢
        by_cases hLt : m.receiver < N
        · simp only [hLt, ↓reduceDIte] at hStepC ⊢
          cases hCorr : Qsag.isCorruptParty ⟨m.receiver, hLt⟩ corruptSet with
          | true =>
            rw [hCorr] at hStepC
            simp only [Bool.true_eq_false, ↓reduceIte] at hStepC ⊢
            injection hStepC with hPair
            rcases Prod.mk.inj hPair with ⟨rfl, rfl⟩
            exact ⟨rfl, rfl, rfl, hPRel⟩
          | false =>
            rw [hCorr] at hStepC
            simp only [↓reduceIte] at hStepC ⊢
            have hrNot : (⟨m.receiver, hLt⟩ : Fin N) ∉ corruptSet :=
              (Qsag.isCorruptParty_eq_false_iff ⟨m.receiver, hLt⟩ corruptSet).mp hCorr
            cases hStepPartyC : (C ⟨m.receiver, hLt⟩).step (sc.parties ⟨m.receiver, hLt⟩) m with
            | none => rw [hStepPartyC] at hStepC; cases hStepC
            | some pairC =>
              rw [hStepPartyC] at hStepC
              rcases pairC with ⟨pC', outC⟩
              injection hStepC with hPair
              rcases Prod.mk.inj hPair with ⟨rfl, rfl⟩
              have hSimOk := (sims ⟨m.receiver, hLt⟩ hrNot).sim_ok (hPRel ⟨m.receiver, hLt⟩ hrNot) hStepPartyC
              cases hStepPartyA : (A ⟨m.receiver, hLt⟩).step (sa.parties ⟨m.receiver, hLt⟩) m with
              | none => rw [hStepPartyA] at hSimOk; exact False.elim hSimOk
              | some pairA =>
                rw [hStepPartyA] at hSimOk
                rcases pairA with ⟨pA', outA⟩
                rcases hSimOk with ⟨rfl, hRelR'⟩
                refine ⟨rfl, rfl, rfl, ?_⟩
                intro i hiNot
                dsimp only
                by_cases hir : i = ⟨m.receiver, hLt⟩
                · subst hir
                  rw [setPartySlot_self, setPartySlot_self]
                  exact hRelR'
                · rw [setPartySlot_ne _ _ _ _ hir, setPartySlot_ne _ _ _ _ hir]
                  exact hPRel i hiNot
        · simp only [hLt, ↓reduceDIte] at hStepC ⊢
          injection hStepC with hPair
          rcases Prod.mk.inj hPair with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl, hPRel⟩
  sim_err {sc sa ev} hRel hNoneC := by
    rcases hRel with ⟨hSent, hDel, hPRel⟩
    cases ev with
    | send m =>
      dsimp only [authChannelNetworkMachine] at hNoneC
      cases hNoneC
    | deliver m =>
      dsimp only [authChannelNetworkMachine] at hNoneC ⊢
      rw [hSent, hDel]
      cases hChk : (decide (m ∈ sc.sent) && !decide (m ∈ sc.delivered)) with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨trivial, hSent, hDel, hPRel⟩
      | true =>
        rw [hChk] at hNoneC
        simp only [↓reduceIte] at hNoneC ⊢
        by_cases hLt : m.receiver < N
        · simp only [hLt, ↓reduceDIte] at hNoneC ⊢
          cases hCorr : Qsag.isCorruptParty ⟨m.receiver, hLt⟩ corruptSet with
          | true =>
            rw [hCorr] at hNoneC
            simp only [Bool.true_eq_false, ↓reduceIte] at hNoneC
            cases hNoneC
          | false =>
            rw [hCorr] at hNoneC
            simp only [↓reduceIte] at hNoneC ⊢
            have hrNot : (⟨m.receiver, hLt⟩ : Fin N) ∉ corruptSet :=
              (Qsag.isCorruptParty_eq_false_iff ⟨m.receiver, hLt⟩ corruptSet).mp hCorr
            cases hStepPartyC : (C ⟨m.receiver, hLt⟩).step (sc.parties ⟨m.receiver, hLt⟩) m with
            | some _ => rw [hStepPartyC] at hNoneC; cases hNoneC
            | none =>
              obtain ⟨hStepPartyA, hRelR'⟩ :=
                (sims ⟨m.receiver, hLt⟩ hrNot).sim_err (hPRel ⟨m.receiver, hLt⟩ hrNot) hStepPartyC
              rw [hStepPartyA]
              dsimp only
              refine ⟨rfl, rfl, rfl, ?_⟩
              intro i hiNot
              by_cases hir : i = ⟨m.receiver, hLt⟩
              · subst hir
                rw [setPartySlot_self, setPartySlot_self]
                exact hRelR'
              · rw [setPartySlot_ne _ _ _ _ hir, setPartySlot_ne _ _ _ _ hir]
                exact hPRel i hiNot
        · simp only [hLt, ↓reduceDIte] at hNoneC
          cases hNoneC

private theorem authChannel_errStep_wire_eq {N : Nat} {PartySt Out : Type}
    (corruptSet : List (Fin N))
    (machines : Fin N → Machine PartySt ChannelMsg Out)
    (s : AuthChannelNetState N PartySt) (ev : ChannelEvent) :
    ((authChannelNetworkMachine corruptSet machines).errStep s ev).sent = s.sent ∧
      ((authChannelNetworkMachine corruptSet machines).errStep s ev).delivered = s.delivered := by
  cases ev with
  | send _ => exact ⟨rfl, rfl⟩
  | deliver m =>
    dsimp only [authChannelNetworkMachine]
    split
    · split
      · split
        · split <;> exact ⟨rfl, rfl⟩
        · exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩

private theorem authChannel_deliver_step_wire {N : Nat} {PartySt Out : Type}
    {corruptSet : List (Fin N)}
    {machines : Fin N → Machine PartySt ChannelMsg Out}
    {s s' : AuthChannelNetState N PartySt} {m : ChannelMsg} {out : Option Out}
    (hStep : (authChannelNetworkMachine corruptSet machines).step s (.deliver m) = some (s', out)) :
    m ∈ s.sent ∧ m ∉ s.delivered ∧ s'.sent = s.sent ∧ s'.delivered = m :: s.delivered := by
  dsimp only [authChannelNetworkMachine] at hStep
  cases hChk : (decide (m ∈ s.sent) && !decide (m ∈ s.delivered)) with
  | false => rw [hChk] at hStep; cases hStep
  | true =>
    rw [hChk] at hStep
    simp only [↓reduceIte] at hStep
    obtain ⟨hInB, hNotDelB⟩ := Bool.and_eq_true_iff.mp hChk
    have hIn : m ∈ s.sent := of_decide_eq_true hInB
    have hNotDel : m ∉ s.delivered := by
      intro hMem
      rw [decide_eq_true hMem] at hNotDelB
      cases hNotDelB
    refine ⟨hIn, hNotDel, ?_⟩
    by_cases hLt : m.receiver < N
    · simp only [hLt, ↓reduceDIte] at hStep
      cases hC : Qsag.isCorruptParty ⟨m.receiver, hLt⟩ corruptSet with
      | true =>
        rw [hC] at hStep
        simp only [Bool.true_eq_false, ↓reduceIte] at hStep
        injection hStep with hP; rcases Prod.mk.inj hP with ⟨rfl, _⟩; exact ⟨rfl, rfl⟩
      | false =>
        rw [hC] at hStep
        simp only [↓reduceIte] at hStep
        cases hM : (machines ⟨m.receiver, hLt⟩).step (s.parties ⟨m.receiver, hLt⟩) m with
        | none => rw [hM] at hStep; cases hStep
        | some pm =>
          rw [hM] at hStep
          injection hStep with hP; rcases Prod.mk.inj hP with ⟨rfl, _⟩; exact ⟨rfl, rfl⟩
    · simp only [hLt, ↓reduceDIte] at hStep
      injection hStep with hP; rcases Prod.mk.inj hP with ⟨rfl, _⟩; exact ⟨rfl, rfl⟩

private theorem authChannel_delivered_absent {N : Nat} {PartySt Out : Type}
    {corruptSet : List (Fin N)}
    {machines : Fin N → Machine PartySt ChannelMsg Out} (m : ChannelMsg)
    {s₀ sF : AuthChannelNetState N PartySt} {tr : List (ChannelEvent × Option Out)}
    (hTr : (authChannelNetworkMachine corruptSet machines).ValidTrace s₀ tr sF)
    (hDl : m ∈ s₀.delivered) :
    .deliver m ∉ tr.map Prod.fst := by
  induction hTr with
  | nil _ => exact fun h => nomatch h
  | @accept s _ _ ev _ _ hStep _ ih =>
    cases ev with
    | send m' =>
      dsimp only [authChannelNetworkMachine] at hStep
      injection hStep with hP; rcases Prod.mk.inj hP with ⟨rfl, _⟩
      intro hMem
      rcases List.mem_cons.mp hMem with hEq | hTail
      · cases hEq
      · exact ih hDl hTail
    | deliver m' =>
      obtain ⟨_, hNotDl, _, hDel'⟩ := authChannel_deliver_step_wire hStep
      intro hMem
      rcases List.mem_cons.mp hMem with hEq | hTail
      · injection hEq with hM
        subst hM
        exact hNotDl hDl
      · exact ih (hDel' ▸ List.mem_cons_of_mem m' hDl) hTail
  | @reject s _ ev _ _ _ ih =>
    have hW := authChannel_errStep_wire_eq corruptSet machines s ev
    exact ih (hW.2.symm ▸ hDl)

private theorem authChannel_authentic_or_sent {N : Nat} {PartySt Out : Type}
    {corruptSet : List (Fin N)}
    {machines : Fin N → Machine PartySt ChannelMsg Out}
    (m : ChannelMsg)
    {s₀ sF : AuthChannelNetState N PartySt} {tr : List (ChannelEvent × Option Out)}
    (hTr : (authChannelNetworkMachine corruptSet machines).ValidTrace s₀ tr sF) :
    ∀ {pre post : List ChannelEvent},
      tr.map Prod.fst = pre ++ .deliver m :: post →
      m ∈ s₀.sent ∨ .send m ∈ pre := by
  induction hTr with
  | nil _ =>
    intro pre _ hEq
    cases pre <;> cases hEq
  | @accept s _ _ ev _ _ hStep _ ih =>
    intro pre post hEq
    cases ev with
    | send m' =>
      dsimp only [authChannelNetworkMachine] at hStep
      injection hStep with hP; rcases Prod.mk.inj hP with ⟨rfl, _⟩
      cases pre with
      | nil => cases hEq
      | cons e preTail =>
        injection hEq with hHead hTail
        subst hHead
        rcases ih hTail with hInSent | hInPre
        · rcases List.mem_cons.mp hInSent with rfl | hOld
          · exact .inr (List.Mem.head preTail)
          · exact .inl hOld
        · exact .inr (List.mem_cons_of_mem _ hInPre)
    | deliver m' =>
      obtain ⟨hInSent, _, hSent', _⟩ := authChannel_deliver_step_wire hStep
      cases pre with
      | nil =>
        injection hEq with hHead _
        injection hHead with hM
        subst hM
        exact .inl hInSent
      | cons e preTail =>
        injection hEq with hHead hTail
        subst hHead
        rcases ih hTail with hInSent' | hInPre
        · exact .inl (hSent' ▸ hInSent')
        · exact .inr (List.mem_cons_of_mem _ hInPre)
  | @reject s _ ev _ _ _ ih =>
    intro pre post hEq
    have hW := authChannel_errStep_wire_eq corruptSet machines s ev
    rcases ih hEq with hInSent' | hInPre
    · exact .inl (hW.1 ▸ hInSent')
    · exact .inr hInPre

private theorem authChannel_no_replay_trace {N : Nat} {PartySt Out : Type}
    {corruptSet : List (Fin N)}
    {machines : Fin N → Machine PartySt ChannelMsg Out}
    (m : ChannelMsg)
    {s₀ sF : AuthChannelNetState N PartySt} {tr : List (ChannelEvent × Option Out)}
    (hTr : (authChannelNetworkMachine corruptSet machines).ValidTrace s₀ tr sF) :
    ∀ {pre post : List ChannelEvent},
      tr.map Prod.fst = pre ++ .deliver m :: post →
      .deliver m ∉ post := by
  induction hTr with
  | nil _ =>
    intro pre _ hEq
    cases pre <;> cases hEq
  | @accept _ _ _ ev _ hRest' hStep hRest ih =>
    intro pre post hEq
    cases ev with
    | send m' =>
      cases pre with
      | nil => cases hEq
      | cons _ preTail =>
        injection hEq with _ hTail
        exact ih hTail
    | deliver m' =>
      obtain ⟨_, _, _, hDel'⟩ := authChannel_deliver_step_wire hStep
      cases pre with
      | nil =>
        injection hEq with hHead hTail
        injection hHead with hM
        subst hM
        have hAbs := authChannel_delivered_absent m' hRest (hDel' ▸ List.Mem.head _)
        rw [hTail] at hAbs
        exact hAbs
      | cons _ preTail =>
        injection hEq with _ hTail
        exact ih hTail
  | reject _ _ _ ih =>
    intro _ _ hEq
    exact ih hEq

/-- **Universal Peer-Authentication & Anti-Replay Theorem (`authChannelNetwork_trace_authentic_and_replay_free`)**:
    Along EVERY initialized trace of `authChannelNetworkMachine corruptSet machines`:
    1. Every `.deliver m` is preceded by `.send m`, and
    2. No message `m` is ever delivered twice! -/
theorem authChannelNetwork_trace_authentic_and_replay_free {N : Nat} {PartySt Out : Type}
    (corruptSet : List (Fin N))
    (machines : Fin N → Machine PartySt ChannelMsg Out)
    {tr : List (ChannelEvent × Option Out)}
    (hAdmits : (authChannelNetworkMachine corruptSet machines).AdmitsTrace tr) :
    (∀ (pre post : List ChannelEvent) (m : ChannelMsg),
      tr.map Prod.fst = pre ++ .deliver m :: post → .send m ∈ pre) ∧
    (∀ (pre post : List ChannelEvent) (m : ChannelMsg),
      tr.map Prod.fst = pre ++ .deliver m :: post → .deliver m ∉ post) := by
  rcases hAdmits with ⟨s₀, sF, ⟨hSent₀, _, _⟩, hTr⟩
  refine ⟨fun pre post m hEq => ?_, fun pre post m hEq => authChannel_no_replay_trace m hTr hEq⟩
  rcases authChannel_authentic_or_sent m hTr hEq with hIn₀ | hPre
  · rw [hSent₀] at hIn₀; cases hIn₀
  · exact hPre

/-- Canonical receptive party machine (accepts every authenticated envelope). -/
def receptiveChannelParty : Machine Unit ChannelMsg ChannelMsg :=
  Machine.ofTotal (fun _ => True) (fun _ m => ((), m))

private theorem receptive_honestSchedule_trace {N : Nat} (corruptSet : List (Fin N)) :
    ∀ (msgs : List ChannelMsg) (s : AuthChannelNetState N Unit),
      msgs.Nodup →
      (∀ m ∈ msgs, m ∉ s.delivered) →
      ∃ (sF : AuthChannelNetState N Unit) (tr : List (ChannelEvent × Option ChannelMsg)),
        tr.map Prod.fst = msgs.flatMap (fun m => [.send m, .deliver m]) ∧
        (authChannelNetworkMachine corruptSet (fun _ => receptiveChannelParty)).ValidTrace s tr sF
  | [], s, _, _ => ⟨s, [], rfl, .nil s⟩
  | m :: rest, s, hNd, hFresh => by
    obtain ⟨hNotInRest, hNdRest⟩ := List.nodup_cons.mp hNd
    let s₁ : AuthChannelNetState N Unit := { s with sent := m :: s.sent }
    have hSend : (authChannelNetworkMachine corruptSet (fun _ => receptiveChannelParty)).step
        s (.send m) = some (s₁, none) := rfl
    have hInSent : decide (m ∈ s₁.sent) = true := decide_eq_true (List.Mem.head s.sent)
    have hNotInDel : decide (m ∈ s₁.delivered) = false :=
      decide_eq_false (hFresh m (List.Mem.head rest))
    have hDeliver : ∃ (s₂ : AuthChannelNetState N Unit) (o : Option ChannelMsg),
        (authChannelNetworkMachine corruptSet (fun _ => receptiveChannelParty)).step
          s₁ (.deliver m) = some (s₂, o) ∧ s₂.delivered = m :: s.delivered := by
      dsimp only [authChannelNetworkMachine]
      rw [hInSent, hNotInDel]
      simp only [Bool.not_false, Bool.and_self, ↓reduceIte]
      by_cases hLt : m.receiver < N
      · simp only [hLt, ↓reduceDIte]
        cases hC : Qsag.isCorruptParty ⟨m.receiver, hLt⟩ corruptSet with
        | true =>
          simp only [Bool.true_eq_false, ↓reduceIte]
          exact ⟨_, _, rfl, rfl⟩
        | false =>
          simp only [↓reduceIte, receptiveChannelParty, Machine.ofTotal]
          exact ⟨_, _, rfl, rfl⟩
      · simp only [hLt, ↓reduceDIte]
        exact ⟨_, _, rfl, rfl⟩
    obtain ⟨s₂, out, hDelStep, hDelEq⟩ := hDeliver
    have hFresh₂ : ∀ m' ∈ rest, m' ∉ s₂.delivered := by
      intro m' hm' hMem
      rw [hDelEq] at hMem
      rcases List.mem_cons.mp hMem with rfl | hOld
      · exact hNotInRest hm'
      · exact hFresh m' (List.mem_cons_of_mem m hm') hOld
    obtain ⟨sF, trRest, hMapRest, hTrRest⟩ :=
      receptive_honestSchedule_trace corruptSet rest s₂ hNdRest hFresh₂
    refine ⟨sF, (.send m, none) :: (.deliver m, out) :: trRest, ?_,
      .accept hSend (.accept hDelStep hTrRest)⟩
    simp only [List.map_cons, List.flatMap_cons, List.cons_append, List.nil_append, hMapRest]

/-- **Completeness of `authChannelNetworkMachine` on Honest Non-Duplicate Schedules**:
    Every `Nodup` message sequence `msgs` is admitted along `msgs.flatMap (fun m => [.send m, .deliver m])`. -/
theorem authChannelNetwork_admits_honest_schedule (N : Nat) (corruptSet : List (Fin N))
    (msgs : List ChannelMsg) (hNd : msgs.Nodup) :
    ∃ tr, tr.map Prod.fst = msgs.flatMap (fun m => [.send m, .deliver m]) ∧
      (authChannelNetworkMachine corruptSet (fun _ => receptiveChannelParty)).AdmitsTrace tr := by
  let s₀ : AuthChannelNetState N Unit := ⟨fun _ => (), [], []⟩
  obtain ⟨sF, tr, hMap, hTr⟩ :=
    receptive_honestSchedule_trace corruptSet msgs s₀ hNd (fun _ _ h => nomatch h)
  exact ⟨tr, hMap, s₀, sF, ⟨rfl, rfl, fun _ _ => trivial⟩, hTr⟩

theorem inhabited_authChannelNetwork_honest_run :
    ∃ (N : Nat) (corruptSet : List (Fin N)) (msgs : List ChannelMsg)
      (tr : List (ChannelEvent × Option ChannelMsg)),
      msgs.Nodup ∧
      (authChannelNetworkMachine corruptSet (fun _ => receptiveChannelParty)).AdmitsTrace tr := by
  have hNd : ([⟨0, 1, 0, [0x42]⟩] : List ChannelMsg).Nodup := by decide
  obtain ⟨tr, _, hAdm⟩ := authChannelNetwork_admits_honest_schedule 2 [] [⟨0, 1, 0, [0x42]⟩] hNd
  exact ⟨2, [], [⟨0, 1, 0, [0x42]⟩], tr, hNd, hAdm⟩

#verify_constructive
  Qsag.Spec.tooth_authChannelNetwork_replay_rejected
  Qsag.Spec.tooth_authChannelNetwork_unauthenticated_rejected
  Qsag.Spec.authChannelNetwork_trace_authentic_and_replay_free
  Qsag.Spec.authChannelNetwork_admits_honest_schedule
#verify_inhabited Qsag.Spec.authChannelNetwork_admits_honest_schedule
  Qsag.Spec.inhabited_authChannelNetwork_honest_run
#tooth_pair Qsag.Spec.authChannelNetwork_trace_authentic_and_replay_free vs
  Qsag.Spec.tooth_authChannelNetwork_replay_rejected
#tooth_pair Qsag.Spec.authChannelNetwork_trace_authentic_and_replay_free vs
  Qsag.Spec.tooth_authChannelNetwork_unauthenticated_rejected

end Qsag.Spec
end
