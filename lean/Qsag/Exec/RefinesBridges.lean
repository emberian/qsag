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
