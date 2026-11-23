module
/-
# Qsag.Exec.Tactic.SimulationKit — Simulation Spine Synthesis, `DataRefinement`, `LawfulFramedCodec`, `frame_prefix_inj` & Coalgebraic Machine Repair

Zero-`Classical.choice` proof-automation and coalgebraic refinement combinator kit for `Spec ↔ Exec ↔ MIR`:
1. **`by compose_forward_sim` / `by compose_refines`**: Goal-directed `TacticM` DFS synthesizer
   chaining `ForwardSim`, `LockstepSim`, `Spec.Refines`, `Spec.LockstepSim`, AND `MachineStateEquiv`
   links with a bounded search.
2. **`by mir_sim_step`**: Bounded structural symbolic splitter over `Option` and `Except`.
3. **`DataRefinement α_spec α_exec` (`Rel1`, `Rel2`, `option_rel`, `list_rel`, `vec_rel`, carrier bridges)**:
   Composable relational & functional data-refinement combinators connecting `List UInt8`, `Nat`,
   `BitVec`, `Digest256` specs to `ByteArray`, `UInt64`, `UInt32`, and length-indexed byte slices.
4. **`LawfulFramedCodec`, `FramedField`, `framePair_inj`, `frameList_inj` & `by frame_prefix_inj`**:
   Composable prefix-free byte-framing combinators + automatic prefix-peeling tactic collapsing
   multi-field Merkle/transcript/intent preimage injectivity (including `boundedList` / `frameList_inj`
   and `tagged`) to 1 line!
5. **Coalgebraic State-Machine Equivalence & Scar-Free Repair (`MachineStateEquiv`, `MealyCoalg`)**:
   Connects `Spec.Machine S₁ In Out ⇄ Spec.Machine S₂ In Out` to `Qsag.Repair.PCoalg` and transports
   both `Spec.Refines` and `Spec.DataRefines` across isomorphic state representations (`S₁ ≃ S₂`),
   with `#assert_no_scar` verification.
-/

public import Qsag.Tactic.AssuranceKit
public import Qsag.Tactic.CathedralKit
public import Qsag.Math.Tactic.MaskBijection
public import Qsag.Math.AlgebraicRepair
public import Qsag.Spec.Encoding
public import Qsag.Exec.SimulationSpine
public import Qsag.Exec.RefinesBridges
public meta import Lean

public section

namespace Qsag

set_option autoImplicit false

/-! ## 0. Coalgebraic State-Machine Equivalence & Repair Transport (`MachineStateEquiv`) -/

/-- Equivalence between two `Spec.Machine`s over a state bijection `e : SimpleEquiv S₁ S₂`
    commuting with `Init`, `step`, and `errStep`. -/
structure MachineStateEquiv {S₁ S₂ In Out : Type}
    (M₁ : Spec.Machine S₁ In Out) (M₂ : Spec.Machine S₂ In Out) where
  equiv : SimpleEquiv S₁ S₂
  init_iff : ∀ s₁ : S₁, M₁.Init s₁ ↔ M₂.Init (equiv.toFun s₁)
  step_comm : ∀ (s₁ : S₁) (inp : In),
    M₂.step (equiv.toFun s₁) inp =
      (M₁.step s₁ inp).map (fun p => (equiv.toFun p.1, p.2))
  errStep_comm : ∀ (s₁ : S₁) (inp : In),
    M₂.errStep (equiv.toFun s₁) inp = equiv.toFun (M₁.errStep s₁ inp)

namespace MachineStateEquiv

/-- Symmetric `MachineStateEquiv` (`M₂ ⇄ M₁`). -/
def symm {S₁ S₂ In Out : Type}
    {M₁ : Spec.Machine S₁ In Out} {M₂ : Spec.Machine S₂ In Out}
    (E : MachineStateEquiv M₁ M₂) : MachineStateEquiv M₂ M₁ where
  equiv := SimpleEquiv.symm E.equiv
  init_iff s₂ := by
    have h := E.init_iff (E.equiv.invFun s₂)
    rw [E.equiv.right_inv] at h
    exact h.symm
  step_comm s₂ inp := by
    dsimp only [SimpleEquiv.symm]
    have h := E.step_comm (E.equiv.invFun s₂) inp
    rw [E.equiv.right_inv] at h
    rw [h]
    cases M₁.step (E.equiv.invFun s₂) inp with
    | none => rfl
    | some p =>
      rcases p with ⟨s₁', out⟩
      dsimp only [Option.map]
      rw [E.equiv.left_inv]
  errStep_comm s₂ inp := by
    dsimp only [SimpleEquiv.symm]
    have h := congrArg E.equiv.invFun (E.errStep_comm (E.equiv.invFun s₂) inp)
    rw [E.equiv.right_inv, E.equiv.left_inv] at h
    exact h.symm

/-- Forward `Spec.Refines` (`M₁ ⊑ M₂`) induced by a `MachineStateEquiv`. -/
def toRefines {S₁ S₂ In Out : Type}
    {M₁ : Spec.Machine S₁ In Out} {M₂ : Spec.Machine S₂ In Out}
    (E : MachineStateEquiv M₁ M₂) : Spec.Refines M₁ M₂ :=
  Spec.LockstepSim.toRefines
    { Inv := fun _ => True
      abs := E.equiv.toFun
      init_inv := fun {s₀} hInit => ⟨trivial, (E.init_iff s₀).mp hInit⟩
      step_eq := fun {s₁} inp _ => by
        have hStep := E.step_comm s₁ inp
        cases hs : M₁.step s₁ inp with
        | some pair =>
          rw [hs] at hStep
          exact ⟨trivial, hStep⟩
        | none =>
          rw [hs] at hStep
          exact ⟨trivial, hStep, (E.errStep_comm s₁ inp).symm⟩ }

/-- Backward `Spec.Refines` (`M₂ ⊑ M₁`) induced by a `MachineStateEquiv`. -/
def toRefinesSymm {S₁ S₂ In Out : Type}
    {M₁ : Spec.Machine S₁ In Out} {M₂ : Spec.Machine S₂ In Out}
    (E : MachineStateEquiv M₁ M₂) : Spec.Refines M₂ M₁ :=
  E.symm.toRefines

/-- Exact trace-set equivalence (`M₁.AdmitsTrace tr ↔ M₂.AdmitsTrace tr`) across `MachineStateEquiv`. -/
theorem admitsTrace_iff {S₁ S₂ In Out : Type}
    {M₁ : Spec.Machine S₁ In Out} {M₂ : Spec.Machine S₂ In Out}
    (E : MachineStateEquiv M₁ M₂) (tr : List (In × Out)) :
    M₁.AdmitsTrace tr ↔ M₂.AdmitsTrace tr :=
  ⟨E.toRefines.preserve_admitsTrace, E.toRefinesSymm.preserve_admitsTrace⟩

/-- **Coalgebraic `DataRefines` Repair (`transportDataRefinesLeft`)**:
    Any interface-abstracting stuttering refinement `Spec.DataRefines M₁ A visIn visOut` repairs
    automatically along `E : MachineStateEquiv M₁ M₂` to `Spec.DataRefines M₂ A visIn visOut`! -/
def transportDataRefinesLeft {S₁ S₂ S_a In_c In_a Out_c Out_a : Type}
    {M₁ : Spec.Machine S₁ In_c Out_c} {M₂ : Spec.Machine S₂ In_c Out_c}
    {A : Spec.Machine S_a In_a Out_a}
    {visIn : In_c → Option In_a} {visOut : Out_c → Out_a}
    (E : MachineStateEquiv M₁ M₂)
    (D : Spec.DataRefines M₁ A visIn visOut) :
    Spec.DataRefines M₂ A visIn visOut where
  Rel s₂ a := D.Rel (E.equiv.invFun s₂) a
  absInit s₂ := D.absInit (E.equiv.invFun s₂)
  init_ok {s₂} hInit₂ := by
    have hInit₁ : M₁.Init (E.equiv.invFun s₂) :=
      (E.init_iff (E.equiv.invFun s₂)).mpr (by rw [E.equiv.right_inv]; exact hInit₂)
    exact D.init_ok hInit₁
  sim_visible {s₂ s₂' a inp out j} hRel hStep₂ hVis := by
    have hComm := E.symm.step_comm s₂ inp
    dsimp only [MachineStateEquiv.symm, SimpleEquiv.symm] at hComm
    rw [hStep₂] at hComm
    dsimp only [Option.map] at hComm
    exact D.sim_visible hRel hComm hVis
  sim_internal {s₂ s₂' a inp out} hRel hStep₂ hNone := by
    have hComm := E.symm.step_comm s₂ inp
    dsimp only [MachineStateEquiv.symm, SimpleEquiv.symm] at hComm
    rw [hStep₂] at hComm
    dsimp only [Option.map] at hComm
    exact D.sim_internal hRel hComm hNone
  sim_reject {s₂ a inp} hRel hNone₂ := by
    have hComm := E.symm.step_comm s₂ inp
    dsimp only [MachineStateEquiv.symm, SimpleEquiv.symm] at hComm
    rw [hNone₂] at hComm
    dsimp only [Option.map] at hComm
    have hRej := D.sim_reject hRel hComm
    have hEqInv : M₁.errStep (E.equiv.invFun s₂) inp = E.equiv.invFun (M₂.errStep s₂ inp) := by
      have hE := E.symm.errStep_comm s₂ inp
      dsimp only [MachineStateEquiv.symm, SimpleEquiv.symm] at hE
      exact hE
    rw [← hEqInv]
    exact hRej

/-- View any `Spec.Machine S In Out` as a polynomial coalgebra `Repair.PCoalg (In → Option Out) (fun _ => In) S`
    via `Machine.runStep`. -/
def toMealyPCoalg {S In Out : Type} (M : Spec.Machine S In Out) :
    Repair.PCoalg (In → Option Out) (fun _ => In) S where
  out s := ⟨fun inp => (M.runStep s inp).2, fun inp => (M.runStep s inp).1⟩

private theorem const_pos_cast {A C In : Type} {a₁ a₂ : A}
    (f : In → C) (h : a₁ = a₂) (inp : (fun _ : A => In) a₁) :
    (f (h ▸ inp : (fun _ : A => In) a₂)) = f inp := by
  subst h
  rfl

/-- Every `MachineStateEquiv M₁ M₂` induces a coalgebraic bisimulation between `M₁` and `M₂` on
    the sum carrier `Sum S₁ S₂`. -/
theorem machineStateEquiv_sum_bisim {S₁ S₂ In Out : Type}
    {M₁ : Spec.Machine S₁ In Out} {M₂ : Spec.Machine S₂ In Out}
    (E : MachineStateEquiv M₁ M₂) :
    let sumCoalg : Repair.PCoalg (In → Option Out) (fun _ => In) (Sum S₁ S₂) :=
      { out := fun
          | .inl s₁ => ⟨fun i => (M₁.runStep s₁ i).2, fun i => .inl (M₁.runStep s₁ i).1⟩
          | .inr s₂ => ⟨fun i => (M₂.runStep s₂ i).2, fun i => .inr (M₂.runStep s₂ i).1⟩ }
    Repair.Bisim (In → Option Out) (fun _ => In) sumCoalg
      (fun x y => match x, y with | .inl s₁, .inr s₂ => s₂ = E.equiv.toFun s₁ | _, _ => False) := by
  intro sumCoalg x y hRel
  cases x with
  | inr _ => exact False.elim hRel
  | inl s₁ =>
    cases y with
    | inl _ => exact False.elim hRel
    | inr s₂ =>
      subst hRel
      have hShape : sumCoalg.shape (.inl s₁) = sumCoalg.shape (.inr (E.equiv.toFun s₁)) := by
        funext inp
        dsimp only [sumCoalg, Repair.PCoalg.shape, Spec.Machine.runStep]
        rw [E.step_comm s₁ inp]
        cases M₁.step s₁ inp <;> rfl
      refine ⟨hShape, fun inp => ?_⟩
      dsimp only [sumCoalg, Repair.PCoalg.pos]
      rw [const_pos_cast (fun i => (M₂.runStep (E.equiv.toFun s₁) i).1) hShape inp]
      dsimp only [Spec.Machine.runStep]
      rw [E.step_comm s₁ inp, E.errStep_comm s₁ inp]
      cases M₁.step s₁ inp <;> rfl

end MachineStateEquiv

end Qsag

namespace Qsag.Tactic.AssuranceKit
open Lean Meta Elab Tactic Command

/-! ## 1. Constructive `compose_forward_sim` / `compose_refines` & `mir_sim_step` (`0 Classical.choice`) -/

/-- Extract the last two arguments `(src, dst)` of an application without `!` (`0 Inhabited`). -/
private meta def lastTwoArgs? (args : Array Expr) : Option (Expr × Expr) :=
  if args.size >= 2 then
    match args[args.size - 2]?, args[args.size - 1]? with
    | some src, some dst => some (src, dst)
    | _, _ => none
  else
    none

/-- Coerce a `ForwardSim` or `LockstepSim` expression into `(srcMachine, dstMachine, forwardSimExpr)`. -/
private meta def asForwardSimLink? (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let ty := stripMData (← instantiateMVars (← inferType e))
  let fn := stripMData ty.getAppFn
  let args := ty.getAppArgs
  if fn.isConstOf ``Qsag.ForwardSim then
    if let some (src, dst) := lastTwoArgs? args then
      return some (src, dst, e)
  if fn.isConstOf ``Qsag.LockstepSim then
    if let some (src, dst) := lastTwoArgs? args then
      let fsExpr ← mkAppM ``Qsag.LockstepSim.toForwardSim #[e]
      return some (src, dst, fsExpr)
  return none

/-- Coerce `Spec.Refines`, `Spec.LockstepSim`, or `MachineStateEquiv` into `(srcMachine, dstMachine, refinesExpr)`. -/
private meta def asSpecRefinesLinks (e : Expr) : MetaM (List (Expr × Expr × Expr)) := do
  let ty := stripMData (← instantiateMVars (← inferType e))
  let fn := stripMData ty.getAppFn
  let args := ty.getAppArgs
  if fn.isConstOf ``Qsag.Spec.Refines then
    if let some (src, dst) := lastTwoArgs? args then
      return [(src, dst, e)]
  if fn.isConstOf ``Qsag.Spec.LockstepSim then
    if let some (src, dst) := lastTwoArgs? args then
      let refExpr ← mkAppM ``Qsag.Spec.LockstepSim.toRefines #[e]
      return [(src, dst, refExpr)]
  if fn.isConstOf ``Qsag.MachineStateEquiv then
    if let some (src, dst) := lastTwoArgs? args then
      let fwd ← mkAppM ``Qsag.MachineStateEquiv.toRefines #[e]
      let bwd ← mkAppM ``Qsag.MachineStateEquiv.toRefinesSymm #[e]
      return [(src, dst, fwd), (dst, src, bwd)]
  return []

/-- Fuel-bounded DFS search over simulation links. -/
private meta partial def searchSimPath (reflConst transConst : Name) :
    Nat → Array Nat → List (Nat × Expr × Expr × Expr) → Expr → Expr → MetaM (Option Expr)
  | 0, _, _, curM, endM => do
    if ← withoutModifyingState (isDefEq curM endM) then
      let _ ← isDefEq curM endM
      return some (← mkAppM reflConst #[curM])
    return none
  | fuel' + 1, used, links, curM, endM => do
    if ← withoutModifyingState (isDefEq curM endM) then
      let _ ← isDefEq curM endM
      return some (← mkAppM reflConst #[curM])
    for (lid, srcM, dstM, linkExpr) in links do
      if !used.contains lid then
        if ← withoutModifyingState (isDefEq curM srcM) then
          if ← withoutModifyingState (isDefEq dstM endM) then
            let _ ← isDefEq curM srcM
            let _ ← isDefEq dstM endM
            return some linkExpr
          let tail? ← withoutModifyingState do
            let _ ← isDefEq curM srcM
            searchSimPath reflConst transConst fuel' (used.push lid) links dstM endM
          if tail?.isSome then
            let _ ← isDefEq curM srcM
            if let some tailExpr ← searchSimPath reflConst transConst fuel' (used.push lid) links dstM endM then
              return some (← mkAppM transConst #[linkExpr, tailExpr])
    return none

syntax "compose_forward_sim" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| compose_forward_sim [$[$ts:term],*]) => do
    let goal ← getMainGoal
    goal.withContext do
      let tgt := stripMData (← instantiateMVars (← goal.getType))
      let fn := stripMData tgt.getAppFn
      let isParty := fn.isConstOf ``Qsag.ForwardSim
      let isSpec := fn.isConstOf ``Qsag.Spec.Refines
      unless isParty || isSpec do
        throwError "compose_forward_sim: goal `{tgt}` is neither `Qsag.ForwardSim C A` nor `Qsag.Spec.Refines C A`"
      let some (startM, _) := lastTwoArgs? tgt.getAppArgs
        | throwError "compose_forward_sim: malformed simulation target `{tgt}`"
      let reflConst := if isParty then ``Qsag.ForwardSim.refl else ``Qsag.Spec.Refines.refl
      let transConst := if isParty then ``Qsag.ForwardSim.trans else ``Qsag.Spec.Refines.trans
      if ts.isEmpty then
        let reflExpr ← mkAppM reflConst #[startM]
        unless ← isDefEq (← goal.getType) (← inferType reflExpr) do
          throwError "compose_forward_sim []: machines are not definitionally equal"
        goal.assign reflExpr
        replaceMainGoal []
      else
        let mut chainExpr? : Option Expr := none
        for t in ts do
          let raw ← Tactic.elabTerm t none
          let linkOpt ←
            if isParty then asForwardSimLink? raw
            else pure (← asSpecRefinesLinks raw).head?
          let some (_, _, fsLink) := linkOpt
            | throwErrorAt t "compose_forward_sim: `{t}` is not a compatible simulation link"
          match chainExpr? with
          | none => chainExpr? := some fsLink
          | some prev => chainExpr? := some (← mkAppM transConst #[prev, fsLink])
        let some finalChain := chainExpr?
          | throwError "compose_forward_sim: empty link chain"
        unless ← isDefEq (← goal.getType) (← inferType finalChain) do
          throwError "compose_forward_sim: composed spine has type `{← inferType finalChain}`, expected `{← goal.getType}`"
        goal.assign finalChain
        replaceMainGoal []
  | `(tactic| compose_forward_sim) => do
    let goal ← getMainGoal
    goal.withContext do
      let tgt := stripMData (← instantiateMVars (← goal.getType))
      let fn := stripMData tgt.getAppFn
      let isParty := fn.isConstOf ``Qsag.ForwardSim
      let isSpec := fn.isConstOf ``Qsag.Spec.Refines
      unless isParty || isSpec do
        throwError "compose_forward_sim: goal `{tgt}` is neither `Qsag.ForwardSim C A` nor `Qsag.Spec.Refines C A`"
      let some (startM, endM) := lastTwoArgs? tgt.getAppArgs
        | throwError "compose_forward_sim: malformed simulation target `{tgt}`"
      let reflConst := if isParty then ``Qsag.ForwardSim.refl else ``Qsag.Spec.Refines.refl
      let transConst := if isParty then ``Qsag.ForwardSim.trans else ``Qsag.Spec.Refines.trans
      let mut links : List (Nat × Expr × Expr × Expr) := []
      let mut nextId : Nat := 0
      for ldecl in ← getLCtx do
        if ldecl.isImplementationDetail then continue
        if isParty then
          if let some (srcM, dstM, fsExpr) ← asForwardSimLink? ldecl.toExpr then
            links := links ++ [(nextId, srcM, dstM, fsExpr)]
            nextId := nextId + 1
        else
          for (srcM, dstM, refExpr) in ← asSpecRefinesLinks ldecl.toExpr do
            links := links ++ [(nextId, srcM, dstM, refExpr)]
            nextId := nextId + 1
      let some proof ← searchSimPath reflConst transConst (links.length + 1) #[] links startM endM
        | throwError "compose_forward_sim: could not find a simulation path from `{startM}` to `{endM}` in local context"
      unless ← isDefEq (← goal.getType) (← inferType proof) do
        throwError "compose_forward_sim: synthesized proof type mismatch"
      goal.assign proof
      replaceMainGoal []

/-- Alias for `compose_forward_sim` on `Spec.Refines` (`C ⊑ A`) goals. -/
macro "compose_refines" : tactic => `(tactic| compose_forward_sim)
macro "compose_refines" "[" ts:term,* "]" : tactic => `(tactic| compose_forward_sim [$ts,*])

/-- Structurally fuel-bounded symbolic splitter over `Option` and `Except` (`0 partial`). -/
private meta def mirStep : Nat → MVarId → TacticM (List MVarId)
  | 0, goal => return [goal]
  | fuel + 1, goal => do
    let rem ← evalTacticAt (← `(tactic| first
      | compose_forward_sim
      | (solve | simp_all)
      | skip)) goal
    if rem.isEmpty then return []
    goal.withContext do
      let mut found? : Option FVarId := none
      for decl in (← getLCtx).decls.toList.reduceOption do
        if found?.isNone && !decl.isImplementationDetail then
          let ty ← whnf decl.type
          if ty.getAppFn.isConstOf ``Option || ty.getAppFn.isConstOf ``Except then
            found? := some decl.fvarId
      if let some fid := found? then
        let cases ← goal.cases fid
        let mut out := []
        for c in cases do
          out := out ++ (← mirStep fuel c.mvarId)
        return out
      return ← evalTacticAt (← `(tactic| simp_all [Bind.bind, Option.bind, Except.bind])) goal

elab "mir_sim_step" : tactic => do
  replaceMainGoal (← mirStep 32 (← getMainGoal))

end Qsag.Tactic.AssuranceKit

/-! ## 2. Composable `Spec ↔ Exec` Data-Refinement Combinators (`DataRefinement`, `Rel1`, `Rel2`) -/

namespace Qsag

set_option autoImplicit false

/-- Constructive pointwise list relation (`0 Mathlib`, `0 Classical.choice`). -/
inductive ListRel {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : ListRel R [] []
  | cons {a : α} {b : β} {xs : List α} {ys : List β} :
      R a b → ListRel R xs ys → ListRel R (a :: xs) (b :: ys)

/-- Relational data refinement from abstract specification carrier `α` to executable carrier `β`. -/
structure DataRefinement (α β : Type) where
  Rel : α → β → Prop

/-- Functional representation refinement (`abs : β → α` under concrete well-formedness `Inv`). -/
structure FuncRefinement (α β : Type) where
  abs : β → α
  Inv : β → Prop := fun _ => True

/-- Every `FuncRefinement` canonically induces a `DataRefinement` (`a = F.abs x ∧ F.Inv x`). -/
@[expose] def FuncRefinement.toDataRefinement {α β : Type}
    (F : FuncRefinement α β) : DataRefinement α β where
  Rel a x := a = F.abs x ∧ F.Inv x

namespace DataRefinement

/-- Identity refinement (`Eq`). -/
def refl (α : Type) : DataRefinement α α where
  Rel := Eq

/-- Sequential relational composition across an intermediate carrier `β`. -/
def comp {α β γ : Type} (R₁ : DataRefinement α β) (R₂ : DataRefinement β γ) :
    DataRefinement α γ where
  Rel a c := ∃ b : β, R₁.Rel a b ∧ R₂.Rel b c

/-- Product refinement (`prod_rel`). -/
def prod {α₁ β₁ α₂ β₂ : Type}
    (R₁ : DataRefinement α₁ β₁) (R₂ : DataRefinement α₂ β₂) :
    DataRefinement (α₁ × α₂) (β₁ × β₂) where
  Rel p q := R₁.Rel p.1 q.1 ∧ R₂.Rel p.2 q.2

/-- `Option` relator (`option_rel`). -/
@[expose] def option {α β : Type} (R : DataRefinement α β) :
    DataRefinement (Option α) (Option β) where
  Rel
    | none, none => True
    | some a, some b => R.Rel a b
    | _, _ => False

/-- `Except` relator (`except_rel`). -/
def except {ε₁ ε₂ α β : Type}
    (Re : DataRefinement ε₁ ε₂) (Ra : DataRefinement α β) :
    DataRefinement (Except ε₁ α) (Except ε₂ β) where
  Rel
    | .error e₁, .error e₂ => Re.Rel e₁ e₂
    | .ok a, .ok b => Ra.Rel a b
    | _, _ => False

/-- Pointwise `List` relator (`list_rel` via `ListRel`). -/
@[expose] def list {α β : Type} (R : DataRefinement α β) :
    DataRefinement (List α) (List β) where
  Rel xs ys := ListRel R.Rel xs ys

/-- Length-indexed vector relator (`vec_rel`). -/
def vec {α β : Type} (n : Nat) (R : DataRefinement α β) :
    DataRefinement { xs : List α // xs.length = n } { ys : List β // ys.length = n } where
  Rel u v := ListRel R.Rel u.val v.val

/-- `ByteArray` refines `List UInt8` (`ba.toList`). -/
def byteArray : DataRefinement (List UInt8) ByteArray where
  Rel xs ba := xs = ba.toList

/-- `UInt64` refines bounded `Nat` (`w.toNat`). -/
def uint64Nat : DataRefinement Nat UInt64 where
  Rel n w := n = w.toNat

/-- `UInt32` refines bounded `Nat` (`w.toNat`). -/
def uint32Nat : DataRefinement Nat UInt32 where
  Rel n w := n = w.toNat

/-- `UInt64` refines `BitVec 64` (`w.toBitVec`). -/
def bitVec64UInt64 : DataRefinement (BitVec 64) UInt64 where
  Rel bv w := bv = w.toBitVec

/-- 32-byte slice `{ bs : List UInt8 // bs.length = 32 }` refines `Digest256` (`BitVec 256`) big-endian. -/
def digest256Bytes32 : DataRefinement Digest256 { bs : List UInt8 // bs.length = 32 } where
  Rel d bs := d = BitVec.ofNat 256 (ofBE bs.val)

theorem digest256Bytes32_injective {d : Digest256}
    {b₁ b₂ : { bs : List UInt8 // bs.length = 32 }}
    (h₁ : digest256Bytes32.Rel d b₁) (h₂ : digest256Bytes32.Rel d b₂) : b₁ = b₂ := by
  have hEqBv : BitVec.ofNat 256 (ofBE b₁.val) = BitVec.ofNat 256 (ofBE b₂.val) := h₁.symm.trans h₂
  have hLt₁ : ofBE b₁.val < 2 ^ 256 := by
    have h := ofBE_lt b₁.val
    rw [b₁.property] at h
    exact h
  have hLt₂ : ofBE b₂.val < 2 ^ 256 := by
    have h := ofBE_lt b₂.val
    rw [b₂.property] at h
    exact h
  have hNatEq : ofBE b₁.val = ofBE b₂.val := by
    have hToNat := congrArg BitVec.toNat hEqBv
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hLt₁, Nat.mod_eq_of_lt hLt₂] at hToNat
    exact hToNat
  apply Subtype.ext
  have hBe₁ := be_ofBE b₁.val
  have hBe₂ := be_ofBE b₂.val
  rw [b₁.property] at hBe₁
  rw [b₂.property, ← hNatEq] at hBe₂
  exact hBe₁.symm.trans hBe₂

end DataRefinement

/-- Unary operator relational refinement (`R₁.Rel a x → R₂.Rel (f a) (g x)`). -/
@[expose] def Rel1 {α₁ β₁ α₂ β₂ : Type}
    (R₁ : DataRefinement α₁ β₁) (R₂ : DataRefinement α₂ β₂)
    (f : α₁ → α₂) (g : β₁ → β₂) : Prop :=
  ∀ {a : α₁} {x : β₁}, R₁.Rel a x → R₂.Rel (f a) (g x)

/-- Binary operator relational refinement (`R₁.Rel a x → R₂.Rel b y → R₃.Rel (f a b) (g x y)`). -/
@[expose] def Rel2 {α₁ β₁ α₂ β₂ α₃ β₃ : Type}
    (R₁ : DataRefinement α₁ β₁) (R₂ : DataRefinement α₂ β₂) (R₃ : DataRefinement α₃ β₃)
    (f : α₁ → α₂ → α₃) (g : β₁ → β₂ → β₃) : Prop :=
  ∀ {a : α₁} {x : β₁} {b : α₂} {y : β₂},
    R₁.Rel a x → R₂.Rel b y → R₃.Rel (f a b) (g x y)

theorem Rel1.comp {α₁ β₁ α₂ β₂ α₃ β₃ : Type}
    {R₁ : DataRefinement α₁ β₁} {R₂ : DataRefinement α₂ β₂} {R₃ : DataRefinement α₃ β₃}
    {f₁ : α₁ → α₂} {g₁ : β₁ → β₂} {f₂ : α₂ → α₃} {g₂ : β₂ → β₃}
    (h₁ : Rel1 R₁ R₂ f₁ g₁) (h₂ : Rel1 R₂ R₃ f₂ g₂) :
    Rel1 R₁ R₃ (f₂ ∘ f₁) (g₂ ∘ g₁) :=
  fun hR => h₂ (h₁ hR)

theorem Rel1.map_option {α₁ β₁ α₂ β₂ : Type}
    {R₁ : DataRefinement α₁ β₁} {R₂ : DataRefinement α₂ β₂}
    {f : α₁ → α₂} {g : β₁ → β₂} (h : Rel1 R₁ R₂ f g) :
    Rel1 R₁.option R₂.option (Option.map f) (Option.map g) := by
  intro oa ox hR
  cases oa <;> cases ox
  · exact trivial
  · exact False.elim hR
  · exact False.elim hR
  · exact h hR

theorem Rel1.map_list {α₁ β₁ α₂ β₂ : Type}
    {R₁ : DataRefinement α₁ β₁} {R₂ : DataRefinement α₂ β₂}
    {f : α₁ → α₂} {g : β₁ → β₂} (h : Rel1 R₁ R₂ f g) :
    Rel1 R₁.list R₂.list (List.map f) (List.map g) := by
  intro xs ys hForall
  induction hForall with
  | nil => exact .nil
  | cons hHead _ ih => exact .cons (h hHead) ih

/-! ## 3. Prefix-Free Length-Framed Codecs (`LawfulFramedCodec`) & `by frame_prefix_inj` -/

/-- **Composable Prefix-Free Encoder (`LawfulFramedCodec`)**:
    An encoder `encode : α → List UInt8` whose image is prefix-free, so `encode x ++ r₁ = encode y ++ r₂`
    uniquely determines both `x = y` and `r₁ = r₂` for **arbitrary** trailing byte suffixes `r₁, r₂`. -/
structure LawfulFramedCodec (α : Type) where
  encode : α → List UInt8
  prefix_inj : ∀ {x y : α} {r₁ r₂ : List UInt8},
    encode x ++ r₁ = encode y ++ r₂ → x = y ∧ r₁ = r₂

namespace LawfulFramedCodec

/-- Standalone injectivity of any `LawfulFramedCodec`. -/
theorem encode_injective {α : Type} (c : LawfulFramedCodec α) {x y : α}
    (h : c.encode x = c.encode y) : x = y := by
  have hApp : c.encode x ++ [] = c.encode y ++ [] := by simpa using h
  exact (c.prefix_inj hApp).1

/-- Every `FixedCodec α w` is canonically a `LawfulFramedCodec α`. -/
@[expose] def ofFixedCodec {α : Type} {w : Nat} (c : FixedCodec α w) : LawfulFramedCodec α where
  encode := c.encode
  prefix_inj h := c.prefix_injective h

/-- **`FramedField` (`u32be_len || enc x`)**:
    Lifts any injective bounded encoder (`(enc x).length < 2 ^ 32`) into a prefix-free
    `LawfulFramedCodec α` via `frameBytes`. -/
@[expose] def framedField {α : Type} (enc : α → List UInt8)
    (hBound : ∀ x : α, (enc x).length < 2 ^ 32)
    (hInj : ∀ {x y : α}, enc x = enc y → x = y) : LawfulFramedCodec α where
  encode x := frameBytes (enc x)
  prefix_inj {x y r₁ r₂} h := by
    obtain ⟨hEnc, hRest⟩ := (FramedBytesCodec.prefix_free_injective (hBound x) (hBound y)).mp h
    exact ⟨hInj hEnc, hRest⟩

/-- Raw bounded byte-list field `{ bs : List UInt8 // bs.length < 2 ^ 32 }` framed by `frameBytes`. -/
def boundedBytes : LawfulFramedCodec { bs : List UInt8 // bs.length < 2 ^ 32 } :=
  framedField Subtype.val (fun x => x.property) (fun h => Subtype.ext h)

/-- **Product Combinator (`LawfulFramedCodec.pair`)**:
    Concatenating two prefix-free codecs `c₁.encode p.1 ++ c₂.encode p.2` is prefix-free! -/
@[expose] def pair {α β : Type} (c₁ : LawfulFramedCodec α) (c₂ : LawfulFramedCodec β) :
    LawfulFramedCodec (α × β) where
  encode p := c₁.encode p.1 ++ c₂.encode p.2
  prefix_inj {p₁ p₂ r₁ r₂} h := by
    rcases p₁ with ⟨a₁, b₁⟩
    rcases p₂ with ⟨a₂, b₂⟩
    dsimp only at h
    rw [List.append_assoc, List.append_assoc] at h
    obtain ⟨rfl, hTail⟩ := c₁.prefix_inj h
    obtain ⟨rfl, hRest⟩ := c₂.prefix_inj hTail
    exact ⟨rfl, hRest⟩

theorem pair_encode_eq {α β : Type} (c₁ : LawfulFramedCodec α) (c₂ : LawfulFramedCodec β)
    (a : α) (b : β) : (c₁.pair c₂).encode (a, b) = c₁.encode a ++ c₂.encode b := rfl

theorem framePair_inj {α β : Type} (c₁ : LawfulFramedCodec α) (c₂ : LawfulFramedCodec β)
    {a₁ a₂ : α} {b₁ b₂ : β} {r₁ r₂ : List UInt8}
    (h : c₁.encode a₁ ++ (c₂.encode b₁ ++ r₁) = c₁.encode a₂ ++ (c₂.encode b₂ ++ r₂)) :
    a₁ = a₂ ∧ b₁ = b₂ ∧ r₁ = r₂ := by
  obtain ⟨hA, hTail⟩ := c₁.prefix_inj h
  obtain ⟨hB, hR⟩ := c₂.prefix_inj hTail
  exact ⟨hA, hB, hR⟩

/-- 1-byte domain-tag prefix on a `LawfulFramedCodec`. -/
@[expose] def tagged (tag : UInt8) {α : Type} (c : LawfulFramedCodec α) : LawfulFramedCodec α where
  encode x := tag :: c.encode x
  prefix_inj h := by
    obtain ⟨_, hTail⟩ := List.cons.inj h
    exact c.prefix_inj hTail

theorem tagged_disjoint {t₁ t₂ : UInt8} (hNe : t₁ ≠ t₂)
    {α β : Type} (c₁ : LawfulFramedCodec α) (c₂ : LawfulFramedCodec β)
    (x : α) (y : β) (r₁ r₂ : List UInt8) :
    (c₁.tagged t₁).encode x ++ r₁ ≠ (c₂.tagged t₂).encode y ++ r₂ := by
  intro hEq
  obtain ⟨hTag, _⟩ := List.cons.inj hEq
  exact hNe hTag

private theorem flatMap_prefix_inj_of_len_eq {α : Type} (c : LawfulFramedCodec α) :
    ∀ {xs ys : List α} {r₁ r₂ : List UInt8},
      xs.length = ys.length →
      xs.flatMap c.encode ++ r₁ = ys.flatMap c.encode ++ r₂ →
      xs = ys ∧ r₁ = r₂
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | [], _ :: _, _, _, hLen, _ => nomatch hLen
  | _ :: _, [], _, _, hLen, _ => nomatch hLen
  | x :: xs, y :: ys, r₁, r₂, hLen, h => by
    simp only [List.flatMap_cons, List.append_assoc] at h
    obtain ⟨rfl, hTail⟩ := c.prefix_inj h
    have hLenTail : xs.length = ys.length := Nat.succ.inj hLen
    obtain ⟨rfl, hRest⟩ := flatMap_prefix_inj_of_len_eq c hLenTail hTail
    exact ⟨rfl, hRest⟩

/-- **Variable-Length Count-Prefixed List Combinator (`LawfulFramedCodec.boundedList` / `frameList_inj`)**:
    Encodes `{ xs : List α // xs.length < 2 ^ 32 }` as `u32be(xs.length) || flatMap c.encode xs`.
    Note that ONLY the element count needs `< 2 ^ 32` — total payload byte length is unrestricted! -/
@[expose] def boundedList {α : Type} (c : LawfulFramedCodec α) :
    LawfulFramedCodec { xs : List α // xs.length < 2 ^ 32 } where
  encode xs := encodeU32BeNat xs.val.length ++ xs.val.flatMap c.encode
  prefix_inj {xs ys r₁ r₂} h := by
    rw [List.append_assoc, List.append_assoc] at h
    have hLen4 : (encodeU32BeNat xs.val.length).length = (encodeU32BeNat ys.val.length).length := by
      rw [encodeU32BeNat_length, encodeU32BeNat_length]
    obtain ⟨hCntBytes, hTail⟩ := append_inj_of_len_eq hLen4 h
    have hDec := congrArg decodeU32BeNat hCntBytes
    rw [decodeU32BeNat_encodeU32BeNat xs.property,
        decodeU32BeNat_encodeU32BeNat ys.property] at hDec
    have hCntEq : xs.val.length = ys.val.length := Option.some.inj hDec
    obtain ⟨hListEq, hRest⟩ := flatMap_prefix_inj_of_len_eq c hCntEq hTail
    exact ⟨Subtype.ext hListEq, hRest⟩

theorem frameList_inj {α : Type} (c : LawfulFramedCodec α)
    {xs ys : List α} {r₁ r₂ : List UInt8}
    (hx : xs.length < 2 ^ 32) (hy : ys.length < 2 ^ 32)
    (h : (encodeU32BeNat xs.length ++ xs.flatMap c.encode) ++ r₁ =
         (encodeU32BeNat ys.length ++ ys.flatMap c.encode) ++ r₂) :
    xs = ys ∧ r₁ = r₂ := by
  obtain ⟨hSub, hRest⟩ := (c.boundedList).prefix_inj (x := ⟨xs, hx⟩) (y := ⟨ys, hy⟩) h
  exact ⟨congrArg Subtype.val hSub, hRest⟩

theorem frameList_flat_inj {α : Type} (c : LawfulFramedCodec α)
    {xs ys : List α} {r₁ r₂ : List UInt8}
    (hx : xs.length < 2 ^ 32) (hy : ys.length < 2 ^ 32)
    (h : encodeU32BeNat xs.length ++ (xs.flatMap c.encode ++ r₁) =
         encodeU32BeNat ys.length ++ (ys.flatMap c.encode ++ r₂)) :
    xs = ys ∧ r₁ = r₂ := by
  rw [← List.append_assoc, ← List.append_assoc] at h
  exact frameList_inj c hx hy h

theorem frameList_end_inj {α : Type} (c : LawfulFramedCodec α)
    {xs ys : List α}
    (hx : xs.length < 2 ^ 32) (hy : ys.length < 2 ^ 32)
    (h : encodeU32BeNat xs.length ++ xs.flatMap c.encode =
         encodeU32BeNat ys.length ++ ys.flatMap c.encode) :
    xs = ys := by
  have hApp : (encodeU32BeNat xs.length ++ xs.flatMap c.encode) ++ [] =
      (encodeU32BeNat ys.length ++ ys.flatMap c.encode) ++ [] := by simpa using h
  exact (frameList_inj c hx hy hApp).1

end LawfulFramedCodec

end Qsag

/-! ## 4. `by frame_prefix_inj` — 1-Line Multi-Field Byte-Framing Injectivity Tactic -/

namespace Qsag.Tactic.AssuranceKit
open Lean Meta Elab Tactic

/-- Try running `stx` without error recovery; returns `true` iff it succeeded cleanly. -/
private meta def tryRunTactic (stx : Syntax) : TacticM Bool := do
  let s ← saveState
  try
    withoutRecover (evalTactic stx)
    return true
  catch _ =>
    s.restore
    return false

/-- Structurally fuel-bounded prefix-peeling loop on a `List UInt8` equality hypothesis `hId`. -/
private meta def peelFramedHyp : Nat → Ident → TacticM Unit
  | 0, _ => pure ()
  | fuel + 1, hId => do
    let _ ← tryRunTactic (← `(tactic|
      simp only [List.append_assoc, Qsag.LawfulFramedCodec.pair_encode_eq,
        Qsag.domainFrame, Qsag.concatFramed] at $hId:ident))
    if ← tryRunTactic (← `(tactic| first
        | replace $hId:ident := Qsag.LawfulFramedCodec.encode_injective _ $hId:ident
        | replace $hId:ident := Qsag.FixedCodec.encode_injective _ $hId:ident
        | replace $hId:ident := Qsag.LawfulFramedCodec.frameList_end_inj _
            (by first | assumption | decide | omega)
            (by first | assumption | decide | omega) $hId:ident
        | replace $hId:ident := Qsag.FramedBytesCodec.frameBytes_injective
            (by first | assumption | decide | omega)
            (by first | assumption | decide | omega) $hId:ident)) then
      pure ()
    else if ← tryRunTactic (← `(tactic| first
        | (replace $hId:ident := Qsag.LawfulFramedCodec.prefix_inj _ $hId:ident;
           rcases $hId:ident with ⟨_, $hId:ident⟩)
        | (replace $hId:ident := Qsag.FixedCodec.prefix_injective _ $hId:ident;
           rcases $hId:ident with ⟨_, $hId:ident⟩)
        | (replace $hId:ident := Qsag.LawfulFramedCodec.frameList_flat_inj _
             (by first | assumption | decide | omega)
             (by first | assumption | decide | omega) $hId:ident;
           rcases $hId:ident with ⟨_, $hId:ident⟩)
        | (replace $hId:ident := (Qsag.FramedBytesCodec.prefix_free_injective
             (by first | assumption | decide | omega)
             (by first | assumption | decide | omega)).mp $hId:ident;
           rcases $hId:ident with ⟨_, $hId:ident⟩)
        | (simp only [List.cons_append, List.nil_append] at $hId:ident;
           replace $hId:ident := List.cons.inj $hId:ident;
           rcases $hId:ident with ⟨_, $hId:ident⟩))) then
      peelFramedHyp fuel hId
    else
      pure ()

private meta def finishFramedGoal : TacticM Unit := do
  let _ ← tryRunTactic (← `(tactic| subst_vars))
  let _ ← tryRunTactic (← `(tactic| simp only [and_self, true_and, and_true]))
  let _ ← tryRunTactic (← `(tactic| rfl))
  let _ ← tryRunTactic (← `(tactic| assumption))

elab "frame_prefix_inj" h?:(ppSpace colGt ident)? : tactic => do
  match h? with
  | some h =>
    peelFramedHyp 32 h
    finishFramedGoal
  | none => do
    let listU8 := mkApp (mkConst ``List [Level.zero]) (mkConst ``UInt8)
    let autoId := mkIdent `hFrameAuto
    let goal0 ← getMainGoal
    let introArrow ← goal0.withContext do
      let tgt ← instantiateMVars (← goal0.getType)
      pure tgt.isForall
    if introArrow then
      let _ ← evalTactic (← `(tactic| intro $autoId:ident))
      peelFramedHyp 32 autoId
      finishFramedGoal
    else
      let goal ← getMainGoal
      let found? ← goal.withContext do
        let mut hit : Option Name := none
        for decl in ← getLCtx do
          if decl.isImplementationDetail || decl.userName.hasMacroScopes then continue
          let ty ← instantiateMVars decl.type
          if ty.isAppOfArity ``Eq 3 then
            if let some et := ty.getAppArgs[0]? then
              if (← withTransparency .default <| isDefEq et listU8) then
                hit := some decl.userName
        pure hit
      if let some hName := found? then
        peelFramedHyp 32 (mkIdent hName)
        finishFramedGoal
      else
        throwError "frame_prefix_inj: no `List UInt8` equality hypothesis found in local context"

end Qsag.Tactic.AssuranceKit

/-! ## 5. Regression & Coalgebraic Repair Checks (`0 Classical.choice`) -/

namespace Qsag

set_option autoImplicit false

theorem mir_option_test (x : Option Nat) (f g : Nat → Option Nat)
    (h : ∀ n, f n = g n) : (x >>= f) = (x >>= g) := by
  mir_sim_step

theorem mir_except_test (x : Except String Nat) (f g : Nat → Except String Nat)
    (h : ∀ n, f n = g n) : (x >>= f) = (x >>= g) := by
  mir_sim_step

def mir_compose_test {S₁ S₂ S₃ In Out : Type}
    {C : PartyMachine S₁ In Out} {A : PartyMachine S₂ In Out} {B : PartyMachine S₃ In Out}
    (ca : ForwardSim C A) (ab : ForwardSim A B) : ForwardSim C B := by
  mir_sim_step

def spec_compose_refines_test {S₁ S₂ S₃ In Out : Type}
    {M₁ : Spec.Machine S₁ In Out} {M₂ : Spec.Machine S₂ In Out} {M₃ : Spec.Machine S₃ In Out}
    (r₁₂ : Spec.Refines M₁ M₂) (r₂₃ : Spec.Refines M₂ M₃) : Spec.Refines M₁ M₃ := by
  compose_refines

def spec_compose_machine_equiv_test {S₁ S₂ S₃ In Out : Type}
    {M₁ : Spec.Machine S₁ In Out} {M₂ : Spec.Machine S₂ In Out} {M₃ : Spec.Machine S₃ In Out}
    (e₁₂ : MachineStateEquiv M₁ M₂) (r₂₃ : Spec.Refines M₂ M₃) : Spec.Refines M₁ M₃ := by
  compose_refines

/-- 4-field mixed fixed-width + variable-length framed transcript message:
    injectivity collapses to a single `by frame_prefix_inj hEq` line! -/
theorem frame_prefix_inj_four_field_exemplar
    (tag₁ tag₂ : List UInt8) (ep₁ ep₂ : UInt64) (role₁ role₂ : UInt8) (msg₁ msg₂ : List UInt8)
    (ht₁ : tag₁.length < 2 ^ 32) (ht₂ : tag₂.length < 2 ^ 32)
    (hm₁ : msg₁.length < 2 ^ 32) (hm₂ : msg₂.length < 2 ^ 32)
    (hEq : frameBytes tag₁ ++ FixedCodec.u64le.encode ep₁ ++
             FixedCodec.u8.encode role₁ ++ frameBytes msg₁ =
           frameBytes tag₂ ++ FixedCodec.u64le.encode ep₂ ++
             FixedCodec.u8.encode role₂ ++ frameBytes msg₂) :
    tag₁ = tag₂ ∧ ep₁ = ep₂ ∧ role₁ = role₂ ∧ msg₁ = msg₂ := by
  frame_prefix_inj hEq

/-- Automatic context discovery (`by frame_prefix_inj` with zero arguments) on a 5-field
    domain-separated framed message! -/
theorem frame_prefix_inj_auto_ctx_exemplar
    (d₁ d₂ : List UInt8) (w₁ w₂ : UInt32) (ep₁ ep₂ : UInt64) (p₁ p₂ : List UInt8)
    (hd₁ : d₁.length < 2 ^ 32) (hd₂ : d₂.length < 2 ^ 32)
    (hp₁ : p₁.length < 2 ^ 32) (hp₂ : p₂.length < 2 ^ 32) :
    frameBytes d₁ ++ FixedCodec.u32be.encode w₁ ++ FixedCodec.u64be.encode ep₁ ++ frameBytes p₁ =
      frameBytes d₂ ++ FixedCodec.u32be.encode w₂ ++ FixedCodec.u64be.encode ep₂ ++ frameBytes p₂ →
    d₁ = d₂ ∧ w₁ = w₂ ∧ ep₁ = ep₂ ∧ p₁ = p₂ := by
  frame_prefix_inj

/-- Tagged + count-prefixed variable-length list + fixed-width epoch + trailing payload peeled in 1 line! -/
theorem frame_prefix_inj_tagged_list_exemplar
    (c : LawfulFramedCodec UInt64)
    (xs₁ xs₂ : List UInt64) (ep₁ ep₂ : UInt64) (tail₁ tail₂ : List UInt8)
    (hx₁ : xs₁.length < 2 ^ 32) (hx₂ : xs₂.length < 2 ^ 32)
    (ht₁ : tail₁.length < 2 ^ 32) (ht₂ : tail₂.length < 2 ^ 32) :
    (0x42 : UInt8) :: (encodeU32BeNat xs₁.length ++ xs₁.flatMap c.encode) ++
        FixedCodec.u64le.encode ep₁ ++ frameBytes tail₁ =
      (0x42 : UInt8) :: (encodeU32BeNat xs₂.length ++ xs₂.flatMap c.encode) ++
        FixedCodec.u64le.encode ep₂ ++ frameBytes tail₂ →
    xs₁ = xs₂ ∧ ep₁ = ep₂ ∧ tail₁ = tail₂ := by
  frame_prefix_inj

/-! ### Scar-Free Coalgebraic Machine State-Packing Repair Exemplar -/

/-- Unpacked `(epoch, spent)` reference state carrier. -/
structure UnpackedCounterSpec where
  epoch : UInt64
  spent : UInt64

/-- Packed `BitVec 128` (`spent_hi64 || epoch_lo64`) hardware register state carrier. -/
structure Packed128Counter where
  word : BitVec 128

def unpackedCounterMachine (cap : Nat) : Spec.Machine UnpackedCounterSpec UInt64 UInt64 where
  Init s := s.epoch = 0 ∧ s.spent = 0
  step s req :=
    if s.epoch.toNat + 1 < 2 ^ 64 ∧ s.spent.toNat + req.toNat ≤ cap ∧ cap < 2 ^ 64 then
      some (⟨UInt64.ofNat (s.epoch.toNat + 1), UInt64.ofNat (s.spent.toNat + req.toNat)⟩,
            UInt64.ofNat (s.epoch.toNat + 1))
    else none

def packedCounterEpoch (s : Packed128Counter) : UInt64 :=
  UInt64.ofNat (s.word.toNat % 2 ^ 64)

def packedCounterSpent (s : Packed128Counter) : UInt64 :=
  UInt64.ofNat (s.word.toNat / 2 ^ 64)

def mkPackedCounter (ep sp : UInt64) : Packed128Counter :=
  ⟨BitVec.ofNat 128 (sp.toNat * 2 ^ 64 + ep.toNat)⟩

def packedCounterMachine (cap : Nat) : Spec.Machine Packed128Counter UInt64 UInt64 where
  Init s := s = mkPackedCounter 0 0
  step s req :=
    let ep := packedCounterEpoch s
    let sp := packedCounterSpent s
    if ep.toNat + 1 < 2 ^ 64 ∧ sp.toNat + req.toNat ≤ cap ∧ cap < 2 ^ 64 then
      some (mkPackedCounter (UInt64.ofNat (ep.toNat + 1)) (UInt64.ofNat (sp.toNat + req.toNat)),
            UInt64.ofNat (ep.toNat + 1))
    else none

private theorem packed_epoch_mk (ep sp : UInt64) :
    packedCounterEpoch (mkPackedCounter ep sp) = ep := by
  have hep : ep.toNat < 2 ^ 64 := ep.toNat_lt
  have hsp : sp.toNat < 2 ^ 64 := sp.toNat_lt
  have h128 : sp.toNat * 2 ^ 64 + ep.toNat < 2 ^ 128 := by omega
  unfold packedCounterEpoch mkPackedCounter
  dsimp only
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h128]
  have hMod : (sp.toNat * 2 ^ 64 + ep.toNat) % 2 ^ 64 = ep.toNat := by omega
  rw [hMod]
  exact UInt64.ofNat_toNat

private theorem packed_spent_mk (ep sp : UInt64) :
    packedCounterSpent (mkPackedCounter ep sp) = sp := by
  have hep : ep.toNat < 2 ^ 64 := ep.toNat_lt
  have hsp : sp.toNat < 2 ^ 64 := sp.toNat_lt
  have h128 : sp.toNat * 2 ^ 64 + ep.toNat < 2 ^ 128 := by omega
  unfold packedCounterSpent mkPackedCounter
  dsimp only
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h128]
  have hDiv : (sp.toNat * 2 ^ 64 + ep.toNat) / 2 ^ 64 = sp.toNat := by omega
  rw [hDiv]
  exact UInt64.ofNat_toNat

private theorem mk_packed_eta (s : Packed128Counter) :
    mkPackedCounter (packedCounterEpoch s) (packedCounterSpent s) = s := by
  cases s with
  | mk w =>
    have hw : w.toNat < 2 ^ 128 := w.isLt
    apply congrArg Packed128Counter.mk
    apply BitVec.eq_of_toNat_eq
    unfold packedCounterEpoch packedCounterSpent
    dsimp only
    have hModLt : w.toNat % 2 ^ 64 < 2 ^ 64 := by omega
    have hDivLt : w.toNat / 2 ^ 64 < 2 ^ 64 := by omega
    rw [BitVec.toNat_ofNat, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
        Nat.mod_eq_of_lt hModLt, Nat.mod_eq_of_lt hDivLt]
    omega

def unpackedToPackedCounterEquiv (cap : Nat) :
    MachineStateEquiv (unpackedCounterMachine cap) (packedCounterMachine cap) where
  equiv :=
    { toFun := fun s => mkPackedCounter s.epoch s.spent
      invFun := fun p => ⟨packedCounterEpoch p, packedCounterSpent p⟩
      left_inv := fun ⟨ep, sp⟩ => by rw [packed_epoch_mk, packed_spent_mk]
      right_inv := mk_packed_eta }
  init_iff s := by
    rcases s with ⟨ep, sp⟩
    dsimp only [unpackedCounterMachine, packedCounterMachine]
    constructor
    · rintro ⟨rfl, rfl⟩; rfl
    · intro h
      have h1 := congrArg packedCounterEpoch h
      have h2 := congrArg packedCounterSpent h
      rw [packed_epoch_mk, packed_epoch_mk] at h1
      rw [packed_spent_mk, packed_spent_mk] at h2
      exact ⟨h1, h2⟩
  step_comm s req := by
    dsimp only [unpackedCounterMachine, packedCounterMachine]
    rw [packed_epoch_mk, packed_spent_mk]
    by_cases hCond : s.epoch.toNat + 1 < 2 ^ 64 ∧ s.spent.toNat + req.toNat ≤ cap ∧ cap < 2 ^ 64
    · simp only [hCond, and_self, ↓reduceIte]; rfl
    · simp only [hCond, ↓reduceIte]; rfl
  errStep_comm _ _ := rfl

-- `packedCounterMachine` is 100% scar-free with respect to `UnpackedCounterSpec`!
#assert_no_scar UnpackedCounterSpec in packedCounterMachine

#verify_constructive
  mir_option_test
  mir_except_test
  MachineStateEquiv.admitsTrace_iff
  MachineStateEquiv.machineStateEquiv_sum_bisim
  DataRefinement.digest256Bytes32_injective
  Rel1.comp
  Rel1.map_option
  Rel1.map_list
  LawfulFramedCodec.encode_injective
  LawfulFramedCodec.framePair_inj
  LawfulFramedCodec.tagged_disjoint
  LawfulFramedCodec.frameList_inj
  LawfulFramedCodec.frameList_flat_inj
  LawfulFramedCodec.frameList_end_inj
  frame_prefix_inj_four_field_exemplar
  frame_prefix_inj_auto_ctx_exemplar
  frame_prefix_inj_tagged_list_exemplar

end Qsag
end
