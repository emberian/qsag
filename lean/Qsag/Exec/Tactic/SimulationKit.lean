module
/-
# Qsag.Exec.Tactic.SimulationKit — `compose_forward_sim` and `mir_sim_step`

**`by compose_forward_sim` / `by compose_forward_sim [h₁, ...]`**: goal-directed `TacticM` spine
synthesizer chaining `ForwardSim.refl`, `ForwardSim.trans`, and `LockstepSim.toForwardSim` across
multi-layer protocol state machines (`Qsag.Exec.SimulationSpine`).
**`by mir_sim_step`**: symbolic case split of monadic `Option` / `Except` results, closing
simulation links with `compose_forward_sim`.
-/

public import Qsag.Tactic.AssuranceKit
public import Qsag.Math.Tactic.MaskBijection
public import Qsag.Exec.SimulationSpine
public meta import Lean

public section

namespace Qsag.Tactic.AssuranceKit
open Lean Meta Elab Tactic Command
/-! ### `by compose_forward_sim` — Compositional `ForwardSim` & `LockstepSim` Spine Synthesizer -/

/-- Coerce a `ForwardSim` or `LockstepSim` expression into `(srcMachine, dstMachine, forwardSimExpr)`. -/
private meta def asForwardSimLink? (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let ty := stripMData (← instantiateMVars (← inferType e))
  let fn := stripMData ty.getAppFn
  let args := ty.getAppArgs
  if fn.isConstOf ``Qsag.ForwardSim && args.size >= 2 then
    return some (args[args.size - 2]!, args[args.size - 1]!, e)
  if fn.isConstOf ``Qsag.LockstepSim && args.size >= 2 then
    let fsExpr ← mkAppM ``Qsag.LockstepSim.toForwardSim #[e]
    return some (args[args.size - 2]!, args[args.size - 1]!, fsExpr)
  return none

/-- Bounded DFS search over local `ForwardSim` / `LockstepSim` links to connect `curM` to `endM`. -/
private meta partial def searchForwardSimPath (fuel : Nat) (used : Array FVarId)
    (links : Array (FVarId × Expr × Expr × Expr)) (curM endM : Expr) : MetaM (Option Expr) := do
  if ← withoutModifyingState (isDefEq curM endM) then
    let _ ← isDefEq curM endM
    return some (← mkAppM ``Qsag.ForwardSim.refl #[curM])
  match fuel with
  | 0 => return none
  | fuel' + 1 =>
    for (fid, srcM, dstM, linkExpr) in links do
      if used.contains fid then continue
      if ← withoutModifyingState (isDefEq curM srcM) then
        if ← withoutModifyingState (isDefEq dstM endM) then
          let _ ← isDefEq curM srcM
          let _ ← isDefEq dstM endM
          return some linkExpr
        let tail? ← withoutModifyingState do
          let _ ← isDefEq curM srcM
          searchForwardSimPath fuel' (used.push fid) links dstM endM
        if tail?.isSome then
          let _ ← isDefEq curM srcM
          if let some tailExpr ← searchForwardSimPath fuel' (used.push fid) links dstM endM then
            return some (← mkAppM ``Qsag.ForwardSim.trans #[linkExpr, tailExpr])
    return none

syntax "compose_forward_sim" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| compose_forward_sim [$[$ts:term],*]) => do
    let goal ← getMainGoal
    goal.withContext do
      let tgt := stripMData (← instantiateMVars (← goal.getType))
      let args := tgt.getAppArgs
      unless (stripMData tgt.getAppFn).isConstOf ``Qsag.ForwardSim && args.size >= 2 do
        throwError "compose_forward_sim: goal `{tgt}` is not a `Qsag.ForwardSim C A`"
      let startM := args[args.size - 2]!
      if ts.isEmpty then
        let reflExpr ← mkAppM ``Qsag.ForwardSim.refl #[startM]
        unless ← isDefEq (← goal.getType) (← inferType reflExpr) do
          throwError "compose_forward_sim []: machines are not definitionally equal"
        goal.assign reflExpr
        replaceMainGoal []
      else
        let mut chainExpr? : Option Expr := none
        for t in ts do
          let raw ← Tactic.elabTerm t none
          let some (_, _, fsLink) ← asForwardSimLink? raw
            | throwErrorAt t "compose_forward_sim: `{t}` has type `{← inferType raw}`, expected `ForwardSim` or `LockstepSim`"
          match chainExpr? with
          | none => chainExpr? := some fsLink
          | some prev => chainExpr? := some (← mkAppM ``Qsag.ForwardSim.trans #[prev, fsLink])
        let some finalChain := chainExpr? | unreachable!
        unless ← isDefEq (← goal.getType) (← inferType finalChain) do
          throwError "compose_forward_sim: composed spine has type `{← inferType finalChain}`, expected `{← goal.getType}`"
        goal.assign finalChain
        replaceMainGoal []
  | `(tactic| compose_forward_sim) => do
    let goal ← getMainGoal
    goal.withContext do
      let tgt := stripMData (← instantiateMVars (← goal.getType))
      let args := tgt.getAppArgs
      unless (stripMData tgt.getAppFn).isConstOf ``Qsag.ForwardSim && args.size >= 2 do
        throwError "compose_forward_sim: goal `{tgt}` is not a `Qsag.ForwardSim C A`"
      let startM := args[args.size - 2]!
      let endM := args[args.size - 1]!
      let mut links : Array (FVarId × Expr × Expr × Expr) := #[]
      for ldecl in ← getLCtx do
        if ldecl.isImplementationDetail then continue
        if let some (srcM, dstM, fsExpr) ← asForwardSimLink? ldecl.toExpr then
          links := links.push (ldecl.fvarId, srcM, dstM, fsExpr)
      let some proof ← searchForwardSimPath (links.size + 1) #[] links startM endM
        | throwError "compose_forward_sim: could not find a `ForwardSim`/`LockstepSim` path from `{startM}` to `{endM}` in local context"
      unless ← isDefEq (← goal.getType) (← inferType proof) do
        throwError "compose_forward_sim: synthesized proof type mismatch"
      goal.assign proof
      replaceMainGoal []

/-- Symbolically split monadic results, retaining equations for each branch. -/
private meta partial def mirStep (goal : MVarId) : TacticM (List MVarId) := do
  let rem ← evalTacticAt (← `(tactic| first
    | compose_forward_sim
    | (solve | simp_all)
    | skip)) goal
  if rem.isEmpty then return []
  goal.withContext do
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty ← whnf decl.type
      if ty.getAppFn.isConstOf ``Option || ty.getAppFn.isConstOf ``Except then
        let cases ← goal.cases decl.fvarId
        let mut out := []
        for c in cases do out := out ++ (← mirStep c.mvarId)
        return out
    return ← evalTacticAt (← `(tactic| simp_all [Bind.bind, Option.bind, Except.bind])) goal

elab "mir_sim_step" : tactic => do
  replaceMainGoal (← mirStep (← getMainGoal))

end Qsag.Tactic.AssuranceKit

namespace Qsag

set_option autoImplicit false

theorem mir_option_test (x : Option Nat) (f g : Nat → Option Nat)
    (h : ∀ n, f n = g n) : (x >>= f) = (x >>= g) := by
  mir_sim_step

theorem mir_except_test (x : Except String Nat) (f g : Nat → Except String Nat)
    (h : ∀ n, f n = g n) : (x >>= f) = (x >>= g) := by
  mir_sim_step

def mir_compose_test {S₁ S₂ S₃ In Out : Type}
    {C : PartyMachine S₁ In Out} {A : PartyMachine S₂ In Out} {B : PartyMachine S₃ In Out} (ca : ForwardSim C A)
    (ab : ForwardSim A B) : ForwardSim C B := by
  mir_sim_step

#verify_constructive mir_option_test mir_except_test

end Qsag
end
