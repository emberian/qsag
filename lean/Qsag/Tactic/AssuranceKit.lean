module
/-
# Qsag.Tactic.AssuranceKit — `0-Classical` Proof Automation & Constructive Assurance Gates

Reusable Lean 4.35 tactic and command-elaboration infrastructure for QSAG (`LAW-M2`):
1. **`#verify_constructive <ident>+`**:
   Compile-time kernel axiom and `Prop`-type auditor enforcing `0 sorryAx`, `0` custom axioms,
   `0` compiler-trust axioms (`_native` / `ofReduceBool`), and **`0` transitive `Classical.choice`**
   (`axioms ⊆ {propext, Quot.sound}`).
2. **`#tooth_pair <secIdent> vs <toothIdent>`**:
   Compile-time structural pairing auditor verifying that a security theorem is paired with a
   structurally related counterexample/refusal theorem and that both satisfy
   `#verify_constructive` without vacuous `False` hypotheses.
   Shared primitive carriers do not establish a pair; a domain operation or predicate must overlap.
   This is a structural diagnostic, not a proof that the tooth is a mutation of the theorem.
   `#verify_inhabited` constructs one joint assignment for all theorem binders, including
   propositions and dependent values; witness parameters must themselves be constructible.
3. **`by bv_xor_cancel`**:
   Constructive (`0 Classical.choice`, `0 ofReduceBool`) XOR one-time-pad normalizer and
   unbounded reflected AC normalization over `BitVec w`; a Boolean fallback handles
   other bitwise identities over `UInt64`, `UInt8`, and `Bool`.
4. **`by compose_forward_sim` / `by compose_forward_sim [h₁, ...]`**:
   Goal-directed `TacticM` spine synthesizer chaining `ForwardSim.refl`, `ForwardSim.trans`, and
   `LockstepSim.toForwardSim` across multi-layer protocol state machines.
5. **`by mask_bijection_hop` / `by mask_bijection_hop <equiv>`**:
   Relational pad-bijection synthesizer discharging `qsum` uniform-mask invariance goals via
   `SimpleEquiv` combinators (`bvXorEquiv`, `u64XorEquiv`, `boolXorEquiv`, `ringAddEquiv`,
   `SimpleEquiv.prodCongr`) and `bv_xor_cancel` with `0 Classical.choice`.
-/

public import Qsag.Tactic.Prelude
public import Qsag.Exec.SimulationSpine
public import Qsag.Protocol.Aggregation.UcGames
public meta import Lean

public section

namespace Qsag

set_option autoImplicit false


theorem ring_add_sub_cancel_right {R : Type} [LawfulCommRing R] (a b : R) :
    CommRingOps.sub (CommRingOps.add a b) b = a := by
  rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc,
      LawfulCommRing.add_right_neg, LawfulCommRing.add_zero]

theorem ring_sub_add_cancel_right {R : Type} [LawfulCommRing R] (a b : R) :
    CommRingOps.add (CommRingOps.sub a b) b = a := by
  rw [LawfulCommRing.add_comm, LawfulCommRing.add_sub_cancel_left]

/-! ## 2. Constructive `SimpleEquiv` Pad-Bijection Combinators (`0 Classical.choice`) -/

@[expose] def SimpleEquiv.symm {α β : Type} (e : SimpleEquiv α β) : SimpleEquiv β α where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv

@[expose] def SimpleEquiv.trans {α β γ : Type}
    (e₁ : SimpleEquiv α β) (e₂ : SimpleEquiv β γ) : SimpleEquiv α γ where
  toFun a := e₂.toFun (e₁.toFun a)
  invFun c := e₁.invFun (e₂.invFun c)
  left_inv a := by rw [e₂.left_inv, e₁.left_inv]
  right_inv c := by rw [e₁.right_inv, e₂.right_inv]

@[expose] def SimpleEquiv.prodCongr {α₁ β₁ α₂ β₂ : Type}
    (e₁ : SimpleEquiv α₁ β₁) (e₂ : SimpleEquiv α₂ β₂) : SimpleEquiv (α₁ × α₂) (β₁ × β₂) where
  toFun p := (e₁.toFun p.1, e₂.toFun p.2)
  invFun q := (e₁.invFun q.1, e₂.invFun q.2)
  left_inv := fun ⟨a₁, a₂⟩ => Prod.ext (e₁.left_inv a₁) (e₂.left_inv a₂)
  right_inv := fun ⟨b₁, b₂⟩ => Prod.ext (e₁.right_inv b₁) (e₂.right_inv b₂)

/-- Constructive involutive one-time-pad bijection `x ↦ x ^^^ mask` on `BitVec w`. -/
@[expose] def bvXorEquiv {w : Nat} (mask : BitVec w) : SimpleEquiv (BitVec w) (BitVec w) where
  toFun x := x ^^^ mask
  invFun y := y ^^^ mask
  left_inv x := bv_xor_cancel_right x mask
  right_inv y := bv_xor_cancel_right y mask

/-- Constructive involutive one-time-pad bijection `x ↦ x ^^^ mask` on `UInt64`. -/
abbrev u64XorEquiv (mask : UInt64) : SimpleEquiv UInt64 UInt64 where
  toFun x := x ^^^ mask
  invFun y := y ^^^ mask
  left_inv x := u64_xor_cancel_right x mask
  right_inv y := u64_xor_cancel_right y mask

/-- Constructive involutive one-time-pad bijection `x ↦ x != mask` on `Bool`. -/
abbrev boolXorEquiv (mask : Bool) : SimpleEquiv Bool Bool where
  toFun x := x != mask
  invFun y := y != mask
  left_inv x := bool_bne_cancel_right x mask
  right_inv y := bool_bne_cancel_right y mask

/-- Constructive additive shift bijection `x ↦ x + delta` over any `LawfulCommRing R`. -/
@[expose] def ringAddEquiv {R : Type} [LawfulCommRing R] (delta : R) : SimpleEquiv R R where
  toFun x := CommRingOps.add x delta
  invFun y := CommRingOps.sub y delta
  left_inv x := ring_add_sub_cancel_right x delta
  right_inv y := ring_sub_add_cancel_right y delta

theorem SimpleEquiv.refl_toFun {α : Type} (x : α) :
    (SimpleEquiv.refl α).toFun x = x := rfl

theorem SimpleEquiv.symm_toFun {α β : Type} (e : SimpleEquiv α β) (y : β) :
    (SimpleEquiv.symm e).toFun y = e.invFun y := rfl

theorem SimpleEquiv.trans_toFun {α β γ : Type}
    (e₁ : SimpleEquiv α β) (e₂ : SimpleEquiv β γ) (x : α) :
    (SimpleEquiv.trans e₁ e₂).toFun x = e₂.toFun (e₁.toFun x) := rfl

theorem SimpleEquiv.prodCongr_toFun {α₁ β₁ α₂ β₂ : Type}
    (e₁ : SimpleEquiv α₁ β₁) (e₂ : SimpleEquiv α₂ β₂) (p : α₁ × α₂) :
    (SimpleEquiv.prodCongr e₁ e₂).toFun p = (e₁.toFun p.1, e₂.toFun p.2) := rfl

theorem bvXorEquiv_toFun {w : Nat} (mask x : BitVec w) :
    (bvXorEquiv mask).toFun x = x ^^^ mask := rfl

theorem u64XorEquiv_toFun (mask x : UInt64) :
    (u64XorEquiv mask).toFun x = x ^^^ mask := rfl

theorem boolXorEquiv_toFun (mask x : Bool) :
    (boolXorEquiv mask).toFun x = (x != mask) := rfl

theorem ringAddEquiv_toFun {R : Type} [LawfulCommRing R] (delta x : R) :
    (ringAddEquiv delta).toFun x = CommRingOps.add x delta := rfl

/-- Relational `qsum` pad-bijection hop reducing distributional equality over a sample space `Ω`
    enumerated by `enum` to pointwise equality after applying mask bijection `e`. -/
theorem qsum_bijection_hop_eq {Ω : Type} {C : Nat}
    (enum : SimpleEquiv (Fin C) Ω) (e : SimpleEquiv Ω Ω)
    (f g : Ω → Nat)
    (hPointwise : ∀ ω : Ω, f (e.toFun ω) = g ω) :
    qsum C (fun i => f (enum.toFun i)) = qsum C (fun i => g (enum.toFun i)) := by
  rw [← qsum_bijection_invariant enum e f]
  exact qsum_congr (fun i => hPointwise (enum.toFun i))

end Qsag
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

private meta partial def framingConclusion (ty : Expr) : MetaM Expr := do
  for decl in ← getLCtx do
    if ← isDefEq decl.type ty then return decl.toExpr
  if ty.getAppFn.isConstOf ``And then
    let args := ty.getAppArgs
    mkAppM ``And.intro #[← framingConclusion args[0]!, ← framingConclusion args[1]!]
  else throwError "frame_prefix_inj: cannot derive {ty} from framed equalities"

/-- Peel all framed equalities in the context, preserving every remainder. -/
elab "frame_prefix_inj" : tactic => do
  evalTactic (← `(tactic| simp only [List.append_assoc] at *))
  let mut pending := true
  while pending do
    pending := false
    let goal ← getMainGoal
    pending ← goal.withContext do
      for decl in ← getLCtx do
        if decl.isImplementationDetail then continue
        let some (_, lhs, _) := decl.type.eq? | continue
        let isFrame := lhs.getAppFn.isConstOf ``Qsag.frameList
        let args := lhs.getAppArgs
        let isAppend := lhs.getAppFn.isConstOf ``HAppend.hAppend && args.size == 6 &&
          args[4]!.getAppFn.isConstOf ``Qsag.frameList
        unless isFrame || isAppend do continue
        let proof? ← try
          pure <| some (← mkAppM (if isFrame then ``Qsag.frameList_inj
            else ``Qsag.frameList_append_inj) #[decl.toExpr])
          catch _ => pure none
        if let some proof := proof? then
          let next ← goal.assert `_frameParts (← inferType proof) proof
          let (fid, next) ← next.intro1
          let next ← next.clear decl.fvarId
          if isFrame then replaceMainGoal [next]
          else
            let cases ← next.cases fid
            replaceMainGoal (cases.toList.map (·.mvarId))
          return true
      return false
  let goal ← getMainGoal
  goal.withContext do
    goal.assign (← framingConclusion (← goal.getType))
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

/-! ### `by mask_bijection_hop` — Constructive `SimpleEquiv` & `qsum` Pad-Bijection Synthesizer -/

/-- Search an expression `body` for `SimpleEquiv.toFun _ _ enum _`, returning `enum`. -/
private meta partial def findEnumInExpr? (e : Expr) : Option Expr :=
  let e := stripMData e
  let fn := stripMData e.getAppFn
  let args := e.getAppArgs
  if fn.isConstOf ``Qsag.SimpleEquiv.toFun && args.size == 4 then
    some args[2]!
  else
    args.findSome? findEnumInExpr? <|>
      match e with
      | .lam _ _ b _ => findEnumInExpr? b
      | .letE _ _ v b _ => findEnumInExpr? v <|> findEnumInExpr? b
      | .proj _ _ inner => findEnumInExpr? inner
      | _ => none

/-- Check whether `sub` is definitionally equal to `sampleExpr`. -/
private meta def matchesSample (sub sampleExpr : Expr) : MetaM Bool :=
  withoutModifyingState (isDefEq (stripMData sub) (stripMData sampleExpr))

/-- Search `body` for a mask expression `mask ^^^ sampleExpr`, `sampleExpr ^^^ mask`,
    `mask != sampleExpr`, or `sampleExpr != mask` applied to `sampleExpr`. -/
private meta partial def findXorMaskForSample? (body sampleExpr : Expr) : MetaM (Option Expr) := do
  let body := stripMData body
  let fn := stripMData body.getAppFn
  let args := body.getAppArgs
  if fn.isConstOf ``HXor.hXor && args.size == 6 then
    let lhs := args[4]!
    let rhs := args[5]!
    if ← matchesSample rhs sampleExpr then
      if !(lhs.hasLooseBVars) then return some lhs
    if ← matchesSample lhs sampleExpr then
      if !(rhs.hasLooseBVars) then return some rhs
  if fn.isConstOf ``bne && args.size == 4 then
    let lhs := args[2]!
    let rhs := args[3]!
    if ← matchesSample rhs sampleExpr then
      if !(lhs.hasLooseBVars) then return some lhs
    if ← matchesSample lhs sampleExpr then
      if !(rhs.hasLooseBVars) then return some rhs
  if fn.isConstOf ``Bool.xor && args.size == 2 then
    let lhs := args[0]!
    let rhs := args[1]!
    if ← matchesSample rhs sampleExpr then
      if !(lhs.hasLooseBVars) then return some lhs
    if ← matchesSample lhs sampleExpr then
      if !(rhs.hasLooseBVars) then return some rhs
  for a in args do
    if let some m ← findXorMaskForSample? a sampleExpr then
      return some m
  match body with
  | .letE _ _ v b _ =>
    if let some m ← findXorMaskForSample? v sampleExpr then return some m
    return (← findXorMaskForSample? (b.instantiate1 v) sampleExpr)
  | .proj _ _ inner => findXorMaskForSample? inner sampleExpr
  | _ => return none

/-- Synthesize a `SimpleEquiv Ω Ω` pad bijection for sample `sampleExpr : Ω` appearing in `body`. -/
private meta partial def synthesizePadEquiv (omegaTy body sampleExpr : Expr) : MetaM Expr := do
  let omegaWhnf := stripMData (← whnf omegaTy)
  let fn := stripMData omegaWhnf.getAppFn
  let args := omegaWhnf.getAppArgs
  if fn.isConstOf ``Prod && args.size == 2 then
    let fstSample ← mkAppM ``Prod.fst #[sampleExpr]
    let sndSample ← mkAppM ``Prod.snd #[sampleExpr]
    let e1 ← synthesizePadEquiv args[0]! body fstSample
    let e2 ← synthesizePadEquiv args[1]! body sndSample
    return (← mkAppM ``Qsag.SimpleEquiv.prodCongr #[e1, e2])
  if fn.isConstOf ``BitVec && args.size == 1 then
    if let some mask ← findXorMaskForSample? body sampleExpr then
      return (← mkAppM ``Qsag.bvXorEquiv #[mask])
    return (← mkAppM ``Qsag.SimpleEquiv.refl #[omegaTy])
  if omegaWhnf.isConstOf ``UInt64 then
    if let some mask ← findXorMaskForSample? body sampleExpr then
      return (← mkAppM ``Qsag.u64XorEquiv #[mask])
    return (← mkAppM ``Qsag.SimpleEquiv.refl #[omegaTy])
  if omegaWhnf.isConstOf ``Bool then
    if let some mask ← findXorMaskForSample? body sampleExpr then
      return (← mkAppM ``Qsag.boolXorEquiv #[mask])
    return (← mkAppM ``Qsag.SimpleEquiv.refl #[omegaTy])
  return (← mkAppM ``Qsag.SimpleEquiv.refl #[omegaTy])

/-- Discharge the pointwise obligation produced by `qsum_bijection_hop_eq`. -/
private meta def dischargeMaskPointwise (goal : MVarId) : TacticM (List MVarId) := do
  let (omegaFVar, goalIntro) ← goal.intro `_ω
  let isProd ← goalIntro.withContext do
    let ty ← whnf (← omegaFVar.getType)
    pure ((stripMData ty.getAppFn).isConstOf ``Prod && ty.getAppArgs.size == 2)
  let postIntroGoals ←
    if isProd then
      let subgs ← goalIntro.cases omegaFVar
      pure (subgs.toList.map (·.mvarId))
    else
      pure [goalIntro]
  let stx ← `(tactic| (
    try dsimp only [
      Qsag.SimpleEquiv.prodCongr, Qsag.SimpleEquiv.refl, Qsag.SimpleEquiv.symm,
      Qsag.SimpleEquiv.trans, Qsag.bvXorEquiv, Qsag.u64XorEquiv, Qsag.boolXorEquiv,
      Qsag.ringAddEquiv
    ]
    try simp only [
      Qsag.SimpleEquiv.refl_toFun, Qsag.SimpleEquiv.symm_toFun,
      Qsag.SimpleEquiv.trans_toFun, Qsag.SimpleEquiv.prodCongr_toFun,
      Qsag.bvXorEquiv_toFun, Qsag.u64XorEquiv_toFun, Qsag.boolXorEquiv_toFun,
      Qsag.ringAddEquiv_toFun
    ]
    try simp only [
      Qsag.bv_xor_self, Qsag.bv_xor_zero, Qsag.bv_zero_xor,
      Qsag.bv_xor_cancel_right, Qsag.bv_xor_cancel_left, Qsag.bv_xor_cancel_mid,
      Qsag.bv_xor_cancel_outer,
      Qsag.u64_xor_self, Qsag.u64_xor_zero, Qsag.u64_zero_xor,
      Qsag.u64_xor_cancel_right, Qsag.u64_xor_cancel_left, Qsag.u64_xor_cancel_mid,
      Qsag.u64_xor_cancel_outer,
      Qsag.u8_xor_self, Qsag.u8_xor_zero, Qsag.u8_zero_xor,
      Qsag.u8_xor_cancel_right, Qsag.u8_xor_cancel_left, Qsag.u8_xor_cancel_mid,
      Qsag.u8_xor_cancel_outer,
      Qsag.bool_xor_self, Qsag.bool_xor_false, Qsag.bool_false_xor,
      Qsag.bool_xor_cancel_right, Qsag.bool_xor_cancel_left, Qsag.bool_xor_cancel_mid,
      Qsag.bool_xor_cancel_outer,
      Qsag.bool_bne_self, Qsag.bool_bne_false, Qsag.bool_false_bne,
      Qsag.bool_bne_cancel_right, Qsag.bool_bne_cancel_left, Qsag.bool_bne_cancel_mid,
      Qsag.bool_bne_cancel_outer,
      Qsag.ring_add_sub_cancel_right, Qsag.ring_sub_add_cancel_right
    ]
    try simp only [
      Qsag.bv_xor_assoc, Qsag.bv_xor_self, Qsag.bv_xor_zero, Qsag.bv_zero_xor,
      Qsag.bv_xor_cancel_right, Qsag.bv_xor_cancel_left, Qsag.bv_xor_cancel_mid,
      Qsag.bv_xor_cancel_outer,
      Qsag.u64_xor_assoc, Qsag.u64_xor_self, Qsag.u64_xor_zero, Qsag.u64_zero_xor,
      Qsag.u64_xor_cancel_right, Qsag.u64_xor_cancel_left, Qsag.u64_xor_cancel_mid,
      Qsag.u64_xor_cancel_outer,
      Qsag.u8_xor_assoc, Qsag.u8_xor_self, Qsag.u8_xor_zero, Qsag.u8_zero_xor,
      Qsag.u8_xor_cancel_right, Qsag.u8_xor_cancel_left, Qsag.u8_xor_cancel_mid,
      Qsag.u8_xor_cancel_outer,
      Qsag.bool_xor_assoc, Qsag.bool_xor_self, Qsag.bool_xor_false, Qsag.bool_false_xor,
      Qsag.bool_xor_cancel_right, Qsag.bool_xor_cancel_left, Qsag.bool_xor_cancel_mid,
      Qsag.bool_xor_cancel_outer,
      Qsag.bool_bne_assoc, Qsag.bool_bne_self, Qsag.bool_bne_false, Qsag.bool_false_bne,
      Qsag.bool_bne_cancel_right, Qsag.bool_bne_cancel_left, Qsag.bool_bne_cancel_mid,
      Qsag.bool_bne_cancel_outer
    ]
    try rfl
  ))
  let mut rem : List MVarId := []
  for pg in postIntroGoals do
    let gs ← evalTacticAt stx pg
    for g in gs do
      if !(← g.isAssigned) then
        rem := rem ++ (← solveSingleXorGoal g)
  return rem

/-- Abstract `(enum.toFun idx)` out of a `qsum C (fun idx => body)` integrand to form `Ω → Nat`. -/
private meta def extractFinSumWeightFn (omegaTy enumExpr sumExpr : Expr) : MetaM Expr := do
  let args := (stripMData sumExpr).getAppArgs
  unless (stripMData sumExpr.getAppFn).isConstOf ``Qsag.qsum && args.size == 2 do
    throwError "mask_bijection_hop: `{sumExpr}` is not a `Qsag.qsum` application"
  let lamFn ← whnf args[1]!
  match stripMData lamFn with
  | .lam nm dom body bi =>
    withLocalDecl nm bi dom fun idxVar => do
      let bodyInst ← instantiateMVars (body.instantiate1 idxVar)
      let sampleExpr ← mkAppM ``Qsag.SimpleEquiv.toFun #[enumExpr, idxVar]
      let absBody ← kabstract bodyInst sampleExpr
      if absBody.hasLooseBVars then
        -- `kabstract` turned `sampleExpr` into `.bvar 0`; verify `idxVar` no longer occurs freely
        let checkClosed := absBody.instantiate1 (mkBVar 0)
        let _ := checkClosed
      if (absBody.instantiate1 enumExpr).containsFVar idxVar.fvarId! then
        throwError "mask_bijection_hop: `qsum` body depends on loop index `{nm}` outside `enum.toFun`"
      return Expr.lam `_ω omegaTy absBody .default
  | _ =>
    throwError "mask_bijection_hop: expected lambda integrand inside `qsum`"

syntax "mask_bijection_hop" (ppSpace term)? : tactic

elab_rules : tactic
  | `(tactic| mask_bijection_hop $eStx:term) => do
    let goal ← getMainGoal
    goal.withContext do
      let tgt := stripMData (← instantiateMVars (← goal.getType))
      let some (_, lhs, rhs) := tgt.eq?
        | throwError "mask_bijection_hop: expected `qsum C ... = qsum C ...` equality goal"
      let some enumExpr := findEnumInExpr? lhs <|> findEnumInExpr? rhs
        | throwError "mask_bijection_hop: could not locate `enum.toFun` inside `qsum` goal"
      let enumTy := stripMData (← whnf (← inferType enumExpr))
      unless (stripMData enumTy.getAppFn).isConstOf ``Qsag.SimpleEquiv && enumTy.getAppArgs.size == 2 do
        throwError "mask_bijection_hop: `{enumExpr}` is not a `SimpleEquiv`"
      let omegaTy := enumTy.getAppArgs[1]!
      let fExpr ← extractFinSumWeightFn omegaTy enumExpr lhs
      let gExpr ← extractFinSumWeightFn omegaTy enumExpr rhs
      let eExpr ← Tactic.elabTermEnsuringType eStx (← mkAppM ``Qsag.SimpleEquiv #[omegaTy, omegaTy])
      let hopThm ← mkAppOptM ``Qsag.qsum_bijection_hop_eq
        #[some omegaTy, none, some enumExpr, some eExpr, some fExpr, some gExpr]
      let subgoals ← goal.apply hopThm
      let mut rem : List MVarId := []
      for sg in subgoals do
        rem := rem ++ (← dischargeMaskPointwise sg)
      replaceMainGoal rem
  | `(tactic| mask_bijection_hop) => do
    let goal ← getMainGoal
    goal.withContext do
      let tgt := stripMData (← instantiateMVars (← goal.getType))
      if (stripMData tgt.getAppFn).isConstOf ``Qsag.SimpleEquiv && tgt.getAppArgs.size == 2 then
        let a := tgt.getAppArgs[0]!
        let b := tgt.getAppArgs[1]!
        if ← isDefEq a b then
          let reflEq ← mkAppM ``Qsag.SimpleEquiv.refl #[a]
          goal.assign reflEq
          replaceMainGoal []
          return
      let some (_, lhs, rhs) := tgt.eq?
        | throwError "mask_bijection_hop: expected `qsum` equality or `SimpleEquiv` goal"
      let lhsArgs := lhs.getAppArgs
      unless (stripMData lhs.getAppFn).isConstOf ``Qsag.qsum && lhsArgs.size == 2 do
        throwError "mask_bijection_hop: LHS `{lhs}` is not a `Qsag.qsum` application"
      let some enumExpr := findEnumInExpr? lhs <|> findEnumInExpr? rhs
        | throwError "mask_bijection_hop: could not locate `enum.toFun` inside `qsum` goal"
      let enumTy := stripMData (← whnf (← inferType enumExpr))
      unless (stripMData enumTy.getAppFn).isConstOf ``Qsag.SimpleEquiv && enumTy.getAppArgs.size == 2 do
        throwError "mask_bijection_hop: `{enumExpr}` is not a `SimpleEquiv`"
      let omegaTy := enumTy.getAppArgs[1]!
      let fExpr ← extractFinSumWeightFn omegaTy enumExpr lhs
      let gExpr ← extractFinSumWeightFn omegaTy enumExpr rhs
      let lamFn ← whnf lhsArgs[1]!
      let eExpr ← match stripMData lamFn with
        | .lam nm dom body bi =>
          withLocalDecl nm bi dom fun idxVar => do
            let bodyInst := body.instantiate1 idxVar
            let sampleExpr ← mkAppM ``Qsag.SimpleEquiv.toFun #[enumExpr, idxVar]
            synthesizePadEquiv omegaTy bodyInst sampleExpr
        | _ => mkAppM ``Qsag.SimpleEquiv.refl #[omegaTy]
      let hopThm ← mkAppOptM ``Qsag.qsum_bijection_hop_eq
        #[some omegaTy, none, some enumExpr, some eExpr, some fExpr, some gExpr]
      let subgoals ← goal.apply hopThm
      let mut rem : List MVarId := []
      for sg in subgoals do
        rem := rem ++ (← dischargeMaskPointwise sg)
      replaceMainGoal rem

end Qsag.Tactic.AssuranceKit

/-! ## 4. Self-Tests of `#verify_constructive` & Constructive Automation -/

namespace Qsag

theorem aux_lemma_preserves_local_value (x : Nat) :
    let y := x + 1
    y = x + 1 := by
  intro y
  qsag_aux_lemma => rfl

/-- Smoke test: `bv_xor_cancel` cancels permuted 4-party shares on polymorphic width `w : Nat`. -/
theorem bv_three_share_fault_shift {w : Nat} (s0 s1 s2 delta : BitVec w) :
    ((s0 ^^^ delta) ^^^ s1) ^^^ s2 = (((s0 ^^^ s1) ^^^ s2) ^^^ delta) := by
  bv_xor_cancel

#verify_constructive
  Qsag.bv_eq_of_getLsbD_eq
  Qsag.bv_three_share_fault_shift
  Qsag.qsum_bijection_hop_eq

/-! End-to-end regressions: each audited proof is kernel-checked, including the
large reflected goal and both successful/error monadic branches. -/
theorem xor_rss16 (a b c d e f g h i j k l m n o p : BitVec 256) :
    (a ^^^ b ^^^ c ^^^ d ^^^ e ^^^ f ^^^ g ^^^ h ^^^ i ^^^ j ^^^ k ^^^ l ^^^ m ^^^ n ^^^ o ^^^ p) ^^^
    (p ^^^ n ^^^ l ^^^ j ^^^ h ^^^ f ^^^ d ^^^ b ^^^ o ^^^ m ^^^ k ^^^ i ^^^ g ^^^ e ^^^ c ^^^ a) = 0 := by
  bv_xor_cancel

theorem xor_rss32 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 : BitVec 256) :
    (a0 ^^^ a1 ^^^ a2 ^^^ a3 ^^^ a4 ^^^ a5 ^^^ a6 ^^^ a7 ^^^ a8 ^^^ a9 ^^^ a10 ^^^ a11 ^^^ a12 ^^^ a13 ^^^ a14 ^^^ a15 ^^^ a16 ^^^ a17 ^^^ a18 ^^^ a19 ^^^ a20 ^^^ a21 ^^^ a22 ^^^ a23 ^^^ a24 ^^^ a25 ^^^ a26 ^^^ a27 ^^^ a28 ^^^ a29 ^^^ a30 ^^^ a31) ^^^
    (a0 ^^^ a2 ^^^ a4 ^^^ a6 ^^^ a8 ^^^ a10 ^^^ a12 ^^^ a14 ^^^ a16 ^^^ a18 ^^^ a20 ^^^ a22 ^^^ a24 ^^^ a26 ^^^ a28 ^^^ a30 ^^^ a31 ^^^ a29 ^^^ a27 ^^^ a25 ^^^ a23 ^^^ a21 ^^^ a19 ^^^ a17 ^^^ a15 ^^^ a13 ^^^ a11 ^^^ a9 ^^^ a7 ^^^ a5 ^^^ a3 ^^^ a1) = 0 := by
  bv_xor_cancel

theorem frame_five (a b c d e a' b' c' d' e' : List UInt8)
    (tail tail' : List UInt8)
    (h : frameList a ++ frameList b ++ frameList c ++ frameList d ++ frameList e ++ tail =
      frameList a' ++ frameList b' ++ frameList c' ++ frameList d' ++ frameList e' ++ tail') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' ∧ e = e' ∧ tail = tail' := by
  frame_prefix_inj

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

namespace AssuranceRegression
structure State where
  counter : Nat

def reachable (s : State) : Prop := s.counter = 0
def step (s : State) : State := ⟨s.counter + 1⟩
def mutant (s : State) : State := s

theorem security (s : State) (h : reachable s) : (step s).counter = 1 := by
  exact congrArg (· + 1) h

theorem witness : ∃ s : State, reachable s ∧ (step s).counter = 1 :=
  ⟨⟨0⟩, rfl, rfl⟩

theorem inhabitedWitness : Nonempty {s : State // reachable s} := ⟨⟨⟨0⟩, rfl⟩⟩

theorem tooth : ∃ s : State, reachable s ∧ (mutant s).counter ≠ (step s).counter := by
  exact ⟨⟨0⟩, rfl, by decide⟩

theorem securityRenamed (t : State) (hr : reachable t) : (step t).counter = 1 :=
  security t hr

theorem trivialTooth : True := True.intro
theorem unrelated : (1 : Nat) ≠ 2 := by decide
theorem reflexiveTooth (s : State) : step s = step s := rfl
theorem unused (s : State) (_h : reachable s) : step s = step s := rfl
theorem impossible (n : Nat) (ha : n = 1) (hb : n = 2) : False := by
  have bad : (1 : Nat) = 2 := ha.symm.trans hb
  cases bad
theorem impossibleBool (b : Bool) (ht : b = true) (hf : b = false) : False := by
  have bad : true = false := ht.symm.trans hf
  cases bad
theorem emptyPremise (x : Empty) : False := nomatch x
theorem pemptyPremise (x : PEmpty) : False := nomatch x
theorem falsePremise (h : False) : False := h

theorem sameZero (n : Nat) (h : n = 0) (h' : n = Nat.zero) : n = 0 ∧ n = Nat.zero := ⟨h, h'⟩
#verify_constructive sameZero

theorem selfNe (n : Nat) (h : n ≠ n) : False := h rfl
theorem conditionalWitness (s : State) (h : reachable s) : ∃ t, reachable t := ⟨s, h⟩
theorem detachedWitness : ∃ s : State, step s = step s := ⟨⟨1⟩, rfl⟩

#verify_constructive security witness tooth
#verify_inhabited security witness
#verify_inhabited security inhabitedWitness
#tooth_pair security vs tooth
#tooth_pair security tooth
def BelowOne (n : Nat) : Prop := n < 1
theorem contradictory (n : Nat) (h : BelowOne n) (hn : ¬ BelowOne n) : n = 42 :=
  False.elim (hn h)
theorem belowWitness : ∃ n, BelowOne n := ⟨0, Nat.zero_lt_succ 0⟩
theorem emptySubtypeWitness (s : {_n : Nat // False}) : ∃ n, BelowOne n :=
  False.elim s.property
theorem wrappedTruth : True := trivialTooth
theorem scalarSecurity (x : UInt64) : x = x := rfl
theorem scalarTooth : ∃ x : UInt64, x = 0 ∧ x ≠ 1 := ⟨0, rfl, by decide⟩
def HasLenTwo (xs : List Nat) : Prop := xs.length = 2
theorem bogusListDefaulting (xs ys : List Nat) (_hLen : HasLenTwo xs) (_hZero : ys = [0, 0]) :
    xs.length + ys.length = 4 := by
  subst _hZero
  simpa [HasLenTwo] using _hLen
theorem nonzeroListWitness : ∃ xs ys : List Nat, HasLenTwo xs ∧ ys.length = 2 :=
  ⟨[1, 2], [3, 4], rfl, rfl⟩
end AssuranceRegression

#verify_constructive xorEval_norm_eq XorTree.norm_sound xor_rss16 xor_rss32 frameList_append_inj
  frame_five mir_option_test mir_except_test

end Qsag
namespace Qsag.Tactic.AssuranceKit
open Lean Meta Elab Command Tactic
private meta def expectRejection (label : String) (action : CommandElabM Unit) : CommandElabM Unit := do
  let rejected ← try action; pure false catch _ => pure true
  unless rejected do throwError "negative assurance self-test accepted {label}"

run_cmd do
  expectRejection "wrapped truth" do
    discard <| verifyConstructiveDecl (← `(ident| Qsag.AssuranceRegression.wrappedTruth))
  expectRejection "primitive carrier overlap" do
    checkToothPair (← `(ident| Qsag.AssuranceRegression.scalarSecurity))
      (← `(ident| Qsag.AssuranceRegression.scalarTooth))
  let (_, impossible) ← verifyConstructiveDecl (← `(ident| Qsag.AssuranceRegression.contradictory))
  let (_, reachable) ← verifyConstructiveDecl (← `(ident| Qsag.AssuranceRegression.belowWitness))
  expectRejection "contradictory joint premises" (liftTermElabM <| checkInhabited impossible reachable)
  let (_, emptyWitness) ← verifyConstructiveDecl (← `(ident| Qsag.AssuranceRegression.emptySubtypeWitness))
  expectRejection "empty subtype parameter" (liftTermElabM <| checkInhabited impossible emptyWitness)
  let (_, bogusListSec) ← verifyConstructiveDecl (← `(ident| Qsag.AssuranceRegression.bogusListDefaulting))
  let (_, nonzeroListWit) ← verifyConstructiveDecl (← `(ident| Qsag.AssuranceRegression.nonzeroListWitness))
  expectRejection "unbound list witness replaced by default"
    (liftTermElabM <| checkInhabited bogusListSec nonzeroListWit)
  let sec ← `(ident| Qsag.AssuranceRegression.security)
  for t in #[← `(ident| Qsag.AssuranceRegression.trivialTooth),
      ← `(ident| Qsag.AssuranceRegression.unrelated),
      ← `(ident| Qsag.AssuranceRegression.reflexiveTooth),
      ← `(ident| Qsag.AssuranceRegression.detachedWitness),
      ← `(ident| Qsag.AssuranceRegression.securityRenamed), sec] do
    expectRejection "tooth" (checkToothPair sec t)
  for t in #[← `(ident| Qsag.AssuranceRegression.unused),
      ← `(ident| Qsag.AssuranceRegression.impossible),
      ← `(ident| Qsag.AssuranceRegression.selfNe),
      ← `(ident| Qsag.AssuranceRegression.impossibleBool),
      ← `(ident| Qsag.AssuranceRegression.emptyPremise),
      ← `(ident| Qsag.AssuranceRegression.pemptyPremise),
      ← `(ident| Qsag.AssuranceRegression.falsePremise)] do
    expectRejection "premise" (discard <| verifyConstructiveDecl t)
  let (_, s) ← verifyConstructiveDecl sec
  for t in #[← `(ident| Qsag.AssuranceRegression.conditionalWitness),
      ← `(ident| Qsag.AssuranceRegression.detachedWitness)] do
    expectRejection "inhabitedness" do
      let (_, w) ← verifyConstructiveDecl t
      liftTermElabM <| checkInhabited s w
end Qsag.Tactic.AssuranceKit

end
