module
/-
# Qsag.Math.Tactic.MaskBijection — `SimpleEquiv` Pad Combinators and `mask_bijection_hop`

**`by mask_bijection_hop` / `by mask_bijection_hop <equiv>`**: relational pad-bijection synthesizer
discharging `qsum` uniform-mask invariance goals via `SimpleEquiv` combinators (`bvXorEquiv`,
`u64XorEquiv`, `boolXorEquiv`, `ringAddEquiv`, `SimpleEquiv.prodCongr`) and `bv_xor_cancel` with
`0 Classical.choice`. The combinators and the `qsum` hop lemma are stated over the finite-sum and
ring interfaces of `Qsag.Math.Algebra`.
-/

public import Qsag.Tactic.AssuranceKit
public import Qsag.Math.Algebra
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

#verify_constructive
  Qsag.qsum_bijection_hop_eq

end
