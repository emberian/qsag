module
/-
# Qsag.Tactic.AssuranceKit — `0-Classical` Proof Automation & Constructive Assurance Gates

Reusable Lean 4.35 tactic and command-elaboration infrastructure for QSAG (`LAW-M2`). This module
is proof support below every library layer: it imports `Qsag.Tactic.Prelude` and `Lean` only.
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
4. **`by frame_prefix_inj`**:
   Peels length-framed equalities (`frameList`) in the context, preserving every remainder.

The tactics that depend on library definitions live with those definitions:
`mask_bijection_hop` and the `SimpleEquiv` pad combinators in `Qsag.Math.Tactic.MaskBijection`,
`compose_forward_sim` and `mir_sim_step` in `Qsag.Exec.Tactic.SimulationKit`.
-/

public import Qsag.Tactic.Prelude
public meta import Lean

public section

namespace Qsag.Tactic.AssuranceKit
open Lean Meta Elab Tactic Command

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
  frame_five

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
