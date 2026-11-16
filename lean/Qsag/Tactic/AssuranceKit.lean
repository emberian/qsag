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

public meta section
open Lean Meta Elab Command

/-- Inline only registered compiler matchers, preserving named algorithm boundaries.
    The bounded expansion is followed by a private-name check and kernel typechecking. -/
private def expandEquationMatchers (env : Environment) (e : Expr) : Expr :=
  (List.range 64).foldl (fun e _ => e.replace fun sub =>
    match sub with
    | .const n us =>
      if isPrivateName n && (getMatcherInfoCore? env n).isSome then
        match env.find? n with
        | some (.defnInfo ci) => some (ci.value.instantiateLevelParams ci.levelParams us)
        | _ => none
      else none
    | _ => none) e

/-- Export selected, kernel-checked compiler equations in their owning module.
    Public statements may not mention private helpers. No definition body is exposed. -/
syntax (name := exportEqnsCmd) "#export_eqns " ident+ : command
elab_rules : command
  | `(command| #export_eqns $[$ids:ident]*) => do
    for id in ids do
      let fn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
      let env ← getEnv
      if (env.getModuleIdxFor? fn).isSome then
        throwErrorAt id "Export equations in the definition's owning module: {fn}"
      if isPrivateName fn then
        throwErrorAt id "The definition must be public: {privateToUserName fn}"
      let some eqns ← liftTermElabM (getEqnsFor? fn) |
        throwErrorAt id "No compiler equations for {fn}"
      if eqns.isEmpty then throwErrorAt id "No compiler equations for {fn}"
      -- Preflight every type before publishing any of the selected equations.
      let infos ← eqns.mapM getConstInfo
      let equationTypes := infos.map fun ci => expandEquationMatchers env ci.type
      for ty in equationTypes do
        for dep in ty.getUsedConstants do
          if isPrivateName dep then
            throwErrorAt id "Equation type exposes a private helper {privateToUserName dep}; write a projection lemma instead"
      let mut levels : List Name := []
      let mut types : List Expr := []
      let mut values : List Expr := []
      for i in [:eqns.size] do
        let ci := infos[i]!
        let ty := equationTypes[i]!
        let name := fn ++ Name.mkSimple s!"public_eq_{i + 1}"
        let value := mkConst eqns[i]! (ci.levelParams.map mkLevelParam)
        liftTermElabM <| addDecl <| .thmDecl {
          name, levelParams := ci.levelParams, type := ty, value }
        for u in ci.levelParams do
          if !levels.contains u then levels := levels ++ [u]
        types := ty :: types
        values := mkConst name (ci.levelParams.map mkLevelParam) :: values
      let some lastType := types.head? | throwErrorAt id "Missing equation type"
      let some lastValue := values.head? | throwErrorAt id "Missing equation proof"
      let mut bundleType := lastType
      let mut bundleValue := lastValue
      for (ty, val) in types.tail!.zip values.tail! do
        bundleValue := mkApp4 (mkConst ``And.intro) ty bundleType val bundleValue
        bundleType := mkApp2 (mkConst ``And) ty bundleType
      liftTermElabM <| addDecl <| .thmDecl {
        name := fn ++ `public_eqs, levelParams := levels,
        type := bundleType, value := bundleValue }
end
