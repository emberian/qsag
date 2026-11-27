module
public import Lean

public section
open Lean

namespace QsagAudit

/-- Proof-automation modules are exactly the `Qsag` modules with a `Tactic` path component
(`Qsag.Tactic.*`, `Qsag.Math.Tactic.*`, `Qsag.Exec.Tactic.*`). -/
def isTacticModule (modName : Name) : Bool :=
  modName.components.contains `Tactic

/-- Only marked tactic code and the compiler-generated definitions immediately beneath it
are excluded. Ordinary theorems are always checked, including private ones. A library
consumer of an excluded helper is still checked through its complete axiom dependency cone. -/
def isCompileTimeAssurance (env : Environment) (name : Name) : Bool := Id.run do
  let some idx := env.getModuleIdxFor? name | return false
  let modName := env.header.moduleNames[idx.toNat]!
  unless isTacticModule modName do return false
  let some info := env.find? name | return false
  if info matches .thmInfo _ then return false
  if info matches .axiomInfo _ then return false
  if isMarkedMeta env name then return true
  unless info matches .defnInfo _ do return false
  let .str parent leaf := name | return false
  return isMarkedMeta env parent &&
    (leaf == "_sunfold" || leaf == "_f" || leaf == "_unsafe_rec" ||
      leaf.startsWith "match_" || leaf.startsWith "_sparseCasesOn_")

private def hasDigitSuffix (pfx cs : List Char) : Bool :=
  cs.take pfx.length == pfx &&
    let rest := cs.drop pfx.length
    !rest.isEmpty && rest.all Char.isDigit

private def isSynthesizedComponent (s : String) : Bool :=
  let cs := s.toList
  cs.head? == some '_' ||
  s == "rec" || s == "recOn" || s == "casesOn" || s == "brecOn" ||
  s == "below" || s == "ibelow" || s == "binductionOn" ||
  s == "noConfusion" || s == "noConfusionType" ||
  s == "ctorIdx" || s == "ctorElim" || s == "ctorElimType" || s == "toCtorIdx" ||
  s == "inj" || s == "injEq" || s == "sizeOf_spec" ||
  s == "eq_def" || s == "eq_unfold" || s == "congr_simp" ||
  s == "induct" || s == "induct_unfolding" ||
  s == "fun_cases" || s == "fun_cases_unfolding" ||
  s == "mutual" || s == "splitter" || s == "public_eqs" ||
  hasDigitSuffix ['e', 'q', '_'] cs ||
  hasDigitSuffix ['p', 'u', 'b', 'l', 'i', 'c', '_', 'e', 'q', '_'] cs ||
  hasDigitSuffix ['m', 'a', 't', 'c', 'h', '_'] cs ||
  hasDigitSuffix ['p', 'r', 'o', 'o', 'f', '_'] cs

/-- Identifies compiler- and elaborator-synthesized constants (`.rec`, `.casesOn`,
`.noConfusion`, `.eq_*`, `._cstage*`, `._proof_*`, `._sunfold*`, match splitters,
constructors, and structure projections) so the user-written declaration/theorem
census is separated cleanly from total kernel constants audited for axiom purity. -/
def isCompilerGenerated (env : Environment) (name : Name) : Bool := Id.run do
  let some info := env.find? name | return true
  if name.hasMacroScopes then return true
  if info matches .recInfo _ | .ctorInfo _ | .quotInfo _ then return true
  if env.isProjectionFn name then return true
  let u := privateToUserName name
  for comp in u.components do
    match comp with
    | .str .anonymous s =>
      if isSynthesizedComponent s then return true
    | _ => return true
  return false

end QsagAudit
