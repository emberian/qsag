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

end QsagAudit
