module
import Lean
import all Lean.Util.CollectAxioms

open Lean

/-- Runtime census of the same import-all environment checked by AuditMirAxioms.
Run from the package root, or with its Lake environment. A shared dependency cache
avoids revisiting the full proof graph separately for every declaration. -/
public def main : IO UInt32 := do
  initSearchPath (← findSysroot) [".lake/build/lib/lean", "../../lean/.lake/build/lib/lean"]
  let env ← importModules #[{ module := `AuditMirAxioms, importAll := true }] {}
  let summaries := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  let (negative, checked, failures) := CollectAxioms.runM (env.setExporting false) do
    let negative ← CollectAxioms.collectAndGet summaries.find? ``Classical.choice
    let mut checked := 0
    let mut failures : Array (Name × Array Name) := #[]
    for (name, _) in env.constants.toList do
      if let some idx := env.getModuleIdxFor? name then
        let owner := env.header.moduleNames[idx.toNat]!.toString
        if owner == "QsagSpecWeld" || owner == "QsagMirProofs" || owner == "QsagVerified" ||
            owner.startsWith "QsagVerified." then
          checked := checked + 1
          let axioms ← CollectAxioms.collectAndGet summaries.find? name
          let forbidden := axioms.filter fun ax => ax != ``propext && ax != ``Quot.sound
          if !forbidden.isEmpty then
            failures := failures.push (name, forbidden)
    return (negative, checked, failures)
  if (negative.filter fun ax => ax != ``propext && ax != ``Quot.sound).isEmpty then
    throw (IO.userError "MIR axiom audit negative control unexpectedly passed")
  for (name, forbidden) in failures do
    IO.println s!"REJECT {name}: {forbidden}"
  IO.println s!"MIR axiom audit: {checked} declarations; {failures.size} rejected"
  return if checked > 0 && failures.isEmpty then 0 else 1
