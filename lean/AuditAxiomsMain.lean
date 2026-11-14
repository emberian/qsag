module
import Lean
import AxiomAuditSupport
import all Lean.Util.CollectAxioms

open Lean

/-- Re-run the dependency census even when the library build is cached. -/
public def main : IO UInt32 := do
  initSearchPath (← findSysroot) [".lake/build/lib/lean"]
  let imported ← importModules #[{ module := `AuditAxioms, importAll := true }] {}
  let env := imported.setExporting false
  unless (env.find? `Qsag.bool_xor_self).isSome &&
      !QsagAudit.isCompileTimeAssurance env `Qsag.bool_xor_self do
    throw (IO.userError "Pure assurance theorem was omitted from the audit")
  let generatedMeta := env.constants.toList.any fun (name, _) =>
    name.toString.endsWith ".witnessHead._unsafe_rec" &&
      QsagAudit.isCompileTimeAssurance env name
  unless generatedMeta do
    throw (IO.userError "Generated tactic implementation was not identified")
  let summaries := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  let (negative, checked, theorems, failures) := CollectAxioms.runM env do
    let negative ← CollectAxioms.collectAndGet summaries.find? ``Classical.choice
    let mut checked := 0
    let mut theorems := 0
    let mut failures : Array (Name × Array Name) := #[]
    for (name, _) in env.constants.toList do
      if let some idx := env.getModuleIdxFor? name then
        let owner := env.header.moduleNames[idx.toNat]!
        if owner.toString.startsWith "Qsag." &&
            !QsagAudit.isCompileTimeAssurance env name then
          checked := checked + 1
          if let some (.thmInfo _) := env.find? name then theorems := theorems + 1
          let axioms ← CollectAxioms.collectAndGet summaries.find? name
          let forbidden := axioms.filter fun ax => ax != ``propext && ax != ``Quot.sound
          if !forbidden.isEmpty then failures := failures.push (name, forbidden)
    return (negative, checked, theorems, failures)
  if (negative.filter fun ax => ax != ``propext && ax != ``Quot.sound).isEmpty then
    throw (IO.userError "Axiom audit negative control unexpectedly passed")
  for (name, forbidden) in failures do IO.println s!"REJECT {name}: {forbidden}"
  let modules := env.header.moduleNames.filter (fun name => name.toString.startsWith "Qsag.")
  IO.println s!"Axiom audit: {checked} declarations, {theorems} theorems, {modules.size} modules; {failures.size} rejected"
  return if checked > 0 && failures.isEmpty then 0 else 1
