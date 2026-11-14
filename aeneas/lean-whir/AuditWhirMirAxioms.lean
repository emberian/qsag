module
import Lean
import all Lean.Util.CollectAxioms
import all QsagWhirVerified
import all QsagWhirVerified.Proofs
import all QsagWhirVerified.Arithmetic
import all QsagWhirVerified.Funs
import all QsagWhirVerified.Types
import all Aeneas
import all Aeneas.Elab.Attrs
import all Aeneas.Std.Containers
import all Aeneas.Std.Types

/- Compile-time linter/attribute registration is meta infrastructure. Only declarations
marked meta in Aeneas.Elab.Attrs are excluded; pure declarations and all proof
dependency closures keep the constructive allowlist. -/
open Lean Elab Command in
run_cmd do
  let negative ← Lean.collectAxioms ``Classical.choice
  if (negative.filter fun ax => ax != ``propext && ax != ``Quot.sound).isEmpty then
    throwError "WHIR MIR axiom audit negative control unexpectedly passed"
  let env := (← getEnv).setExporting false
  let mut checked : Nat := 0
  let mut rejectedCount : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let owner := env.header.moduleNames[idx.toNat]!.toString
      if (owner == "QsagWhirVerified" || owner.startsWith "QsagWhirVerified." ||
          owner == "Aeneas" || owner.startsWith "Aeneas.") &&
          !(owner == "Aeneas.Elab.Attrs" && isMarkedMeta env name) then
        checked := checked + 1
        let deps ← withEnv env <| Lean.collectAxioms name
        let rejected := deps.filter fun n => n != ``propext && n != ``Quot.sound
        if !rejected.isEmpty then
          rejectedCount := rejectedCount + 1
          logInfo m!"REJECT {name} (module {owner}): {rejected}"
  if checked == 0 then
    throwError "Empty WHIR MIR audit coverage"
  if rejectedCount > 0 then
    throwError "WHIR MIR axiom policy failed: {rejectedCount} of {checked} declarations rejected"
  logInfo m!"WHIR MIR audit: {checked} declarations across QsagWhirVerified + Aeneas, zero rejected (allowlist: propext, Quot.sound)"

open Lean

public def main : IO UInt32 := do
  initSearchPath (← findSysroot) [".lake/build/lib/lean"]
  let imported ← importModules #[{ module := `AuditWhirMirAxioms, importAll := true }] {}
  let env := imported.setExporting false
  let summaries := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  let (negative, checked, theorems, modules, failures) := CollectAxioms.runM (env.setExporting false) do
    let negative ← CollectAxioms.collectAndGet summaries.find? ``Classical.choice
    let mut checked := 0
    let mut theorems := 0
    let mut modules : Array Name := #[]
    let mut failures : Array (Name × Array Name) := #[]
    for (name, _) in env.constants.toList do
      if let some idx := env.getModuleIdxFor? name then
        let owner := env.header.moduleNames[idx.toNat]!.toString
        if (owner == "QsagWhirVerified" || owner.startsWith "QsagWhirVerified." ||
            owner == "Aeneas" || owner.startsWith "Aeneas.") &&
            !(owner == "Aeneas.Elab.Attrs" && isMarkedMeta env name) then
          checked := checked + 1
          if let some (.thmInfo _) := env.find? name then theorems := theorems + 1
          let ownerName := env.header.moduleNames[idx.toNat]!
          if !modules.contains ownerName then modules := modules.push ownerName
          let axioms ← CollectAxioms.collectAndGet summaries.find? name
          let forbidden := axioms.filter fun ax => ax != ``propext && ax != ``Quot.sound
          if !forbidden.isEmpty then
            failures := failures.push (name, forbidden)
    return (negative, checked, theorems, modules, failures)
  if (negative.filter fun ax => ax != ``propext && ax != ``Quot.sound).isEmpty then
    throw (IO.userError "WHIR MIR axiom audit negative control unexpectedly passed")
  for (name, forbidden) in failures do
    IO.println s!"REJECT {name}: {forbidden}"
  IO.println s!"WHIR MIR axiom audit: {checked} declarations, {theorems} theorems, {modules.size} modules; {failures.size} rejected"
  return if checked > 0 && failures.isEmpty then 0 else 1
