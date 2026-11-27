module
import Lean
import AxiomAuditSupport
import all Aeneas.Elab.Attrs
import all Lean.Util.CollectAxioms

open Lean

private def allowedAxiom (ax : Name) : Bool :=
  ax == ``propext || ax == ``Quot.sound

private def isPackageOwner (owner : String) : Bool :=
  owner == "QsagCustodyWeld" || owner == "QsagSpecWeld" || owner == "QsagMirProofs" ||
  owner == "QsagVerified" || owner.startsWith "QsagVerified."

private def isAeneasOwner (owner : String) : Bool :=
  owner == "Aeneas" || owner.startsWith "Aeneas."

private def isMetaElabHelper (env : Environment) (owner : String) (name : Name) : Bool :=
  (owner.startsWith "Aeneas.Elab." && (isDeclMeta env name || isDeclMeta env name.getPrefix)) ||
  QsagAudit.isCompileTimeAssurance env name

private def directDeps (info : ConstantInfo) : Array Name :=
  let tyDeps := info.type.getUsedConstants
  match info.value? (allowOpaque := true) with
  | some v => tyDeps ++ v.getUsedConstants
  | none => tyDeps

/-- Runtime census of the combined primitive and custody-weld import-all environments,
separating user-written/extracted `QsagVerified` & weld declarations from `Aeneas.*`
stdlib and compiler-synthesized constants while auditing the full transitive axiom closure. -/
public def main : IO UInt32 := do
  initSearchPath (← findSysroot) [".lake/build/lib/lean", "../../lean/.lake/build/lib/lean"]
  let imported ← importModules #[{ module := `AuditMirAxioms, importAll := true },
    { module := `QsagCustodyWeld, importAll := true }] {}
  let env := imported.setExporting false
  let summaries := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  let (negative, userDecls, userTheorems, pkgModules, pkgKernelConsts, aeneasConsts, transitiveConsts, failures) :=
    CollectAxioms.runM env do
      let negative ← CollectAxioms.collectAndGet summaries.find? ``Classical.choice
      let mut userDecls := 0
      let mut userTheorems := 0
      let mut pkgModules : Array Name := #[]
      let mut pkgKernelConsts := 0
      let mut aeneasConsts := 0
      let mut visited : NameSet := {}
      let mut todo : Array Name := #[]
      let mut failures : Array (Name × Array Name) := #[]
      for (name, info) in env.constants.toList do
        if let some idx := env.getModuleIdxFor? name then
          let ownerName := env.header.moduleNames[idx.toNat]!
          let owner := ownerName.toString
          if isMetaElabHelper env owner name then continue
          if isPackageOwner owner then
            pkgKernelConsts := pkgKernelConsts + 1
            if !pkgModules.contains ownerName then
              pkgModules := pkgModules.push ownerName
            if !QsagAudit.isCompilerGenerated env name then
              userDecls := userDecls + 1
              if info matches .thmInfo _ then
                userTheorems := userTheorems + 1
            if !visited.contains name then
              visited := visited.insert name
              todo := todo.push name
          else if isAeneasOwner owner then
            aeneasConsts := aeneasConsts + 1
            if !visited.contains name then
              visited := visited.insert name
              todo := todo.push name
      while h : todo.size > 0 do
        let cur := todo.back
        todo := todo.pop
        let axioms ← CollectAxioms.collectAndGet summaries.find? cur
        let forbidden := axioms.filter (!allowedAxiom ·)
        if !forbidden.isEmpty then
          failures := failures.push (cur, forbidden)
        if let some info := env.find? cur then
          for dep in directDeps info do
            if !visited.contains dep then
              if let some depIdx := env.getModuleIdxFor? dep then
                let depOwner := env.header.moduleNames[depIdx.toNat]!.toString
                if !isMetaElabHelper env depOwner dep then
                  visited := visited.insert dep
                  todo := todo.push dep
              else if (env.find? dep).isSome then
                visited := visited.insert dep
                todo := todo.push dep
      return (negative, userDecls, userTheorems, pkgModules, pkgKernelConsts, aeneasConsts, visited.size, failures)
  if (negative.filter (!allowedAxiom ·)).isEmpty then
    throw (IO.userError "MIR axiom audit negative control unexpectedly passed")
  for (name, forbidden) in failures do
    IO.println s!"REJECT {name}: {forbidden}"
  let userDefs := userDecls - userTheorems
  let otherDeps := transitiveConsts - (pkgKernelConsts + aeneasConsts)
  IO.println s!"MIR axiom audit (user-written & extracted QsagVerified.*): {userDecls} declarations ({userTheorems} theorems, {userDefs} definitions/types) across {pkgModules.size} modules"
  IO.println s!"MIR axiom audit (transitive closure): {transitiveConsts} kernel constants audited ({pkgKernelConsts} in QsagVerified/Weld, {aeneasConsts} in Aeneas stdlib, {otherDeps} reachable Qsag/Init/Std constants); {failures.size} rejected (allowlist: propext, Quot.sound; 0 Classical.choice, 0 sorryAx, 0 ofReduceBool)"
  return if userDecls > 0 && transitiveConsts >= pkgKernelConsts && failures.isEmpty then 0 else 1
