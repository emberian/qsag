module
import Lean
import AxiomAuditSupport
import all Lean.Util.CollectAxioms

open Lean

private def allowedAxiom (ax : Name) : Bool :=
  ax == ``propext || ax == ``Quot.sound

private def directDeps (info : ConstantInfo) : Array Name :=
  let tyDeps := info.type.getUsedConstants
  match info.value? (allowOpaque := true) with
  | some v => tyDeps ++ v.getUsedConstants
  | none => tyDeps

/-- Re-run the full transitive axiom-closure audit and separate user-written `Qsag.*`
declarations/theorems from compiler-generated helpers and stdlib dependencies. -/
public def main : IO UInt32 := do
  initSearchPath (← findSysroot) [".lake/build/lib/lean"]
  let imported ← importModules #[{ module := `AuditAxioms, importAll := true }] {}
  let env := imported.setExporting false
  unless (env.find? `Qsag.bool_xor_self).isSome &&
      !QsagAudit.isCompileTimeAssurance env `Qsag.bool_xor_self &&
      !QsagAudit.isCompilerGenerated env `Qsag.bool_xor_self do
    throw (IO.userError "Pure assurance theorem was omitted from the audit")
  let generatedMeta := env.constants.toList.any fun (name, _) =>
    name.toString.endsWith ".witnessHead._unsafe_rec" &&
      QsagAudit.isCompileTimeAssurance env name
  unless generatedMeta do
    throw (IO.userError "Generated tactic implementation was not identified")
  let summaries := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  let (negChoice, userDecls, userTheorems, pkgKernelConsts, transitiveConsts, failures) :=
    CollectAxioms.runM env do
      let negChoice ← CollectAxioms.collectAndGet summaries.find? ``Classical.choice
      let mut userDecls := 0
      let mut userTheorems := 0
      let mut pkgKernelConsts := 0
      let mut visited : NameSet := {}
      let mut todo : Array Name := #[]
      let mut failures : Array (Name × Array Name) := #[]
      for (name, info) in env.constants.toList do
        if let some idx := env.getModuleIdxFor? name then
          let owner := env.header.moduleNames[idx.toNat]!
          if owner.toString.startsWith "Qsag." &&
              !QsagAudit.isCompileTimeAssurance env name then
            pkgKernelConsts := pkgKernelConsts + 1
            if !QsagAudit.isCompilerGenerated env name then
              userDecls := userDecls + 1
              if info matches .thmInfo _ then
                userTheorems := userTheorems + 1
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
            if !visited.contains dep && (env.find? dep).isSome &&
                !QsagAudit.isCompileTimeAssurance env dep then
              visited := visited.insert dep
              todo := todo.push dep
      return (negChoice, userDecls, userTheorems, pkgKernelConsts, visited.size, failures)
  if (negChoice.filter (!allowedAxiom ·)).isEmpty then
    throw (IO.userError "Axiom audit negative control unexpectedly passed")
  for (name, forbidden) in failures do
    IO.println s!"REJECT {name}: {forbidden}"
  let modules := env.header.moduleNames.filter (fun name => name.toString.startsWith "Qsag.")
  let userDefs := userDecls - userTheorems
  let depConsts := transitiveConsts - pkgKernelConsts
  IO.println s!"Axiom audit (user-written Qsag.*): {userDecls} declarations ({userTheorems} theorems, {userDefs} definitions/types) across {modules.size} modules"
  IO.println s!"Axiom audit (transitive closure): {transitiveConsts} kernel constants audited ({pkgKernelConsts} in Qsag.* incl. compiler-generated helpers, {depConsts} reachable Init/Std constants); {failures.size} rejected (allowlist: propext, Quot.sound; 0 Classical.choice, 0 sorryAx, 0 ofReduceBool)"
  return if userDecls > 0 && transitiveConsts >= pkgKernelConsts && failures.isEmpty then 0 else 1
