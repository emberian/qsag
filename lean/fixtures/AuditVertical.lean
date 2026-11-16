module
public import Lean
import all Qsag.Machine.ElfFixtures
import all Qsag.Machine.ElfInvCerts
import all Qsag.Machine.ElfParse
import all Qsag.Machine.McRefine
import all Qsag.Machine.ElfVerify
import all Qsag.Machine.ElfFixtureVerify
import all Qsag.Machine.ElfFunctionalEquiv
import all Qsag.Machine.SydTv
import all Qsag.Machine.IsaCosim
open Lean Elab Command
elab "#auditVertical" : command => do
  let env := (← getEnv).setExporting false
  let targets : List Name := [`Qsag.Machine.ElfFixtures, `Qsag.Machine.ElfFixtures, `Qsag.Machine.ElfInvCerts, `Qsag.Machine.ElfParse, `Qsag.Machine.McRefine, `Qsag.Machine.ElfVerify, `Qsag.Machine.ElfFixtureVerify, `Qsag.Machine.ElfFunctionalEquiv, `Qsag.Machine.SydTv, `Qsag.Machine.IsaCosim]
  let negative ← withEnv env <| Lean.collectAxioms ``Classical.choice
  unless negative.contains ``Classical.choice do
    throwError "Axiom audit negative control failed"
  let mut total := 0
  let mut theorems := 0
  let mut rejected := 0
  for target in targets do
    let mut count := 0
    for (name, ci) in env.constants.toList do
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]! == target then
          count := count + 1
          total := total + 1
          if ci matches .thmInfo _ then theorems := theorems + 1
          let axioms ← withEnv env <| Lean.collectAxioms name
          let bad := axioms.filter fun ax => ax != ``propext && ax != ``Quot.sound
          unless bad.isEmpty do
            rejected := rejected + 1
            logError m!"REJECT {name}: {bad}"
    unless count > 0 do throwError "Empty audit module: {target}"
    logInfo m!"{target}: {count} declarations"
  logInfo m!"Vertical audit: {total} declarations, {theorems} theorems, {targets.length} modules; {rejected} rejected"
  unless rejected == 0 do throwError "Vertical axiom audit failed"
#auditVertical

