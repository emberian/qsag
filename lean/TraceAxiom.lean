module
/- Diagnostic dependency prefixes. A prefix may stop at an imported declaration
whose axiom summary is available but whose proof body is not exposed. -/
import all Qsag.Math.Goldilocks
import all Qsag.Math.BinaryTower
import all Qsag.Oracle.UcGames
import all Qsag.Oracle.Keccak
import all Qsag.Protocol.Threshold.ThresholdMpc
import all Qsag.Protocol.Threshold.Preprocessing
import all Qsag.Machine.ConstantTimeIsa
import all Qsag.Machine.ElfBinaryVerify
import all Qsag.Oracle.Poseidon2
import all Qsag.Protocol.Credentials.AdvancedMpcAndCreds
import Lean

open Lean

private partial def findAxiomPath (target name : Name) (visited : List Name) : CoreM (Option (List Name)) := do
  if name == target then return some [name]
  if visited.contains name then return none
  let axs ← collectAxioms name
  if !axs.contains target then return none
  let env := (← getEnv).setExporting false
  let some ci := env.checked.get.find? name | return some [name]
  let deps := ci.type.getUsedConstants
  let deps := match ci with
    | .defnInfo v => deps ++ v.value.getUsedConstants
    | .thmInfo v => deps ++ v.value.getUsedConstants
    | .opaqueInfo v => deps ++ v.value.getUsedConstants
    | .inductInfo v => deps ++ v.ctors.toArray
    | _ => deps
  for dep in deps do
    if let some path ← findAxiomPath target dep (name :: visited) then
      return some (name :: path)
  return some [name]

open Lean.Elab.Command in
run_cmd do
  let env ← getEnv
  for (root, _) in env.constants.toList do
    if !(root.toString.startsWith "Qsag." || root.toString.startsWith "_private.Qsag.") then continue
    let axioms ← Lean.collectAxioms root
    for target in axioms do
      if target != ``propext && target != ``Quot.sound then
        let path ← liftCoreM (findAxiomPath target root [])
        logInfo m!"{root}: {path}"
