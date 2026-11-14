module
import Lean
import all QsagWhirVerified
import all QsagWhirVerified.Proofs
import all QsagWhirVerified.Arithmetic
import all QsagWhirVerified.Funs
import all QsagWhirVerified.Types
import all Aeneas
import all Aeneas.Std.Containers
import all Aeneas.Std.Types

open Lean Elab Command in
run_cmd do
  let negative ← Lean.collectAxioms ``Classical.choice
  if (negative.filter fun ax => ax != ``propext && ax != ``Quot.sound).isEmpty then
    throwError "WHIR MIR axiom audit negative control unexpectedly passed"
  let env ← getEnv
  let mut checked : Nat := 0
  let mut rejectedCount : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let owner := env.header.moduleNames[idx.toNat]!.toString
      if owner == "QsagWhirVerified" || owner.startsWith "QsagWhirVerified." ||
          owner == "Aeneas" || owner.startsWith "Aeneas." then
        checked := checked + 1
        let deps ← Lean.collectAxioms name
        let rejected := deps.filter fun n => n != ``propext && n != ``Quot.sound
        if !rejected.isEmpty then
          rejectedCount := rejectedCount + 1
          logInfo m!"REJECT {name} (module {owner}): {rejected}"
  if checked == 0 then
    throwError "Empty WHIR MIR audit coverage"
  if rejectedCount > 0 then
    throwError "WHIR MIR axiom policy failed: {rejectedCount} of {checked} declarations rejected"
  logInfo m!"WHIR MIR audit: {checked} declarations across QsagWhirVerified + Aeneas, zero rejected (allowlist: propext, Quot.sound)"

public def main : IO Unit :=
  IO.println "WHIR MIR kernel dependency audit passed (negative control: Classical.choice rejected; allowlist: propext, Quot.sound)"
