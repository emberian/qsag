module
import Lean
public import QsagVerified.Proofs.AuthenticatedBeltAndRealSpecWeld
import all QsagVerified.Proofs.AuthenticatedBeltAndRealSpecWeld
public import QsagVerified.Proofs.RealSpecFieldWeld
import all QsagVerified.Proofs.RealSpecFieldWeld
public import QsagVerified.Proofs.RealSpecHashWeld
import all QsagVerified.Proofs.RealSpecHashWeld
public import QsagVerified.Proofs.RealSpecTowerWeld
import all QsagVerified.Proofs.RealSpecTowerWeld
public import QsagVerified.Proofs.RealSpecBeltWeld
import all QsagVerified.Proofs.RealSpecBeltWeld
public import QsagVerified.Proofs.RealSpecKeccakWeld
import all QsagVerified.Proofs.RealSpecKeccakWeld

/-!
# Cross-package weld library and its axiom census

Root of the `QsagSpecWeld` library: the modules that import both the Aeneas extraction and the
`Qsag` specifications. Building it also runs the same axiom policy as `AuditMirAxioms`
(`propext` and `Quot.sound` only) over every declaration those modules own, with a negative
control.
-/

open Lean Elab Command in
run_cmd do
  let negative ← Lean.collectAxioms ``Classical.choice
  if (negative.filter fun ax => ax != ``propext && ax != ``Quot.sound).isEmpty then
    throwError "spec weld axiom audit negative control unexpectedly passed"
  let env ← getEnv
  let mut checked : Nat := 0
  let mut rejected : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let owner := env.header.moduleNames[idx.toNat]!.toString
      if owner.startsWith "QsagVerified.Proofs.RealSpec" ||
          owner == "QsagVerified.Proofs.AuthenticatedBeltAndRealSpecWeld" then
        checked := checked + 1
        let axioms ← Lean.collectAxioms name
        let forbidden := axioms.filter fun ax => ax != ``propext && ax != ``Quot.sound
        if !forbidden.isEmpty then
          rejected := rejected + 1
          logInfo m!"REJECT {name} (module {owner}): {forbidden}"
  if checked == 0 then
    throwError "spec weld axiom audit has empty coverage"
  if rejected > 0 then
    throwError "spec weld axiom policy failed: {rejected} of {checked} declarations rejected"
  logInfo m!"spec weld axiom audit: {checked} declarations; zero rejected (allowlist: propext, Quot.sound)"
