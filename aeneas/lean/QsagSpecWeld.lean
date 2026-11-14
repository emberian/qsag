module
import Lean
public import QsagVerified.Proofs.RealSpecGuardBoundary
import all QsagVerified.Proofs.RealSpecGuardBoundary
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
control. The census measures axiom dependencies, not production linkage or completeness.

Current mathematical boundaries:
* Goldilocks: add/sub/mul and canonical inversion, including exact nonzero MIR cancellation.
* Binary towers: GF(256) multiplication; GF(256), Tower128, Tower256 addition.
* Hash signatures: WOTS+C digit acceptance/rejection, not hash-chain verification.
* Keccak: arbitrary-state 24-round permutation and streaming phase laws, not multi-block XOF.
* Belt: validated local guard grants and authenticated mask provenance, not production IO.

Outstanding targets: canonical wider-tower multiplication, KoalaBear extraction, streaming
absorb/pad/squeeze byte equivalence, production arithmetic linkage, and production BeltLatch
persistence/recovery/echo refinement. These require additional proofs and, for missing
production entry points, changes to Rust/extraction outside these weld modules.
-/

open Lean Elab Command in
run_cmd do
  let negative ← Lean.collectAxioms ``Classical.choice
  if (negative.filter fun ax => ax != ``propext && ax != ``Quot.sound).isEmpty then
    throwError "spec weld axiom audit negative control unexpectedly passed"
  let env ← getEnv
  let requiredModules := [
    "QsagVerified.Proofs.RealSpecFieldWeld",
    "QsagVerified.Proofs.RealSpecTowerWeld",
    "QsagVerified.Proofs.RealSpecHashWeld",
    "QsagVerified.Proofs.RealSpecKeccakWeld",
    "QsagVerified.Proofs.RealSpecBeltWeld",
    "QsagVerified.Proofs.RealSpecGuardBoundary",
    "QsagVerified.Proofs.AuthenticatedBeltAndRealSpecWeld"]
  let mut coveredModules : List String := []
  let mut checked : Nat := 0
  let mut rejected : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let owner := env.header.moduleNames[idx.toNat]!.toString
      if owner.startsWith "QsagVerified.Proofs.RealSpec" ||
          owner == "QsagVerified.Proofs.AuthenticatedBeltAndRealSpecWeld" then
        if !coveredModules.contains owner then
          coveredModules := owner :: coveredModules
        checked := checked + 1
        let axioms ← Lean.collectAxioms name
        let forbidden := axioms.filter fun ax => ax != ``propext && ax != ``Quot.sound
        if !forbidden.isEmpty then
          rejected := rejected + 1
          logInfo m!"REJECT {name} (module {owner}): {forbidden}"
  for owner in requiredModules do
    if !coveredModules.contains owner then
      throwError "spec weld axiom audit missing module: {owner}"
  if checked == 0 then
    throwError "spec weld axiom audit has empty coverage"
  if rejected > 0 then
    throwError "spec weld axiom policy failed: {rejected} of {checked} declarations rejected"
  logInfo m!"spec weld axiom audit: {checked} declarations; zero rejected (allowlist: propext, Quot.sound)"
