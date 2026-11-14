module
import Lean
public import QsagVerified.Proofs.RealSpecFieldWeld
import all QsagVerified.Proofs.RealSpecFieldWeld
public import QsagVerified.Proofs.RealSpecHashWeld
import all QsagVerified.Proofs.RealSpecHashWeld
public import QsagVerified.Proofs.RealSpecTowerWeld
import all QsagVerified.Proofs.RealSpecTowerWeld
public import QsagVerified.Proofs.RealSpecKeccakWeld
import all QsagVerified.Proofs.RealSpecKeccakWeld

/-!
# Primitive weld library and its axiom census

Root of the `QsagSpecWeld` library: the modules that weld extracted primitives to the `Qsag`
specifications of the same primitives. Its `Qsag` imports are the primitive specifications only
(`Goldilocks`, `SimulationSpine`, `BinaryTower`, `HashSigs`, `Keccak` and what those import), so
it builds independently of the protocol-level `Qsag` modules. The welds whose statements mention
protocol specifications (`MirSpecBridge`, `JortsBeltLatchAndQuorumSwitching`) are the separate
`QsagCustodyWeld` library.

Building this root runs the axiom policy of `AuditMirAxioms` (`propext` and `Quot.sound` only)
over every declaration those modules own, with a negative control. The census measures axiom
dependencies, not production linkage.

Mathematical content:
* Goldilocks: add/sub/mul and canonical inversion, including exact nonzero MIR cancellation.
* Binary towers: addition and multiplication at GF(256), Tower128 and Tower256 against the
  canonical recursive field, and absence of zero divisors for the extracted Tower128 product.
* Hash signatures: WOTS+C digit acceptance/rejection, not hash-chain verification.
* Keccak: arbitrary-state 24-round permutation and streaming phase laws.
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
    "QsagVerified.Proofs.RealSpecKeccakWeld"]
  let mut coveredModules : List String := []
  let mut checked : Nat := 0
  let mut rejected : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let owner := env.header.moduleNames[idx.toNat]!.toString
      if requiredModules.contains owner then
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
