module
import Lean
import all QsagVerified.Proofs.AuthenticatedBeltAndRealSpecWeld
import all QsagMirProofs
import all QsagVerified.Funs
import all QsagVerified.Proofs
import all QsagVerified.Proofs.Adrs
import all QsagVerified.Proofs.AdrsConverse
import all QsagVerified.Proofs.Bdoz
import all QsagVerified.Proofs.Common
import all QsagVerified.Proofs.CredAndHdGuards
import all QsagVerified.Proofs.Epoch
import all QsagVerified.Proofs.FtsSpnGuard
import all QsagVerified.Proofs.Gf256
import all QsagVerified.Proofs.Goldilocks
import all QsagVerified.Proofs.Hash
import all QsagVerified.Proofs.HashEpoch
import all QsagVerified.Proofs.KeccakWitness
import all QsagVerified.Proofs.KeccakWitness.Group0
import all QsagVerified.Proofs.KeccakWitness.Group1
import all QsagVerified.Proofs.KeccakWitness.Group2
import all QsagVerified.Proofs.KeccakWitness.Group3
import all QsagVerified.Proofs.KeccakWitness.Group4
import all QsagVerified.Proofs.KeccakWitness.Group5
import all QsagVerified.Proofs.KeccakWitness.Group6
import all QsagVerified.Proofs.KeccakWitness.Group7
import all QsagVerified.Proofs.KeccakWitness.States
import all QsagVerified.Proofs.MirRefinementKit
import all QsagVerified.Proofs.PantsAndQuorumGuards
import all QsagVerified.Proofs.PolicyAndAddr
import all QsagVerified.Proofs.RssCutSession
import all QsagVerified.Proofs.ShamirDkg
import all QsagVerified.Proofs.Sponge
import all QsagVerified.Proofs.TowerBdoz
import all QsagVerified.Proofs.Tsw
import all QsagVerified.Proofs.Wots
import all QsagVerified.Types

import all QsagVerified.Proofs.BeltAckProvenance
import all QsagVerified.Proofs.CallerContracts
import all QsagVerified.Proofs.MultiTurnMediationAndReachability
import all QsagVerified.Proofs.RealSpecBeltWeld
import all QsagVerified.Proofs.RealSpecFieldWeld
import all QsagVerified.Proofs.RealSpecHashWeld
import all QsagVerified.Proofs.RealSpecKeccakWeld
import all QsagVerified.Proofs.RealSpecTowerWeld
import all QsagSpecWeld

open Lean Elab Command in
run_cmd do
  let negative ← Lean.collectAxioms ``Classical.choice
  if (negative.filter fun ax => ax != ``propext && ax != ``Quot.sound).isEmpty then
    throwError "MIR axiom audit negative control unexpectedly passed"
  let env ← getEnv
  let mut checked : Nat := 0
  let mut rejected : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let owner := env.header.moduleNames[idx.toNat]!.toString
      if owner == "QsagSpecWeld" || owner == "QsagMirProofs" || owner == "QsagVerified" ||
          owner.startsWith "QsagVerified." then
        checked := checked + 1
        let axioms ← Lean.collectAxioms name
        let forbidden := axioms.filter fun ax => ax != ``propext && ax != ``Quot.sound
        if !forbidden.isEmpty then
          rejected := rejected + 1
          logInfo m!"REJECT {name} (module {owner}): {forbidden}"
  if checked == 0 then
    throwError "MIR axiom audit has empty coverage"
  if rejected > 0 then
    throwError "MIR axiom policy failed: {rejected} of {checked} declarations rejected"
  logInfo m!"MIR axiom audit: {checked} declarations; zero rejected (allowlist: propext, Quot.sound)"
