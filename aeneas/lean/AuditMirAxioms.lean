module
import Lean
import all QsagMirProofs
import all QsagVerified.Funs
import all QsagVerified.Proofs
import all QsagVerified.Proofs.Adrs
import all QsagVerified.Proofs.AdrsConverse
import all QsagVerified.Proofs.Bdoz
import all QsagVerified.Proofs.BdozConsumption
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
import all QsagVerified.Proofs.SpongeConformance
import all QsagVerified.Proofs.TowerBdoz
import all QsagVerified.Proofs.Tsw
import all QsagVerified.Proofs.Wots
import all QsagVerified.Types

import all QsagVerified.Proofs.BeltAckProvenance
import all QsagVerified.Proofs.BeltLatchKernel
import all QsagVerified.Proofs.CallerContracts
import all QsagVerified.Proofs.MultiTurnMediationAndReachability
import all QsagVerified.Proofs.RealSpecFieldWeld
import all QsagVerified.Proofs.RealSpecHashWeld
import all QsagVerified.Proofs.RealSpecKeccakWeld
import all QsagVerified.Proofs.RealSpecTowerWeld
import all QsagSpecWeld

/-!
This gate audits dependency closures of definitions AND theorems. Auditing an extracted
function is not a correctness proof for that function. The theorem anchors below prevent
core delivered weld boundaries from silently disappearing or becoming mere definitions.
The complete per-module census still includes every declaration, including future proofs.
The protocol-level welds (`RealSpecBeltWeld`, `RealSpecGuardBoundary`,
`AuthenticatedBeltAndRealSpecWeld`) are censused by `QsagCustodyWeld`, which shares this policy.
-/

open Lean Elab Command in
run_cmd do
  let negative ← Lean.collectAxioms ``Classical.choice
  if (negative.filter fun ax => ax != ``propext && ax != ``Quot.sound).isEmpty then
    throwError "MIR axiom audit negative control unexpectedly passed"
  let env ← getEnv
  let requiredTheorems : List Name := [
    ``qsag_verified.proofs.goldilocks_add_refines_qsag,
    ``qsag_verified.proofs.goldilocks_sub_refines_qsag,
    ``qsag_verified.proofs.goldilocks_mul_refines_qsag,
    ``qsag_verified.proofs.goldilocks_inv_or_zero_refines_qsag,
    ``qsag_verified.proofs.goldilocks_inverse_mul_eq_one,
    ``qsag_verified.proofs.goldilocks_inv_none_iff_zero,
    ``qsag_verified.proofs.goldilocks_inv_some_mul_eq_one,
    ``qsag_verified.proofs.gf256_mul_refines_qsag,
    ``qsag_verified.proofs.gf256_add_refines_qsag,
    ``qsag_verified.proofs.tower128_add_refines_qsag,
    ``qsag_verified.proofs.tower256_add_refines_qsag,
    ``qsag_verified.proofs.wotsc256_verify_refines_qsag,
    ``qsag_verified.proofs.wotsc256_accept_iff_qsag,
    ``qsag_verified.proofs.wotsc256_reject_iff_qsag,
    ``qsag_verified.proofs.keccak_f1600_array_refines_qsag,
    ``qsag_verified.proofs.keccak_f1600_result_iff,
    ``qsag_verified.proofs.shake256_absorb_after_squeezing,
    ``qsag_verified.proofs.shake256_finalize_after_squeezing,
    ``qsag_verified.proofs.tower128_mul_refines_qsag,
    ``qsag_verified.proofs.tower128_mul_eq_zero_iff,
    ``qsag_verified.proofs.tower256_mul_refines_qsag,
    ``qsag_verified.proofs.bdoz_verify_arbitrary_batch,
    ``qsag_verified.proofs.belt_latch_bind_eq,
    ``qsag_verified.proofs.belt_latch_epoch_binding_unique,
    ``qsag_verified.proofs.belt_latch_poison_absorbing,
    ``qsag_verified.proofs.belt_latch_recover_then_replay,
    ``qsag_verified.proofs.checked_velocity_spend_spec,
    ``qsag_verified.proofs.inhabited_belt_one_fault_multi_epoch]
  for name in requiredTheorems do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "MIR axiom audit missing theorem target: {name}"
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
