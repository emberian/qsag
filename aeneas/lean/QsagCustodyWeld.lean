module
import Lean
public import QsagVerified.Proofs.RealSpecGuardBoundary
import all QsagVerified.Proofs.RealSpecGuardBoundary
public import QsagVerified.Proofs.AuthenticatedBeltAndRealSpecWeld
import all QsagVerified.Proofs.AuthenticatedBeltAndRealSpecWeld
public import QsagVerified.Proofs.RealSpecBeltWeld
import all QsagVerified.Proofs.RealSpecBeltWeld

/-!
# Protocol-level weld library and its axiom census

Root of the `QsagCustodyWeld` library: the welds whose statements mention the protocol
specifications `Qsag.MirSpecBridge` and `Qsag.JortsBeltLatchAndQuorumSwitching` (RSS cut-session
forward simulation, the velocity-guard boundary witness, and belt grants as custodian masks).
It builds exactly when those `Qsag` modules and their imports do; the primitive welds in
`QsagSpecWeld` do not depend on it.

Building this root runs the same axiom policy (`propext` and `Quot.sound` only) over every
declaration these modules own, with a negative control, and checks that the belt and RSS weld
theorems are present as theorems and the RSS simulation is a typed `ForwardSim` value.
-/

namespace QsagMirProofs
export qsag_verified.proofs (
  beltMaskAbs
  beltMaskAbs_card
  beltMaskAbs_inter
  belt_grant_refines_qsag_mask
  belt_quorum_intersection_refines_qsag
  belt_validated_grant_refines_qsag_mask
  bytes32OfArray
  bytes32OfArray_injective
  rssCutPhaseAbs
  rssCutStateAbs
  rssCutInputAbs
  rssCutOutputAbs
  rssCutStateAbs_new_round1_committed
  rssCut_extracted_step_refines
  extractedRssCutMachine
  extractedRssCut_forwardSim_mirRssCut
  extractedRssCut_inherits_spec_trace_safety
  tooth_extractedRssCut_nonzero_residual_rejected
  tooth_velocity_used_nonce_model_is_not_monotone_nonce
)
end QsagMirProofs

open Lean Elab Command in
run_cmd do
  let negative ← Lean.collectAxioms ``Classical.choice
  if (negative.filter fun ax => ax != ``propext && ax != ``Quot.sound).isEmpty then
    throwError "custody weld axiom audit negative control unexpectedly passed"
  let env := (← getEnv).setExporting false
  let requiredModules := [
    "QsagVerified.Proofs.RealSpecBeltWeld",
    "QsagVerified.Proofs.RealSpecGuardBoundary",
    "QsagVerified.Proofs.AuthenticatedBeltAndRealSpecWeld"]
  let requiredTheorems : List Name := [
    ``qsag_verified.proofs.belt_grant_refines_qsag_mask,
    ``qsag_verified.proofs.belt_quorum_intersection_refines_qsag,
    ``qsag_verified.proofs.belt_validated_grant_refines_qsag_mask,
    ``qsag_verified.proofs.extractedRssCut_inherits_spec_trace_safety,
    ``qsag_verified.proofs.tooth_velocity_used_nonce_model_is_not_monotone_nonce]
  for name in requiredTheorems do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "custody weld axiom audit missing theorem target: {name}"
  let simulationName := ``qsag_verified.proofs.extractedRssCut_forwardSim_mirRssCut
  match env.find? simulationName with
  | some (.defnInfo info) =>
    unless info.type.getAppFn.constName? == some ``Qsag.ForwardSim do
      throwError "custody weld target is not a ForwardSim value: {simulationName}"
  | _ => throwError "custody weld axiom audit missing simulation definition: {simulationName}"
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
        let axioms ← withEnv env <| Lean.collectAxioms name
        let forbidden := axioms.filter fun ax => ax != ``propext && ax != ``Quot.sound
        if !forbidden.isEmpty then
          rejected := rejected + 1
          logInfo m!"REJECT {name} (module {owner}): {forbidden}"
  for owner in requiredModules do
    if !coveredModules.contains owner then
      throwError "custody weld axiom audit missing module: {owner}"
  if rejected > 0 then
    throwError "custody weld axiom policy failed: {rejected} of {checked} declarations rejected"
  logInfo m!"custody weld axiom audit: {checked} declarations; zero rejected (allowlist: propext, Quot.sound)"
