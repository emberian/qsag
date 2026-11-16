module
import all QsagVerified.Funs
import Lean
public import QsagVerified.Proofs.RealSpecGuardBoundary
import all QsagVerified.Proofs.RealSpecGuardBoundary
public import QsagVerified.Proofs.AuthenticatedBeltAndRealSpecWeld
import all QsagVerified.Proofs.AuthenticatedBeltAndRealSpecWeld
public import QsagVerified.Proofs.RealSpecBeltWeld
import all QsagVerified.Proofs.RealSpecBeltWeld
public import QsagVerified.Proofs.CustodyMediation
import all QsagVerified.Proofs.CustodyMediation
public import QsagVerified.Proofs.ElfMirTriangles
import Qsag.Tactic.AssuranceKit

/-!
# Protocol-level weld library and its axiom census

Root of the `QsagCustodyWeld` library: the welds whose statements mention the protocol
specifications `Qsag.MirSpecBridge` and `Qsag.JortsBeltLatchAndQuorumSwitching`: lockstep forward
simulations of the extracted RSS cut session, velocity guard, ML-DSA release gate and belt-latch
kernel into their `Qsag` machines, the witness that the velocity guard is not the burned-nonce policy model, belt
grants as custodian masks, and the mediation statements of the two production opening rounds
(`CustodyMediation`).
It builds exactly when those `Qsag` modules and their imports do; the primitive welds in
`QsagSpecWeld` do not depend on it.

Building this root runs the same axiom policy (`propext` and `Quot.sound` only) over every
declaration these modules own, with a negative control, and checks that the belt and RSS weld
theorems are present as theorems and the four guard simulations are typed `ForwardSim` values.
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
  velocityGuardAbs
  velocityReqAbs
  velocity_extracted_step_refines
  extractedVelocityMachine
  extractedVelocity_forwardSim_mirVelocity
  extractedVelocity_multiTurn_cap_and_monotonic_nonce
  tooth_extractedVelocity_replayed_nonce_never_approved
  mlDsaGateAbs
  mlDsaChecksAbs
  mlDsa_extracted_step_refines
  extractedMlDsaMachine
  extractedMlDsa_forwardSim_mirMlDsa
  extractedMlDsa_at_most_one_release
  tooth_extractedMlDsa_failed_barrier_never_released
  beltKernelAbs
  beltReqAbs
  beltLatch_extracted_step_refines
  extractedBeltLatchMachine
  extractedBeltLatch_forwardSim_mirBeltLatchKernel
  extractedBeltLatch_equivocation_free
  tooth_extractedBeltLatch_poisoned_accepts_nothing
  sigma_release_iff
  sigma_release_permit
  plane_open_release_iff
  tooth_opening_wrong_context_refused
  tooth_sigma_nonzero_lane_refused
)
end QsagMirProofs

-- Ordinary imports use the owning-module theorem certificates and transitive
-- kernel axiom inventories; no private-body import is needed for these anchors.
#verify_constructive qsag_verified.proofs.elf_mir_goldilocks_add_x86_64
#verify_constructive qsag_verified.proofs.elf_mir_goldilocks_sub_x86_64
#verify_constructive qsag_verified.proofs.elf_mir_goldilocks_mul_x86_64
#verify_constructive qsag_verified.proofs.elf_mir_goldilocks_mul_aarch64
#verify_constructive qsag_verified.proofs.elf_mir_keccak_f1600_avx2_4x
#verify_constructive qsag_verified.proofs.elf_mir_gf256_gfni
#verify_constructive qsag_verified.proofs.elf_mir_tower128_pclmul

open Lean Elab Command in
run_cmd do
  let negative ← Lean.collectAxioms ``Classical.choice
  if (negative.filter fun ax => ax != ``propext && ax != ``Quot.sound).isEmpty then
    throwError "custody weld axiom audit negative control unexpectedly passed"
  let env := (← getEnv).setExporting false
  let requiredModules := [
    "QsagVerified.Proofs.RealSpecBeltWeld",
    "QsagVerified.Proofs.RealSpecGuardBoundary",
    "QsagVerified.Proofs.AuthenticatedBeltAndRealSpecWeld",
    "QsagVerified.Proofs.CustodyMediation",
    "QsagVerified.Proofs.ElfMirTriangles"]
  let requiredTheorems : List Name := [
    ``qsag_verified.proofs.belt_grant_refines_qsag_mask,
    ``qsag_verified.proofs.belt_quorum_intersection_refines_qsag,
    ``qsag_verified.proofs.belt_validated_grant_refines_qsag_mask,
    ``qsag_verified.proofs.extractedRssCut_inherits_spec_trace_safety,
    ``qsag_verified.proofs.tooth_velocity_used_nonce_model_is_not_monotone_nonce,
    ``qsag_verified.proofs.velocity_extracted_step_refines,
    ``qsag_verified.proofs.extractedVelocity_multiTurn_cap_and_monotonic_nonce,
    ``qsag_verified.proofs.mlDsa_extracted_step_refines,
    ``qsag_verified.proofs.extractedMlDsa_at_most_one_release,
    ``qsag_verified.proofs.beltLatch_extracted_step_refines,
    ``qsag_verified.proofs.extractedBeltLatch_equivocation_free,
    ``qsag_verified.proofs.sigma_release_iff,
    ``qsag_verified.proofs.plane_open_release_iff,
    ``qsag_verified.proofs.tooth_opening_wrong_context_refused]
  for name in requiredTheorems do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "custody weld axiom audit missing theorem target: {name}"
  let simulationNames : List Name := [
    ``qsag_verified.proofs.extractedRssCut_forwardSim_mirRssCut,
    ``qsag_verified.proofs.extractedVelocity_forwardSim_mirVelocity,
    ``qsag_verified.proofs.extractedMlDsa_forwardSim_mirMlDsa,
    ``qsag_verified.proofs.extractedBeltLatch_forwardSim_mirBeltLatchKernel]
  for simulationName in simulationNames do
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
