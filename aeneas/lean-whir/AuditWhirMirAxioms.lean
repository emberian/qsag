module
import Lean
import all Lean.Util.CollectAxioms
import all QsagWhirVerified
import all QsagWhirSpecWeld
import all QsagWhirVerified.Canonical
import all QsagWhirVerified.ProtocolWeld
import all QsagWhirVerified.Proofs
import all QsagWhirVerified.Arithmetic
import all QsagWhirVerified.Funs
import all QsagWhirVerified.Types
import all Aeneas
import all Aeneas.Elab.Attrs
import all Aeneas.Std.Containers
import all Aeneas.Std.Types

open Lean

private def requiredWhirMirTheorems : Array Name := #[
  ``qsag_whir_verified.proofs.goldilocks_p_val,
  ``qsag_whir_verified.proofs.max_u64_word_val,
  ``qsag_whir_verified.proofs.fp5_nonresidue_w_val,
  ``qsag_whir_verified.proofs.frobenius_zeta5_1_val,
  ``qsag_whir_verified.proofs.frobenius_zeta5_2_val,
  ``qsag_whir_verified.proofs.frobenius_zeta5_3_val,
  ``qsag_whir_verified.proofs.frobenius_zeta5_4_val,
  ``qsag_whir_verified.proofs.qsaghqm2_profile_turbo400_val,
  ``qsag_whir_verified.proofs.qsaghqm2_profile_gl24_val,
  ``qsag_whir_verified.proofs.min_quintic_log_cells_val,
  ``qsag_whir_verified.proofs.max_quintic_log_cells_val,
  ``qsag_whir_verified.proofs.max_canopy_log_leaves_val,
  ``qsag_whir_verified.proofs.copy_fp5_spec,
  ``qsag_whir_verified.proofs.zeta5_powers_spec,
  ``qsag_whir_verified.proofs.add_refines,
  ``qsag_whir_verified.proofs.sub_refines,
  ``qsag_whir_verified.proofs.mul_refines,
  ``qsag_whir_verified.proofs.fp5_zero_refines,
  ``qsag_whir_verified.proofs.fp5_one_refines,
  ``qsag_whir_verified.proofs.fp5_from_base_refines,
  ``qsag_whir_verified.proofs.fp5_add_refines,
  ``qsag_whir_verified.proofs.fp5_sub_refines,
  ``qsag_whir_verified.proofs.fp5_neg_refines,
  ``qsag_whir_verified.proofs.fp5_scale_refines,
  ``qsag_whir_verified.proofs.fp5_mul_refines,
  ``qsag_whir_verified.proofs.fp5_frobenius_refines,
  ``qsag_whir_verified.proofs.fp5Frob_pow5_id,
  ``qsag_whir_verified.proofs.affine_combine_fp5_refines,
  ``qsag_whir_verified.proofs.fp5X_pow5_eq_three,
  ``qsag_whir_verified.proofs.duet_fold_fp5_refines,
  ``qsag_whir_verified.proofs.duet_fold_fp5_algebraic_sound,
  ``qsag_whir_verified.proofs.cwyz_duet_fold_fp5_refines,
  ``qsag_whir_verified.proofs.cwyz_duet_fold_fp5_algebraic_sound,
  ``qsag_whir_verified.proofs.cwyz_bridge_claim_step_fp5_refines,
  ``qsag_whir_verified.proofs.cwyz_bridge_claim_step_fp5_dual_sound,
  ``qsag_whir_verified.proofs.eval_quadratic_sumcheck_wire_fp5_refines,
  ``qsag_whir_verified.proofs.eval_quadratic_sumcheck_wire_fp5_hypercube_sum,
  ``qsag_whir_verified.proofs.hornerSpec_eq_evalPolyAscending,
  ``qsag_whir_verified.proofs.load_le_u64_40_spec,
  ``qsag_whir_verified.proofs.load_le_u64_56_spec,
  ``qsag_whir_verified.proofs.decode_canonical_u64_spec,
  ``qsag_whir_verified.proofs.decode_canonical_u64_some_iff,
  ``qsag_whir_verified.proofs.decode_canonical_u64_none_iff,
  ``qsag_whir_verified.proofs.decode_canonical_u64_rejects_noncanonical,
  ``qsag_whir_verified.proofs.decode_canonical_fp5_limbs_spec,
  ``qsag_whir_verified.proofs.decode_canonical_fp5_limbs_some_iff,
  ``qsag_whir_verified.proofs.decode_canonical_fp5_limbs_none_iff,
  ``qsag_whir_verified.proofs.decode_canonical_fp5_spec,
  ``qsag_whir_verified.proofs.decode_canonical_fp5_some_iff,
  ``qsag_whir_verified.proofs.decode_canonical_fp5_none_iff,
  ``qsag_whir_verified.proofs.decode_canonical_gl24_limbs_spec,
  ``qsag_whir_verified.proofs.decode_canonical_gl24_limbs_some_iff,
  ``qsag_whir_verified.proofs.decode_canonical_gl24_limbs_none_iff,
  ``qsag_whir_verified.proofs.decode_canonical_gl24_digest_spec,
  ``qsag_whir_verified.proofs.decode_canonical_gl24_digest_some_iff,
  ``qsag_whir_verified.proofs.decode_canonical_gl24_digest_none_iff,
  ``qsag_whir_verified.proofs.fp5_eq_spec,
  ``qsag_whir_verified.proofs.fp5_eq_sound,
  ``qsag_whir_verified.proofs.verify_ood_pin_eq_fp5_spec,
  ``qsag_whir_verified.proofs.verify_ood_pin_eq_fp5_sound,
  ``qsag_whir_verified.proofs.verify_ood_pin_eq_fp5_false_iff,
  ``qsag_whir_verified.proofs.duet_fold_fp5_coset_sound,
  ``qsag_whir_verified.proofs.verify_affine_duet_fold_step_fp5_spec,
  ``qsag_whir_verified.proofs.verify_affine_duet_fold_step_fp5_sound,
  ``qsag_whir_verified.proofs.verify_affine_duet_fold_step_fp5_coset_sound,
  ``qsag_whir_verified.proofs.cwyz_duet_fold_fp5_coset_sound,
  ``qsag_whir_verified.proofs.verify_cwyz_duet_fold_step_fp5_spec,
  ``qsag_whir_verified.proofs.verify_cwyz_duet_fold_step_fp5_sound,
  ``qsag_whir_verified.proofs.verify_cwyz_duet_fold_step_fp5_coset_sound,
  ``qsag_whir_verified.proofs.cwyz_bridge_claim_step_fp5_dual_spec,
  ``qsag_whir_verified.proofs.verify_cwyz_bridge_claim_step_fp5_spec,
  ``qsag_whir_verified.proofs.verify_cwyz_bridge_claim_step_fp5_sound,
  ``qsag_whir_verified.proofs.verify_cwyz_bridge_claim_step_fp5_dual_sound,
  ``qsag_whir_verified.proofs.eval_quadratic_sumcheck_wire_fp5_hypercube_spec,
  ``qsag_whir_verified.proofs.eval_fp5_univariate_at_base_spec,
  ``qsag_whir_verified.proofs.eval_fp5_univariate_at_base_ascending_sound,
  ``qsag_whir_verified.proofs.verify_fp5_univariate_at_base_pin_spec,
  ``qsag_whir_verified.proofs.verify_fp5_univariate_at_base_pin_sound,
  ``qsag_whir_verified.proofs.verify_fp5_univariate_at_base_pin_ascending_sound,
  ``qsag_whir_verified.proofs.canonical_query_group_idx_spec,
  ``qsag_whir_verified.proofs.canonical_query_group_idx_some_iff,
  ``qsag_whir_verified.proofs.canonical_query_group_idx_none_iff,
  ``qsag_whir_verified.proofs.canonical_query_group_idx_lt_groups,
  ``qsag_whir_verified.proofs.step_merkle_pair_order_400_spec,
  ``qsag_whir_verified.proofs.step_merkle_pair_order_400_some_iff,
  ``qsag_whir_verified.proofs.step_merkle_pair_order_400_none_iff,
  ``qsag_whir_verified.proofs.step_merkle_pair_order_gl24_spec,
  ``qsag_whir_verified.proofs.step_merkle_pair_order_gl24_some_iff,
  ``qsag_whir_verified.proofs.step_merkle_pair_order_gl24_none_iff,
  ``qsag_whir_verified.proofs.checked_quorum_sum_total,
  ``qsag_whir_verified.proofs.checked_quorum_sum_sound,
  ``qsag_whir_verified.proofs.checked_quorum_sum_none_iff,
  ``qsag_whir_verified.proofs.checked_quorum_sum_le_max_u64_word,
  ``qsag_whir_verified.proofs.verify_qsaghqm2_header_spec,
  ``qsag_whir_verified.proofs.verify_qsaghqm2_header_some_iff,
  ``qsag_whir_verified.proofs.verify_qsaghqm2_header_none_iff,
  ``qsag_whir_verified.proofs.verify_quintic_schedule_envelope_spec,
  ``qsag_whir_verified.proofs.verify_quintic_schedule_envelope_sound,
  ``qsag_whir_verified.proofs.verify_quintic_schedule_envelope_le_max_canopy,
  ``qsag_whir_verified.proofs.fieldAbs_add,
  ``qsag_whir_verified.proofs.fieldAbs_mul,
  ``qsag_whir_verified.proofs.fieldAbs_sub,
  ``qsag_whir_verified.proofs.fp5Abs_add,
  ``qsag_whir_verified.proofs.fp5Abs_sub,
  ``qsag_whir_verified.proofs.fp5Abs_mul,
  ``qsag_whir_verified.proofs.fp5Abs_frob,
  ``qsag_whir_verified.proofs.fp5Abs_canonicalFp5,
  ``qsag_whir_verified.proofs.gl24Abs_canonicalGl24,
  ``qsag_whir_verified.proofs.fp5_mul_fp5Inv_ok_one,
  ``qsag_whir_verified.proofs.canonicalFieldWord_two_inv,
  ``qsag_whir_verified.proofs.canonicalFieldWord_two_x_inv,
  ``qsag_whir_verified.proofs.load_le_u64_40_refines_qsag,
  ``qsag_whir_verified.proofs.load_le_u64_56_refines_qsag,
  ``qsag_whir_verified.proofs.decode_canonical_u64_refines_qsag,
  ``qsag_whir_verified.proofs.decode_canonical_fp5_limbs_refines_qsag,
  ``qsag_whir_verified.proofs.decode_canonical_fp5_refines_qsag,
  ``qsag_whir_verified.proofs.decode_canonical_gl24_limbs_refines_qsag,
  ``qsag_whir_verified.proofs.decode_canonical_gl24_digest_refines_qsag,
  ``qsag_whir_verified.proofs.ofBase_inv,
  ``qsag_whir_verified.proofs.duet_fold_fp5_refines_qsag,
  ``qsag_whir_verified.proofs.cwyz_duet_fold_fp5_refines_hemVirtualFoldOracle,
  ``qsag_whir_verified.proofs.verify_cwyz_duet_fold_step_fp5_sound_qsag,
  ``qsag_whir_verified.proofs.verify_affine_duet_fold_step_fp5_sound_qsag,
  ``qsag_whir_verified.proofs.verify_affine_duet_fold_step_fp5_roots_le_one,
  ``qsag_whir_verified.proofs.cwyz_bridge_claim_step_fp5_refines_hemBridgeFoldClaim,
  ``qsag_whir_verified.proofs.verify_cwyz_bridge_claim_step_fp5_sound_qsag,
  ``qsag_whir_verified.proofs.eval_quadratic_sumcheck_wire_fp5_refines_qsag,
  ``qsag_whir_verified.proofs.eval_quadratic_sumcheck_wire_fp5_bad_challenges_le_two,
  ``qsag_whir_verified.proofs.eval_fp5_univariate_at_base_refines_evalCoeffs,
  ``qsag_whir_verified.proofs.verify_fp5_univariate_at_base_pin_sound_qsag,
  ``qsag_whir_verified.proofs.verify_fp5_univariate_at_base_pin_roots_le_degree,
  ``qsag_whir_verified.proofs.verify_ood_pin_eq_fp5_canonical_iff_qsag,
  ``qsag_whir_verified.proofs.step_merkle_pair_order_400_canonical_parity,
  ``qsag_whir_verified.proofs.step_merkle_pair_order_gl24_refines_poseidon2Gl24,
  ``qsag_whir_verified.proofs.checked_quorum_sum_sound_qsag,
  ``qsag_whir_verified.proofs.checked_quorum_sum_wp_u64NatRefines,
  ``qsag_whir_verified.proofs.goldilocks_p_eq_qsag_prime,
  ``qsag_whir_verified.proofs.max_u64_word_lt_two_pow_64_qsag,
  ``qsag_whir_verified.proofs.fp5_nonresidue_w_eq_qsag,
  ``qsag_whir_verified.proofs.frobenius_zeta5_constants_eq_qsag,
  ``qsag_whir_verified.proofs.copy_fp5_refines_qsag,
  ``qsag_whir_verified.proofs.add_refines_qsag,
  ``qsag_whir_verified.proofs.sub_refines_qsag,
  ``qsag_whir_verified.proofs.mul_refines_qsag,
  ``qsag_whir_verified.proofs.fp5_zero_refines_qsag,
  ``qsag_whir_verified.proofs.fp5_one_refines_qsag,
  ``qsag_whir_verified.proofs.fp5_from_base_refines_qsag,
  ``qsag_whir_verified.proofs.fp5_eq_iff_qsag,
  ``qsag_whir_verified.proofs.fp5_add_refines_qsag,
  ``qsag_whir_verified.proofs.fp5_sub_refines_qsag,
  ``qsag_whir_verified.proofs.fp5_neg_refines_qsag,
  ``qsag_whir_verified.proofs.fp5_scale_refines_qsag,
  ``qsag_whir_verified.proofs.fp5_mul_refines_qsag,
  ``qsag_whir_verified.proofs.fp5_frobenius_refines_qsag,
  ``qsag_whir_verified.proofs.canonical_query_group_idx_refines_qsag,
  ``qsag_whir_verified.proofs.duet_fold_fp5_antipodal_fiberPoint_qsag,
  ``qsag_whir_verified.proofs.affine_combine_fp5_refines_zkHemV2_maskLine,
  ``qsag_whir_verified.proofs.mir_affine_combine_fp5_coin_bijection_simulated,
  ``qsag_whir_verified.proofs.mirVerifyShiftSumcheckChainFp5_iff_qsag,
  ``qsag_whir_verified.proofs.verify_qsaghqm2_header_refines_qsag,
  ``qsag_whir_verified.proofs.verify_quintic_schedule_envelope_accepts_zkHemV2ProdStages,
  ``qsag_whir_verified.proofs.mirStageGatesFp5_sound_for_verifyHemAffineWhir,
  ``qsag_whir_verified.proofs.tooth_unchecked_mod_p_accepts_aliased_field_limb,
  ``qsag_whir_verified.proofs.tooth_decode_canonical_fp5_rejects_fifth_limb_alias,
  ``qsag_whir_verified.proofs.tooth_decode_canonical_gl24_rejects_seventh_limb_alias,
  ``qsag_whir_verified.proofs.tooth_merkle_400_and_gl24_swap_and_reject,
  ``qsag_whir_verified.proofs.tooth_checked_quorum_sum_rejects_u64_wraparound_forgery,
  ``qsag_whir_verified.proofs.tooth_ood_pin_fp5_rejects_perturbation,
  ``qsag_whir_verified.proofs.tooth_coset_inverse_premises_inhabited_and_fp5_fold_rejects_perturbation,
  ``qsag_whir_verified.proofs.tooth_cwyz_bridge_fp5_accepts_dual_and_rejects_perturbation,
  ``qsag_whir_verified.proofs.tooth_horner_fp5_accepts_ascending_and_rejects_perturbation,
  ``qsag_whir_verified.proofs.tooth_qsaghqm2_header_and_schedule_reject_tamper,
  ``qsag_whir_verified.proofs.tooth_canonical_cwyz_fp5_fold_rejects_wrong_twiddle_and_forged_claim
]

/-! ## Symbol coverage -/

private def funsModule : Name := `QsagWhirVerified.Funs

private def isToothTheorem (thm : Name) : Bool :=
  match thm with
  | .str _ s => s.startsWith "tooth_"
  | _ => false

private def extractedSymbols (env : Environment) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if env.header.moduleNames[idx.toNat]! == funsModule && !name.isInternalDetail then
        if let .defnInfo _ := info then out := out.push name
  return out.qsort fun a b => a.toString < b.toString

private def definitionUses (env : Environment) (name used : Name) : Bool :=
  match env.find? name with
  | some (.defnInfo d) => d.value.getUsedConstants.contains used
  | _ => false

private def loopOrigin? (name : Name) : Option (Name × Name) :=
  let loopName := match name with
    | .str pre "body" => pre
    | other => other
  match loopName with
  | .str pre s =>
    if s.endsWith "_loop" && s.length > 5 then
      some (.str pre (String.ofList (s.toList.take (s.length - 5))), loopName)
    else none
  | _ => none

private def symbolCoverage (env : Environment) (theorems : Array Name) :
    Array Name × Array Name := Id.run do
  let symbols := extractedSymbols env
  let mut mentioned : NameSet := {}
  for thm in theorems do
    if !isToothTheorem thm then
      if let some (.thmInfo info) := env.find? thm then
        for used in info.type.getUsedConstants do
          mentioned := mentioned.insert used
  let mut gaps : Array Name := #[]
  for symbol in symbols do
    let covered :=
      match loopOrigin? symbol with
      | some (origin, loopName) =>
        symbols.contains origin && mentioned.contains origin &&
          definitionUses env origin loopName &&
          (symbol == loopName || definitionUses env loopName symbol)
      | none => mentioned.contains symbol
    if !covered then gaps := gaps.push symbol
  return (symbols, gaps)

private def symbolCoverageControlsFail (env : Environment) (theorems : Array Name) : Bool :=
  let (symbols, allGaps) := symbolCoverage env #[]
  let (_, toothOnlyGaps) := symbolCoverage env (theorems.filter isToothTheorem)
  let target := `qsag_whir_verified.checked_quorum_sum
  let withoutTarget := theorems.filter fun thm =>
    match env.find? thm with
    | some (.thmInfo info) => !info.type.getUsedConstants.contains target
    | _ => true
  let (_, targetGaps) := symbolCoverage env withoutTarget
  symbols.isEmpty || allGaps.size != symbols.size || toothOnlyGaps.size != symbols.size ||
    !(targetGaps.contains target &&
      targetGaps.contains `qsag_whir_verified.checked_quorum_sum_loop &&
      targetGaps.contains `qsag_whir_verified.checked_quorum_sum_loop.body)

open Lean Elab Command in
run_cmd do
  let negative ← Lean.collectAxioms ``Classical.choice
  if (negative.filter fun ax => ax != ``propext && ax != ``Quot.sound).isEmpty then
    throwError "WHIR MIR axiom audit negative control unexpectedly passed"
  let env := (← getEnv).setExporting false
  for req in requiredWhirMirTheorems do
    match env.find? req with
    | some (.thmInfo _) =>
      let deps ← withEnv env <| Lean.collectAxioms req
      let rejected := deps.filter fun n => n != ``propext && n != ``Quot.sound
      if !rejected.isEmpty then
        throwError "Required WHIR theorem {req} depends on rejected axioms: {rejected}"
    | _ =>
      throwError "Required WHIR theorem missing or not a theorem: {req}"
  let (symbols, gaps) := symbolCoverage env requiredWhirMirTheorems
  if symbolCoverageControlsFail env requiredWhirMirTheorems then
    throwError "WHIR symbol coverage negative control unexpectedly passed"
  if !gaps.isEmpty then
    throwError "Extracted WHIR symbols without an anchored theorem statement: {gaps}"
  logInfo m!"WHIR symbol coverage: {symbols.size} extracted symbols, zero without an anchored theorem statement"
  let mut checked : Nat := 0
  let mut rejectedCount : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let owner := env.header.moduleNames[idx.toNat]!.toString
      if (owner == "QsagWhirSpecWeld" || owner == "QsagWhirVerified" || owner.startsWith "QsagWhirVerified." ||
          owner == "Aeneas" || owner.startsWith "Aeneas.") &&
          !(owner == "Aeneas.Elab.Attrs" && isMarkedMeta env name) then
        checked := checked + 1
        let deps ← withEnv env <| Lean.collectAxioms name
        let rejected := deps.filter fun n => n != ``propext && n != ``Quot.sound
        if !rejected.isEmpty then
          rejectedCount := rejectedCount + 1
          logInfo m!"REJECT {name} (module {owner}): {rejected}"
  if checked == 0 then
    throwError "Empty WHIR MIR audit coverage"
  if rejectedCount > 0 then
    throwError "WHIR MIR axiom policy failed: {rejectedCount} of {checked} declarations rejected"
  logInfo m!"WHIR MIR audit: {checked} declarations across QsagWhirVerified + Aeneas ({requiredWhirMirTheorems.size} anchored theorems), zero rejected (allowlist: propext, Quot.sound)"

