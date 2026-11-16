module
import Lean
import all Lean.Util.CollectAxioms
import all QsagWhirVerified
import all QsagWhirVerified.Canonical
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
  ``qsag_whir_verified.proofs.fieldAbs_add,
  ``qsag_whir_verified.proofs.ext4Abs_canonicalExt4,
  ``qsag_whir_verified.proofs.ext4Abs_inv,
  ``qsag_whir_verified.proofs.fieldAbs_one,
  ``qsag_whir_verified.proofs.ext4Abs_one,
  ``qsag_whir_verified.proofs.canonicalFieldWord_val,
  ``qsag_whir_verified.proofs.isCanonical_canonicalFieldWord,
  ``qsag_whir_verified.proofs.canonicalFieldWord_fieldAbs,
  ``qsag_whir_verified.proofs.fieldAbs_inj,
  ``qsag_whir_verified.proofs.isCanonicalExt4_canonicalExt4,
  ``qsag_whir_verified.proofs.canonicalExt4_ext4Abs,
  ``qsag_whir_verified.proofs.ext4Abs_inj,
  ``qsag_whir_verified.proofs.isCanonicalExt4_extInv,
  ``qsag_whir_verified.proofs.ext_mul_extInv_ok_one,
  ``qsag_whir_verified.proofs.canonicalFieldWord_two_inv,
  ``qsag_whir_verified.proofs.canonicalFieldWord_two_x_inv,
  ``qsag_whir_verified.proofs.decode_canonical_u64_refines_qsag,
  ``qsag_whir_verified.proofs.decode_canonical_ext4_refines_qsag,
  ``qsag_whir_verified.proofs.decode_canonical_ext4_canonicalExt4,
  ``qsag_whir_verified.proofs.embedBase_inv,
  ``qsag_whir_verified.proofs.hemAffineDuetFold_eq_hemVirtualFoldOracle,
  ``qsag_whir_verified.proofs.fold_duet_affine_ext4_refines_hemVirtualFoldOracle,
  ``qsag_whir_verified.proofs.verify_cwyz_duet_fold_step_sound_qsag,
  ``qsag_whir_verified.proofs.verify_affine_duet_fold_step_sound_qsag,
  ``qsag_whir_verified.proofs.verify_affine_duet_fold_step_roots_le_one,
  ``qsag_whir_verified.proofs.hemBridgeClaimStep_eq_hemBridgeFoldClaim,
  ``qsag_whir_verified.proofs.verify_cwyz_bridge_claim_step_sound_qsag,
  ``qsag_whir_verified.proofs.affine_cascade_claim_step_refines_evalCascadeClaim,
  ``qsag_whir_verified.proofs.eval_quadratic_sumcheck_wire_refines_qsag,
  ``qsag_whir_verified.proofs.eval_quadratic_sumcheck_wire_bad_challenges_le_two,
  ``qsag_whir_verified.proofs.hemHorner_zero_eq_evalCoeffs,
  ``qsag_whir_verified.proofs.eval_ext4_univariate_at_base_refines_evalCoeffs,
  ``qsag_whir_verified.proofs.verify_ext4_univariate_at_base_pin_sound_qsag,
  ``qsag_whir_verified.proofs.verify_ext4_univariate_at_base_pin_roots_le_degree,
  ``qsag_whir_verified.proofs.ext4SliceWords_injective,
  ``qsag_whir_verified.proofs.verify_ood_pin_eq_canonical_ext4_iff,
  ``qsag_whir_verified.proofs.verify_stage_pow_mask_16_iff_verifyWhirStagePow,
  ``qsag_whir_verified.proofs.step_merkle_pair_order_canonical_parity,
  ``qsag_whir_verified.proofs.checked_quorum_sum_sound_qsag,
  ``qsag_whir_verified.proofs.tooth_canonical_cwyz_fold_rejects_wrong_twiddle_and_forged_claim,
  ``qsag_whir_verified.proofs.fieldAbs_mul,
  ``qsag_whir_verified.proofs.fieldAbs_sub,
  ``qsag_whir_verified.proofs.ext4Abs_add,
  ``qsag_whir_verified.proofs.ext4Abs_sub,
  ``qsag_whir_verified.proofs.ext4Abs_mul,
  ``qsag_whir_verified.proofs.ext_mul_refines_exec,
  ``qsag_whir_verified.proofs.cwyz_bridge_refines_exec,
  ``qsag_whir_verified.proofs.ext4Abs_scale,
  ``qsag_whir_verified.proofs.fieldAbs_zero,
  ``qsag_whir_verified.proofs.ext4Abs_zero,
  ``qsag_whir_verified.proofs.duet_fold_refines_exec,
  ``qsag_whir_verified.proofs.hornerSpec_refines_exec,
  ``qsag_whir_verified.proofs.eval_ext4_univariate_refines_exec,
  ``qsag_whir_verified.proofs.fold_duet_affine_ext4_refines_exec,
  ``qsag_whir_verified.proofs.fieldAbs_canonicalFieldWord,
  ``qsag_whir_verified.proofs.fold_duet_affine_ext4_canonical_twiddles,
  ``qsag_whir_verified.proofs.verify_stage_pow_mask_refines_canonical,
  ``qsag_whir_verified.proofs.goldilocks_p_val,
  ``qsag_whir_verified.proofs.max_u64_word_val,
  ``qsag_whir_verified.proofs.tag_canopy_merkle_internal_eq,
  ``qsag_whir_verified.proofs.add_refines,
  ``qsag_whir_verified.proofs.sub_refines,
  ``qsag_whir_verified.proofs.mul_refines,
  ``qsag_whir_verified.proofs.ext_add_refines,
  ``qsag_whir_verified.proofs.ext_sub_refines,
  ``qsag_whir_verified.proofs.ext_scale_refines,
  ``qsag_whir_verified.proofs.ext_mul_refines,
  ``qsag_whir_verified.proofs.affine_combine_refines,
  ``qsag_whir_verified.proofs.extU_pow4_eq_seven,
  ``qsag_whir_verified.proofs.towerToPoly_mul_hom,
  ``qsag_whir_verified.proofs.duet_refines,
  ``qsag_whir_verified.proofs.duet_fold_algebraic_sound,
  ``qsag_whir_verified.proofs.cwyz_duet_refines,
  ``qsag_whir_verified.proofs.cwyz_duet_fold_algebraic_sound,
  ``qsag_whir_verified.proofs.cwyz_bridge_claim_step_refines,
  ``qsag_whir_verified.proofs.cwyz_bridge_claim_step_dual_sound,
  ``qsag_whir_verified.proofs.eval_quadratic_sumcheck_wire_refines,
  ``qsag_whir_verified.proofs.eval_quadratic_sumcheck_wire_hypercube_sum,
  ``qsag_whir_verified.proofs.affine_cascade_claim_step_refines,
  ``qsag_whir_verified.proofs.hornerSpec_eq_evalPolyAscending,
  ``qsag_whir_verified.proofs.decode_canonical_u64_spec,
  ``qsag_whir_verified.proofs.decode_canonical_u64_some_iff,
  ``qsag_whir_verified.proofs.decode_canonical_u64_none_iff,
  ``qsag_whir_verified.proofs.decode_canonical_u64_rejects_noncanonical,
  ``qsag_whir_verified.proofs.decode_canonical_ext4_spec,
  ``qsag_whir_verified.proofs.decode_canonical_ext4_some_iff,
  ``qsag_whir_verified.proofs.decode_canonical_ext4_none_iff,
  ``qsag_whir_verified.proofs.ext_eq_spec,
  ``qsag_whir_verified.proofs.ext_eq_sound,
  ``qsag_whir_verified.proofs.duet_fold_coset_sound,
  ``qsag_whir_verified.proofs.verify_affine_duet_fold_step_spec,
  ``qsag_whir_verified.proofs.verify_affine_duet_fold_step_sound,
  ``qsag_whir_verified.proofs.verify_affine_duet_fold_step_coset_sound,
  ``qsag_whir_verified.proofs.cwyz_duet_fold_coset_sound,
  ``qsag_whir_verified.proofs.fold_duet_affine_ext4_spec,
  ``qsag_whir_verified.proofs.fold_duet_affine_ext4_coset_sound,
  ``qsag_whir_verified.proofs.verify_cwyz_duet_fold_step_spec,
  ``qsag_whir_verified.proofs.verify_cwyz_duet_fold_step_sound,
  ``qsag_whir_verified.proofs.verify_cwyz_duet_fold_step_coset_sound,
  ``qsag_whir_verified.proofs.cwyz_bridge_claim_step_dual_spec,
  ``qsag_whir_verified.proofs.verify_cwyz_bridge_claim_step_spec,
  ``qsag_whir_verified.proofs.verify_cwyz_bridge_claim_step_sound,
  ``qsag_whir_verified.proofs.verify_cwyz_bridge_claim_step_dual_sound,
  ``qsag_whir_verified.proofs.eval_quadratic_sumcheck_wire_hypercube_spec,
  ``qsag_whir_verified.proofs.affine_cascade_claim_step_spec,
  ``qsag_whir_verified.proofs.eval_ext4_univariate_at_base_spec,
  ``qsag_whir_verified.proofs.eval_ext4_univariate_at_base_ascending_sound,
  ``qsag_whir_verified.proofs.eval_univariate_ext4_at_base_spec,
  ``qsag_whir_verified.proofs.eval_univariate_ext4_at_base_ascending_sound,
  ``qsag_whir_verified.proofs.verify_ext4_univariate_at_base_pin_spec,
  ``qsag_whir_verified.proofs.verify_ext4_univariate_at_base_pin_sound,
  ``qsag_whir_verified.proofs.verify_ext4_univariate_at_base_pin_ascending_sound,
  ``qsag_whir_verified.proofs.verify_stage_pow_mask_spec,
  ``qsag_whir_verified.proofs.verify_stage_pow_mask_sound,
  ``qsag_whir_verified.proofs.verify_stage_pow_mask_mod_sound,
  ``qsag_whir_verified.proofs.verify_ood_pin_eq_spec,
  ``qsag_whir_verified.proofs.verify_ood_pin_eq_sound,
  ``qsag_whir_verified.proofs.verify_ood_pin_eq_false_iff,
  ``qsag_whir_verified.proofs.canonical_query_group_idx_spec,
  ``qsag_whir_verified.proofs.canonical_query_group_idx_some_iff,
  ``qsag_whir_verified.proofs.canonical_query_group_idx_none_iff,
  ``qsag_whir_verified.proofs.canonical_query_group_idx_lt_groups,
  ``qsag_whir_verified.proofs.step_merkle_pair_order_spec,
  ``qsag_whir_verified.proofs.step_merkle_pair_order_some_iff,
  ``qsag_whir_verified.proofs.step_merkle_pair_order_none_iff,
  ``qsag_whir_verified.proofs.step_merkle_pair_order_tag_eq,
  ``qsag_whir_verified.proofs.checked_quorum_sum_total,
  ``qsag_whir_verified.proofs.checked_quorum_sum_sound,
  ``qsag_whir_verified.proofs.checked_quorum_sum_none_iff,
  ``qsag_whir_verified.proofs.checked_quorum_sum_le_max_u64_word,
  ``qsag_whir_verified.proofs.tooth_unchecked_mod_p_accepts_aliased_field_limb,
  ``qsag_whir_verified.proofs.tooth_decode_canonical_ext4_rejects_fourth_limb_alias,
  ``qsag_whir_verified.proofs.tooth_pow_rejects_excessive_bits_and_nonzero_low_bits,
  ``qsag_whir_verified.proofs.tooth_merkle_pair_swaps_on_direction_bit_and_rejects_shift64,
  ``qsag_whir_verified.proofs.tooth_checked_quorum_sum_rejects_u64_wraparound_forgery,
  ``qsag_whir_verified.proofs.tooth_ood_pin_rejects_perturbation_and_length_mismatch,
  ``qsag_whir_verified.proofs.tooth_coset_inverse_premises_inhabited_and_fold_rejects_perturbation,
  ``qsag_whir_verified.proofs.tooth_cwyz_bridge_accepts_dual_and_rejects_perturbation,
  ``qsag_whir_verified.proofs.tooth_horner_and_pin_accepts_ascending_and_rejects_perturbation,
  ``qsag_whir_verified.proofs.tooth_quadratic_sumcheck_wire_nontrivial_eval,
  ``qsag_whir_verified.proofs.whirWp_ok,
  ``qsag_whir_verified.proofs.whirWp_mono,
  ``qsag_whir_verified.proofs.FieldRefines_canonicalFieldWord,
  ``qsag_whir_verified.proofs.FieldRefines_iff_eq_canonicalFieldWord,
  ``qsag_whir_verified.proofs.Ext4Refines_canonicalExt4,
  ``qsag_whir_verified.proofs.Ext4Refines_iff_eq_canonicalExt4,
  ``qsag_whir_verified.proofs.extAdd_rel2,
  ``qsag_whir_verified.proofs.extSub_rel2,
  ``qsag_whir_verified.proofs.extMul_rel2,
  ``qsag_whir_verified.proofs.extInv_rel1,
  ``qsag_whir_verified.proofs.decode_canonical_ext4_wp_ext4Refines,
  ``qsag_whir_verified.proofs.fold_duet_affine_ext4_wp_ext4Refines,
  ``qsag_whir_verified.proofs.cwyz_bridge_claim_step_wp_ext4Refines,
  ``qsag_whir_verified.proofs.eval_quadratic_sumcheck_wire_wp_ext4Refines,
  ``qsag_whir_verified.proofs.verify_ood_pin_eq_wp_ext4Refines,
  ``qsag_whir_verified.proofs.checked_quorum_sum_wp_u64NatRefines
]

/-! ## Symbol coverage

Every Rust item extracted into `QsagWhirVerified.Funs` must occur in the *statement* of at
least one non-`tooth_*` specification or soundness theorem from the supplied list. Aeneas
splits a Rust loop into `f_loop` and `f_loop.body`; these are not Rust items, so each is
accepted only when the Rust function `f` it was split from is itself covered by a
non-`tooth_*` theorem and reaches the helper through its definition. -/

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

/-- For `f_loop` and `f_loop.body`, the pair `(f, f_loop)`. -/
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

/-- Returns the extracted symbols and the subset no non-`tooth_*` theorem statement covers. -/
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

/-- The gate must notice a missing specification theorem: with no theorems every symbol is a
gap, with only `tooth_*` theorems every symbol is still a gap, and without the
`checked_quorum_sum` theorems that function and both loop helpers are gaps. -/
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

/- Compile-time linter/attribute registration is meta infrastructure. Only declarations
marked meta in Aeneas.Elab.Attrs are excluded; pure declarations and all proof
dependency closures keep the constructive allowlist. -/
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
      if (owner == "QsagWhirVerified" || owner.startsWith "QsagWhirVerified." ||
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

public def main : IO UInt32 := do
  initSearchPath (← findSysroot) [".lake/build/lib/lean", "../../lean/.lake/build/lib/lean"]
  let imported ← importModules #[{ module := `AuditWhirMirAxioms, importAll := true }] {}
  let env := imported.setExporting false
  let summaries := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  let mut missingAnchors : Array Name := #[]
  for req in requiredWhirMirTheorems do
    match env.find? req with
    | some (.thmInfo _) => pure ()
    | _ => missingAnchors := missingAnchors.push req
  let (negative, checked, theorems, modules, failures) := CollectAxioms.runM (env.setExporting false) do
    let negative ← CollectAxioms.collectAndGet summaries.find? ``Classical.choice
    let mut checked := 0
    let mut theorems := 0
    let mut modules : Array Name := #[]
    let mut failures : Array (Name × Array Name) := #[]
    for (name, _) in env.constants.toList do
      if let some idx := env.getModuleIdxFor? name then
        let owner := env.header.moduleNames[idx.toNat]!.toString
        if (owner == "QsagWhirVerified" || owner.startsWith "QsagWhirVerified." ||
            owner == "Aeneas" || owner.startsWith "Aeneas.") &&
            !(owner == "Aeneas.Elab.Attrs" && isMarkedMeta env name) then
          checked := checked + 1
          if let some (.thmInfo _) := env.find? name then theorems := theorems + 1
          let ownerName := env.header.moduleNames[idx.toNat]!
          if !modules.contains ownerName then modules := modules.push ownerName
          let axioms ← CollectAxioms.collectAndGet summaries.find? name
          let forbidden := axioms.filter fun ax => ax != ``propext && ax != ``Quot.sound
          if !forbidden.isEmpty then
            failures := failures.push (name, forbidden)
    return (negative, checked, theorems, modules, failures)
  if (negative.filter fun ax => ax != ``propext && ax != ``Quot.sound).isEmpty then
    throw (IO.userError "WHIR MIR axiom audit negative control unexpectedly passed")
  -- The replayed theorem list is read from the comparator configuration in the package root.
  let config ← IO.ofExcept (Json.parse (← IO.FS.readFile "comparator.json"))
  let replayed := (← IO.ofExcept (config.getObjValAs? (Array String) "theorem_names")).map
    String.toName
  let unanchored := replayed.filter fun thm => !requiredWhirMirTheorems.contains thm
  let (symbols, gaps) := symbolCoverage env replayed
  if symbolCoverageControlsFail env replayed then
    throw (IO.userError "WHIR symbol coverage negative control unexpectedly passed")
  for thm in unanchored do
    IO.println s!"REPLAYED THEOREM WITHOUT AN AXIOM ANCHOR {thm}"
  for symbol in gaps do
    IO.println s!"EXTRACTED SYMBOL WITHOUT A REPLAYED THEOREM STATEMENT {symbol}"
  IO.println s!"WHIR symbol coverage: {symbols.size} extracted symbols, {replayed.size} replayed theorems; {gaps.size} uncovered, {unanchored.size} unanchored"
  for req in missingAnchors do
    IO.println s!"MISSING ANCHOR THEOREM {req}"
  for (name, forbidden) in failures do
    IO.println s!"REJECT {name}: {forbidden}"
  IO.println s!"WHIR MIR axiom audit: {checked} declarations, {theorems} theorems ({requiredWhirMirTheorems.size} anchored), {modules.size} modules; {failures.size} rejected, {missingAnchors.size} missing anchors"
  return if checked > 0 && failures.isEmpty && missingAnchors.isEmpty &&
      !symbols.isEmpty && gaps.isEmpty && unanchored.isEmpty then 0 else 1
