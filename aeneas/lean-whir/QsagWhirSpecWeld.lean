module
import Lean
import all QsagWhirVerified.Funs
public import QsagWhirVerified.Canonical
import all QsagWhirVerified.Canonical
public import QsagWhirVerified.ProtocolWeld
import all QsagWhirVerified.ProtocolWeld

/-!
# `QsagWhirSpecWeld` — 37/37 WHIR MIR-to-`Qsag` Protocol Weld Library & Axiom Census

Root weld target for `qsag_whir_aeneas` (analogous to `QsagSpecWeld` and `QsagCustodyWeld` in
`aeneas/lean`), enforcing at compile time:
1. **100% Canonical `Qsag` Weld Coverage (37/37 `QsagWhirVerified.Funs` Definitions):**
   Every extracted Rust constant/function in `QsagWhirVerified.Funs` (and every loop helper via its
   parent Rust function) occurs in a non-`tooth_*` theorem statement whose proposition ALSO
   references a canonical `Qsag.*` specification declaration!
2. **Protocol-Level `Arch 2a` Anchors:**
   Verifies the presence of the multi-round sumcheck weld (`mirVerifyShiftSumcheckChain_iff_qsag`),
   the `ZkHemV2` zero-knowledge mask-line weld (`mir_affine_combine_coin_bijection_simulated`),
   and the `verifyHemAffineWhir` cascade/stage weld (`mirStageGates_sound_for_verifyHemAffineWhir`).
3. **Constructive Axiom Gate (`axioms ⊆ {propext, Quot.sound}`):**
   Audits every declaration in `QsagWhirVerified.Canonical` and `QsagWhirVerified.ProtocolWeld`
   with an active negative control rejecting `Classical.choice`.
-/

namespace QsagWhirSpecWeld
export qsag_whir_verified.proofs (
  fieldAbs
  ext4Abs
  canonicalFieldWord
  canonicalExt4
  extInv
  goldilocks_p_eq_qsag_prime
  max_u64_word_lt_two_pow_64_qsag
  tag_canopy_merkle_internal_qsag
  decode_canonical_u64_refines_qsag
  decode_canonical_ext4_refines_qsag
  add_refines_qsag
  sub_refines_qsag
  mul_refines_qsag
  ext_eq_iff_qsag
  ext_add_refines_qsag
  ext_sub_refines_qsag
  ext_scale_refines_qsag
  ext_mul_refines_exec
  affine_combine_refines_zkHemV2_maskLine
  mir_affine_combine_coin_bijection_simulated
  duet_fold_refines_exec
  verify_affine_duet_fold_step_sound_qsag
  cwyz_duet_fold_refines_foldDuetExt4
  fold_duet_affine_ext4_refines_hemVirtualFoldOracle
  verify_cwyz_duet_fold_step_sound_qsag
  cwyz_bridge_refines_exec
  verify_cwyz_bridge_claim_step_sound_qsag
  eval_quadratic_sumcheck_wire_refines_qsag
  mirVerifyShiftSumcheckChain
  mirVerifyShiftSumcheckChain_iff_qsag
  affine_cascade_claim_step_refines_evalCascadeClaim
  mirEvalCascadeBatch
  mirEvalCascadeBatch_refines_evalCascadeClaim
  mirStageGates_sound_for_verifyHemAffineWhir
  eval_ext4_univariate_at_base_refines_evalCoeffs
  eval_univariate_ext4_at_base_refines_evalCoeffs
  verify_ext4_univariate_at_base_pin_sound_qsag
  verify_stage_pow_mask_refines_canonical
  verify_stage_pow_mask_16_iff_verifyWhirStagePow
  verify_ood_pin_eq_canonical_ext4_iff
  canonical_query_group_idx_refines_qsag
  step_merkle_pair_order_canonical_parity
  checked_quorum_sum_sound_qsag
  checked_quorum_sum_wp_u64NatRefines
)
end QsagWhirSpecWeld

open Lean Elab Command in
run_cmd do
  let canonicalWeldTheorems : Array Name := #[
    ``qsag_whir_verified.proofs.goldilocks_p_eq_qsag_prime,
    ``qsag_whir_verified.proofs.max_u64_word_lt_two_pow_64_qsag,
    ``qsag_whir_verified.proofs.tag_canopy_merkle_internal_qsag,
    ``qsag_whir_verified.proofs.decode_canonical_u64_refines_qsag,
    ``qsag_whir_verified.proofs.decode_canonical_ext4_refines_qsag,
    ``qsag_whir_verified.proofs.add_refines_qsag,
    ``qsag_whir_verified.proofs.sub_refines_qsag,
    ``qsag_whir_verified.proofs.mul_refines_qsag,
    ``qsag_whir_verified.proofs.ext_eq_iff_qsag,
    ``qsag_whir_verified.proofs.ext_add_refines_qsag,
    ``qsag_whir_verified.proofs.ext_sub_refines_qsag,
    ``qsag_whir_verified.proofs.ext_scale_refines_qsag,
    ``qsag_whir_verified.proofs.ext_mul_refines_exec,
    ``qsag_whir_verified.proofs.affine_combine_refines_zkHemV2_maskLine,
    ``qsag_whir_verified.proofs.mir_affine_combine_coin_bijection_simulated,
    ``qsag_whir_verified.proofs.duet_fold_refines_exec,
    ``qsag_whir_verified.proofs.verify_affine_duet_fold_step_sound_qsag,
    ``qsag_whir_verified.proofs.cwyz_duet_fold_refines_foldDuetExt4,
    ``qsag_whir_verified.proofs.fold_duet_affine_ext4_refines_hemVirtualFoldOracle,
    ``qsag_whir_verified.proofs.verify_cwyz_duet_fold_step_sound_qsag,
    ``qsag_whir_verified.proofs.cwyz_bridge_refines_exec,
    ``qsag_whir_verified.proofs.verify_cwyz_bridge_claim_step_sound_qsag,
    ``qsag_whir_verified.proofs.eval_quadratic_sumcheck_wire_refines_qsag,
    ``qsag_whir_verified.proofs.mirVerifyShiftSumcheckChain_iff_qsag,
    ``qsag_whir_verified.proofs.affine_cascade_claim_step_refines_evalCascadeClaim,
    ``qsag_whir_verified.proofs.mirEvalCascadeBatch_refines_evalCascadeClaim,
    ``qsag_whir_verified.proofs.mirStageGates_sound_for_verifyHemAffineWhir,
    ``qsag_whir_verified.proofs.eval_ext4_univariate_at_base_refines_evalCoeffs,
    ``qsag_whir_verified.proofs.eval_univariate_ext4_at_base_refines_evalCoeffs,
    ``qsag_whir_verified.proofs.verify_ext4_univariate_at_base_pin_sound_qsag,
    ``qsag_whir_verified.proofs.verify_stage_pow_mask_refines_canonical,
    ``qsag_whir_verified.proofs.verify_stage_pow_mask_16_iff_verifyWhirStagePow,
    ``qsag_whir_verified.proofs.verify_ood_pin_eq_canonical_ext4_iff,
    ``qsag_whir_verified.proofs.canonical_query_group_idx_refines_qsag,
    ``qsag_whir_verified.proofs.step_merkle_pair_order_canonical_parity,
    ``qsag_whir_verified.proofs.checked_quorum_sum_wp_u64NatRefines
  ]
  let negative ← Lean.collectAxioms ``Classical.choice
  if (negative.filter fun ax => ax != ``propext && ax != ``Quot.sound).isEmpty then
    throwError "WHIR spec weld negative control unexpectedly passed"
  let env := (← getEnv).setExporting false
  -- 1. Verify every canonical weld theorem exists, is a `.thmInfo`, and mentions a `Qsag.*` constant!
  let mut mentioned : NameSet := {}
  for thm in canonicalWeldTheorems do
    if let .str _ leaf := thm then
      if leaf.startsWith "tooth_" then
        throwError "WHIR spec weld cannot use a mutation witness for coverage: {thm}"
    match env.find? thm with
    | some (.thmInfo info) =>
      let used := info.type.getUsedConstants
      let touchesQsag := used.any fun c => c.toString.startsWith "Qsag."
      unless touchesQsag do
        throwError "WHIR weld theorem `{thm}` does not mention any canonical `Qsag.*` symbol in its statement"
      for u in used do
        mentioned := mentioned.insert u
    | _ =>
      throwError "WHIR spec weld missing theorem target: {thm}"
  -- 2. Verify 37/37 `QsagWhirVerified.Funs` symbol coverage by canonical `Qsag`-welded theorems!
  let mut symbols : Array Name := #[]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if env.header.moduleNames[idx.toNat]! == `QsagWhirVerified.Funs && !name.isInternalDetail then
        if let .defnInfo _ := info then
          symbols := symbols.push name
  let defUses (nm used : Name) : Bool :=
    match env.find? nm with
    | some (.defnInfo d) => d.value.getUsedConstants.contains used
    | _ => false
  let loopOrigin? (nm : Name) : Option (Name × Name) :=
    let loopName := match nm with | .str pre "body" => pre | other => other
    match loopName with
    | .str pre s =>
      if s.endsWith "_loop" && s.length > 5 then
        some (.str pre (String.ofList (s.toList.take (s.length - 5))), loopName)
      else none
    | _ => none
  let mut gaps : Array Name := #[]
  for sym in symbols do
    let cov := match loopOrigin? sym with
      | some (origin, loopName) =>
        symbols.contains origin && mentioned.contains origin &&
          defUses origin loopName && (sym == loopName || defUses loopName sym)
      | none => mentioned.contains sym
    if !cov then gaps := gaps.push sym
  unless symbols.size == 37 && gaps.isEmpty do
    throwError "WHIR spec weld symbol coverage failed: {symbols.size} symbols, uncovered={gaps}"
  -- 3. Audit every declaration in `Canonical` and `ProtocolWeld` against `{propext, Quot.sound}`.
  let weldModules := ["QsagWhirVerified.Canonical", "QsagWhirVerified.ProtocolWeld"]
  let mut checked : Nat := 0
  let mut rejected : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let owner := env.header.moduleNames[idx.toNat]!.toString
      if weldModules.contains owner then
        checked := checked + 1
        let axioms ← withEnv env <| Lean.collectAxioms name
        let forbidden := axioms.filter fun ax => ax != ``propext && ax != ``Quot.sound
        if !forbidden.isEmpty then
          rejected := rejected + 1
          logInfo m!"REJECT {name} ({owner}): {forbidden}"
  if checked == 0 || rejected > 0 then
    throwError "WHIR spec weld axiom audit failed: checked={checked}, rejected={rejected}"
  logInfo m!"WHIR spec weld audit: {symbols.size}/37 Funs symbols welded to Qsag, {checked} declarations audited, 0 rejected"
