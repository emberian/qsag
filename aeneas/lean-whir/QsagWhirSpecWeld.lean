module
import Lean
import all QsagWhirVerified.Funs
public import QsagWhirVerified.Canonical
import all QsagWhirVerified.Canonical
public import QsagWhirVerified.ProtocolWeld
import all QsagWhirVerified.ProtocolWeld

/-!
# `QsagWhirSpecWeld` — 54/54 Quintic `Fp5` WHIR MIR-to-`Qsag` Protocol Weld Library & Axiom Census

Root weld target for `qsag_whir_aeneas`, enforcing at compile time:
1. **100% Canonical `Qsag` Weld Coverage (54/54 `QsagWhirVerified.Funs` Definitions):**
   Every extracted Rust constant/function in `QsagWhirVerified.Funs` (50 Rust items plus 4 split
   loop helpers) occurs in a non-`tooth_*` theorem statement whose proposition ALSO references a
   canonical `Qsag.*` specification declaration!
2. **Protocol-Level Quintic `Fp5` Anchors:**
   Verifies the presence of the multi-round sumcheck weld (`mirVerifyShiftSumcheckChainFp5_iff_qsag`),
   the `ZkHemV2` zero-knowledge mask-line weld (`mir_affine_combine_fp5_coin_bijection_simulated`),
   the `QSAGHQM2` & `[16, 28]` schedule welds (`verify_qsaghqm2_header_refines_qsag`,
   `verify_quintic_schedule_envelope_accepts_zkHemV2ProdStages`), and the `verifyHemAffineWhir`
   stage weld (`mirStageGatesFp5_sound_for_verifyHemAffineWhir`).
3. **Constructive Axiom Gate (`axioms ⊆ {propext, Quot.sound}`):**
   Audits every declaration in `QsagWhirVerified.Canonical` and `QsagWhirVerified.ProtocolWeld`
   with an active negative control rejecting `Classical.choice`.
-/

namespace QsagWhirSpecWeld
export qsag_whir_verified.proofs (
  fieldAbs
  fp5Abs
  gl24Abs
  canonicalFieldWord
  canonicalFp5
  canonicalGl24
  fp5Inv
  goldilocks_p_eq_qsag_prime
  max_u64_word_lt_two_pow_64_qsag
  fp5_nonresidue_w_eq_qsag
  frobenius_zeta5_constants_eq_qsag
  copy_fp5_refines_qsag
  load_le_u64_40_refines_qsag
  load_le_u64_56_refines_qsag
  decode_canonical_u64_refines_qsag
  decode_canonical_fp5_limbs_refines_qsag
  decode_canonical_fp5_refines_qsag
  decode_canonical_gl24_limbs_refines_qsag
  decode_canonical_gl24_digest_refines_qsag
  add_refines_qsag
  sub_refines_qsag
  mul_refines_qsag
  fp5_zero_refines_qsag
  fp5_one_refines_qsag
  fp5_from_base_refines_qsag
  fp5_eq_iff_qsag
  fp5_add_refines_qsag
  fp5_sub_refines_qsag
  fp5_neg_refines_qsag
  fp5_scale_refines_qsag
  fp5_mul_refines_qsag
  fp5_frobenius_refines_qsag
  affine_combine_fp5_refines_zkHemV2_maskLine
  mir_affine_combine_fp5_coin_bijection_simulated
  duet_fold_fp5_refines_qsag
  duet_fold_fp5_antipodal_fiberPoint_qsag
  verify_affine_duet_fold_step_fp5_sound_qsag
  cwyz_duet_fold_fp5_refines_hemVirtualFoldOracle
  verify_cwyz_duet_fold_step_fp5_sound_qsag
  cwyz_bridge_claim_step_fp5_refines_hemBridgeFoldClaim
  verify_cwyz_bridge_claim_step_fp5_sound_qsag
  eval_quadratic_sumcheck_wire_fp5_refines_qsag
  mirVerifyShiftSumcheckChainFp5
  mirVerifyShiftSumcheckChainFp5_iff_qsag
  mirStageGatesFp5_sound_for_verifyHemAffineWhir
  eval_fp5_univariate_at_base_refines_evalCoeffs
  verify_fp5_univariate_at_base_pin_sound_qsag
  verify_ood_pin_eq_fp5_canonical_iff_qsag
  canonical_query_group_idx_refines_qsag
  step_merkle_pair_order_400_canonical_parity
  step_merkle_pair_order_gl24_refines_poseidon2Gl24
  checked_quorum_sum_sound_qsag
  checked_quorum_sum_wp_u64NatRefines
  verify_qsaghqm2_header_refines_qsag
  verify_quintic_schedule_envelope_accepts_zkHemV2ProdStages
)
end QsagWhirSpecWeld

open Lean Elab Command in
run_cmd do
  let canonicalWeldTheorems : Array Name := #[
    ``qsag_whir_verified.proofs.goldilocks_p_eq_qsag_prime,
    ``qsag_whir_verified.proofs.max_u64_word_lt_two_pow_64_qsag,
    ``qsag_whir_verified.proofs.fp5_nonresidue_w_eq_qsag,
    ``qsag_whir_verified.proofs.frobenius_zeta5_constants_eq_qsag,
    ``qsag_whir_verified.proofs.copy_fp5_refines_qsag,
    ``qsag_whir_verified.proofs.load_le_u64_40_refines_qsag,
    ``qsag_whir_verified.proofs.load_le_u64_56_refines_qsag,
    ``qsag_whir_verified.proofs.decode_canonical_u64_refines_qsag,
    ``qsag_whir_verified.proofs.decode_canonical_fp5_limbs_refines_qsag,
    ``qsag_whir_verified.proofs.decode_canonical_fp5_refines_qsag,
    ``qsag_whir_verified.proofs.decode_canonical_gl24_limbs_refines_qsag,
    ``qsag_whir_verified.proofs.decode_canonical_gl24_digest_refines_qsag,
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
    ``qsag_whir_verified.proofs.affine_combine_fp5_refines_zkHemV2_maskLine,
    ``qsag_whir_verified.proofs.mir_affine_combine_fp5_coin_bijection_simulated,
    ``qsag_whir_verified.proofs.duet_fold_fp5_antipodal_fiberPoint_qsag,
    ``qsag_whir_verified.proofs.verify_affine_duet_fold_step_fp5_sound_qsag,
    ``qsag_whir_verified.proofs.cwyz_duet_fold_fp5_refines_hemVirtualFoldOracle,
    ``qsag_whir_verified.proofs.verify_cwyz_duet_fold_step_fp5_sound_qsag,
    ``qsag_whir_verified.proofs.cwyz_bridge_claim_step_fp5_refines_hemBridgeFoldClaim,
    ``qsag_whir_verified.proofs.verify_cwyz_bridge_claim_step_fp5_sound_qsag,
    ``qsag_whir_verified.proofs.eval_quadratic_sumcheck_wire_fp5_refines_qsag,
    ``qsag_whir_verified.proofs.mirVerifyShiftSumcheckChainFp5_iff_qsag,
    ``qsag_whir_verified.proofs.mirStageGatesFp5_sound_for_verifyHemAffineWhir,
    ``qsag_whir_verified.proofs.eval_fp5_univariate_at_base_refines_evalCoeffs,
    ``qsag_whir_verified.proofs.verify_fp5_univariate_at_base_pin_sound_qsag,
    ``qsag_whir_verified.proofs.verify_ood_pin_eq_fp5_canonical_iff_qsag,
    ``qsag_whir_verified.proofs.canonical_query_group_idx_refines_qsag,
    ``qsag_whir_verified.proofs.step_merkle_pair_order_400_canonical_parity,
    ``qsag_whir_verified.proofs.step_merkle_pair_order_gl24_refines_poseidon2Gl24,
    ``qsag_whir_verified.proofs.checked_quorum_sum_wp_u64NatRefines,
    ``qsag_whir_verified.proofs.verify_qsaghqm2_header_refines_qsag,
    ``qsag_whir_verified.proofs.verify_quintic_schedule_envelope_accepts_zkHemV2ProdStages
  ]
  let negative ← Lean.collectAxioms ``Classical.choice
  if (negative.filter fun ax => ax != ``propext && ax != ``Quot.sound).isEmpty then
    throwError "WHIR spec weld negative control unexpectedly passed"
  let env := (← getEnv).setExporting false
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
  unless symbols.size == 54 && gaps.isEmpty do
    throwError "WHIR spec weld symbol coverage failed: {symbols.size} symbols, uncovered={gaps}"
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
  logInfo m!"WHIR spec weld audit: {symbols.size}/54 Funs symbols welded to Qsag, {checked} declarations audited, 0 rejected"
