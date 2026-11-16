module
import Lean
import all Aeneas.Elab.Attrs
import all QsagMirProofs
import all QsagVerified.Funs
import all QsagVerified.Proofs
import all QsagVerified.Proofs.Adrs
import all QsagVerified.Proofs.AdrsConverse
import all QsagVerified.Proofs.Bdoz
import all QsagVerified.Proofs.BdozConsumption
import all QsagVerified.Proofs.Common
import all QsagVerified.Proofs.ConsumingOpening
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
import all QsagVerified.Proofs.MirWpKit
import all QsagVerified.Proofs.PantsAndQuorumGuards
import all QsagVerified.Proofs.PolicyAndAddr
import all QsagVerified.Proofs.RssCutSession
import all QsagVerified.Proofs.ShamirDkg
import all QsagVerified.Proofs.Sponge
import all QsagVerified.Proofs.SpongeConformance
import all QsagVerified.Proofs.SpongeFraming
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
import all QsagCustodyWeld

/-!
This gate audits dependency closures of definitions AND theorems. Auditing an extracted
function is not a correctness proof for that function. The theorem anchors below prevent
core delivered weld boundaries from silently disappearing or becoming mere definitions.
The per-module census includes every logical declaration, including future proofs.
Compile-time elaborators are classified by meta metadata; their emitted terms are audited.
The protocol-level welds (`RealSpecBeltWeld`, `RealSpecGuardBoundary`,
`AuthenticatedBeltAndRealSpecWeld`) are censused by `QsagCustodyWeld`, which shares this policy.
-/

open Lean Elab Command in
run_cmd do
  let negative ← Lean.collectAxioms ``Classical.choice
  if (negative.filter fun ax => ax != ``propext && ax != ``Quot.sound).isEmpty then
    throwError "MIR axiom audit negative control unexpectedly passed"
  let env := (← getEnv).setExporting false
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
    -- Production MIR boundaries must remain present as theorems, not just modules.
    ``qsag_verified.proofs.wots_checksum_base16_spec,
    ``qsag_verified.proofs.wots_checksum_strict_antitone,
    ``qsag_verified.proofs.wots_extract_base16_digits_spec,
    ``qsag_verified.proofs.fips205_wots_checksum_spec,
    ``qsag_verified.proofs.adrs_encode_eq,
    ``qsag_verified.proofs.fips205_adrs_roundtrip_spec,
    ``qsag_verified.proofs.fips205_adrs_decode_invalid_type_none,
    ``qsag_verified.proofs.bdoz_authenticate_open_spec,
    ``qsag_verified.proofs.bdoz_tampered_mac_rejected,
    ``qsag_verified.proofs.bdoz_mac_one_time_burn_spec,
    ``qsag_verified.proofs.shamir_eval_poly_gf256_spec,
    ``qsag_verified.proofs.shamir_lagrange_at_zero_gf256_2of2_spec,
    ``qsag_verified.proofs.shamir_lagrange_at_zero_gf256_3of3_spec,
    ``qsag_verified.proofs.shamir_degree_reduce_2of3_gf256_spec,
    ``qsag_verified.proofs.dkg_verify_shamir_2of3_key_bit_gf256_spec,
    ``qsag_verified.proofs.dkg_inconsistent_reconstructions_rejected,
    ``qsag_verified.proofs.fts_guard_at_most_one_sig_per_epoch,
    ``qsag_verified.proofs.wots_cs_68_sum136_incomparable_mir,
    ``qsag_verified.proofs.fts_spn_output_implies_intermediate_mac_ok,
    ``qsag_verified.proofs.wotsc256_verify_refines_qsag,
    ``qsag_verified.proofs.wotsc256_accept_iff_qsag,
    ``qsag_verified.proofs.wotsc256_reject_iff_qsag,
    ``qsag_verified.proofs.keccak_f1600_array_refines_qsag,
    ``qsag_verified.proofs.keccak_f1600_result_iff,
    ``qsag_verified.proofs.shake256_absorb_after_squeezing_fails,
    ``qsag_verified.proofs.shake256_absorb_ok_iff_absorbing,
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
    ``qsag_verified.proofs.inhabited_belt_one_fault_multi_epoch,
    ``qsag_verified.proofs.xor_rate_block_refines,
    ``qsag_verified.proofs.sponge_absorb_refines,
    ``qsag_verified.proofs.sponge_absorb_all_refines,
    ``qsag_verified.proofs.sponge_finalize_refines,
    ``qsag_verified.proofs.shake256_absorb_pad_refines,
    ``qsag_verified.proofs.shake256_xof_from_extracted_state,
    ``qsag_verified.proofs.sponge_squeeze32_refines,
    ``qsag_verified.proofs.sponge_squeeze_refines,
    ``qsag_verified.proofs.shake256_squeeze_refines,
    ``qsag_verified.proofs.shake256_32_refines,
    ``qsag_verified.proofs.sp800_185_left_encode_u128_refines,
    ``qsag_verified.proofs.sponge_new_cshake256_nonempty_absorbed,
    ``qsag_verified.proofs.cshake256_32_refines,
    ``qsag_verified.proofs.cshake256_squeeze_refines,
    ``qsag_verified.proofs.tooth_multiblock_squeeze_permuted_beyond_136,
    ``qsag_verified.proofs.opening_verify_once_eq,
    ``qsag_verified.proofs.opening_verify_once_single_consumption,
    ``qsag_verified.proofs.opening_round_permit_sound,
    ``qsag_verified.proofs.opening_round_permit_complete,
    ``qsag_verified.proofs.mlDsa_abort_in_place_spec,
    ``qsag_verified.proofs.mlDsa_abort_in_place_refuses_valid_checks,
    ``qsag_verified.proofs.mlDsa_try_release_into_eq_by_value,
    ``qsag_verified.proofs.mlDsa_try_release_into_postcondition,
    ``qsag_verified.proofs.mlDsaInto_extracted_step_refines,
    ``qsag_verified.proofs.extractedMlDsaInto_at_most_one_release,
    ``qsag_verified.proofs.mlDsa_try_release_into_failed_barrier_wipes_out_and_aborts]
  for name in requiredTheorems do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "MIR axiom audit missing theorem target: {name}"
  let mut checked : Nat := 0
  let mut rejected : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let owner := env.header.moduleNames[idx.toNat]!.toString
      -- Elaboration programs are not logical axioms. Their emitted declarations and
      -- every transitive dependency of a checked proof remain in the census.
      if owner.startsWith "Aeneas.Elab." &&
          (isDeclMeta env name || isDeclMeta env name.getPrefix) then continue
      if owner == "Aeneas" || owner.startsWith "Aeneas." || owner == "QsagCustodyWeld" ||
          owner == "QsagSpecWeld" || owner == "QsagMirProofs" || owner == "QsagVerified" ||
          owner.startsWith "QsagVerified." then
        checked := checked + 1
        let axioms ← withEnv env <| Lean.collectAxioms name
        let forbidden := axioms.filter fun ax => ax != ``propext && ax != ``Quot.sound
        if !forbidden.isEmpty then
          rejected := rejected + 1
          logInfo m!"REJECT {name} (module {owner}): {forbidden}"
  if checked == 0 then
    throwError "MIR axiom audit has empty coverage"
  if rejected > 0 then
    throwError "MIR axiom policy failed: {rejected} of {checked} declarations rejected"
  logInfo m!"MIR axiom audit: {checked} declarations; zero rejected (allowlist: propext, Quot.sound)"
