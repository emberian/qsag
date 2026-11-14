module

public import QsagVerified.Proofs

public section

/-!
# Rust MIR refinement interface

This module re-exports the public specifications and proof declarations from
`QsagVerified.Proofs`. The verification document records the coverage boundary
and the Linux validation requirements for each revision.
-/

namespace QsagMirProofs

export qsag_verified.proofs (
  GoldilocksP
  bdoz_authenticate_open_total
  bdoz_authenticate_open_spec
  bdoz_mac_one_time_burn_spec
  bdoz_tampered_mac_rejected
  pureTower128Mul
  BeltAckCountInvariant
  repeatCustodianAck
  authenticated_belt_initial_count_invariant
  authenticated_belt_forged_tag_fails_closed
  authenticated_belt_duplicate_ack_unchanged
  tooth_duplicate_custodian_cannot_reach_quorum
  tower128_mul_zero
  tower128_mul_small_vectors
  tower128_mul_eq_independent
  tower128_mul_comm
  tower_basis_square_vector
  tower_basis_is_not_untranslated_artin_schreier
  bdozMaskedSum
  bdozFoldedKey
  bdozExpectedMacLanes
  bdozOpening1
  goldilocks_canon_spec
  goldilocks_add_spec
  goldilocks_sub_spec
  goldilocks_reduce128_spec
  goldilocks_mul_spec
  goldilocks_pow7_spec
  goldilocks_inv_spec
  goldilocks_inv_or_zero_spec
  tooth_goldilocks_inv_seven
  tooth_epoch_acquire_and_retry_ok
  goldilocks_inv_or_zero_total
  tower_gf256_boolean_iff_frobenius
  tower128_mul_total
  tower_gf256_inv_or_zero_spec
  pureGf256Mul
  gf256_mul_eq_pure
  pureGf256Mul_comm
  pureGf256Mul_xor_right
  pureGf256Mul_xor_left
  dkg_beaver_frobenius_eval_spec
  verify_mac_2lane_rejects_empty
  verify_mac_2lane_burn_irreversible
  rss_reconstruct_share_roundtrip
  rss_xor_homomorphic
  rss_not_spec
  tooth_dkg_inconsistent_shares_rejected
  rss_and_gate_spec
  rss_keccak_chi_lane_spec
  pureGf256Mul_zero
  pureGf256Mul_zero_left
  pureGf256Mul_one
  pureGf256Mul_assoc
  tower_gf256_field_laws
  tower_gf256_inv_spec
  pureGf256Mul_eq_zero_iff
  pureGf256Inv
  gf256_inv_or_zero_eq_pure
  pureGf256Inv_mul
  goldilocks_from_canonical_spec
  goldilocks_neg_spec
  goldilocks_ext2_add_spec
  goldilocks_ext2_mul_spec
  tower256_mul_total
  pureHornerGf256Prefix
  pureHornerGf256
  shamir_eval_poly_gf256_spec
  pureHornerGoldilocksPrefix
  pureHornerGoldilocks
  shamir_eval_poly_goldilocks_spec
  shamir_validate_points_gf256_rejects_empty
  shamir_validate_points_gf256_3_spec
  shamir_lagrange_at_zero_gf256_rejects_invalid
  keccak_f1600_round_total
  keccak_f1600_zero_state_nonconstant
  keccak_f1600_total
  ct_eq_bytes32_spec
  fips205_wots_chain_oob_none
  fips205_wots_chain_zero_steps
  tsw_canonical_target_sum_spec
  WellFormedWal
  epoch_latch_new_spec
  epoch_latch_advance_spec
  epoch_latch_advance_seals_prior_epochs
  gfSlice2
  gfSlice3
  shamir_lagrange_at_zero_gf256_2of2_spec
  shamir_lagrange_at_zero_gf256_3of3_spec
  shamir_degree_reduce_2of3_gf256_spec
  ValidPoints3
  dkg_linear_key_bit_gf256_spec
  dkg_inconsistent_reconstructions_rejected
  dkg_verify_shamir_2of3_key_bit_gf256_spec
  fips205AdrsTypeTag
  fips205_adrs_decode_encode_spec
  fips205_adrs_roundtrip_spec
  fips205_adrs_decode_invalid_type_none
  natPrefixSum
  wotsChecksumNat
  wotsBase16Digits
  wots_extract_base16_digits_spec
  wots_checksum_base16_spec
  fips205_wots_checksum_spec
  wots_checksum_strict_antitone
  fips205_f_total
  fips205_wots_chain_compose
  digitsNatSum
  tsw_check_target_sum_spec
  EpochAdvanceError
  EpochFreshError
  EpochAcquireError
  epochWitnessBytes
  epochWitnessChanged
  traceAssignedEpochs
  EpochAcquireSuccess
  epoch_latch_acquire_or_retry_spec
  epoch_latch_key_binding_mismatch
  epoch_latch_equivocation_rejected
  epoch_latch_randomizer_mismatch
  EpochTurn
  EpochTrace
  traceGrants
  epoch_latch_multiturn_safety
  tooth_goldilocks_noncanonical_rejected
  tooth_gf256_nonboolean_rejected
  tooth_shamir_duplicate_points_rejected
  tooth_adrs_invalid_type_rejected
  tooth_tsw_wrong_sum_rejected
  tooth_epoch_equivocation_rejected
  tooth_epoch_r_rand_drift_rejected
  tooth_epoch_advance_seals_retry
  MealySpec
  SpecTurn
  specAcceptedPairs
  ValidSpecTrace
  MirOutcome
  adaptResultPair
  adaptStateResult
  adaptMutResult
  adaptOptionPair
  adaptStateOption
  adaptStateBool
  adaptTuple
  MirStepSim
  MirTurn
  mirAcceptedPairs
  MirTrace
  InputsMatchTurns
  AcceptedPairsRel
  MirPhaseSim
  seqSpecPhases
  seqMirPhases
  u64_val_add_checked
  u64_val_sub_checked
  u32_val_add_checked
  uscalar_eq_iff
  u8_eq_iff
  u64_eq_iff
  result_bind_ok_split
  array32_to_list_injective
  arrayU8ToBytes
  arrayU8ToBytes_length
  arrayU8ToBytes_injective
  tooth_u64_val_add_checked_overflow_refused
  tooth_quarantine_errStep_blocks_subsequent_accept
  compute_rss_mask_commitment_total
  rssCutMealy
  rss_cut_step_sim
  rssCutTraceSafe
  rss_cut_session_never_releases_unverified_cut
  tooth_rss_cut_skip_round3_poisoned
  tooth_rss_cut_nonzero_mac_poisoned
  tooth_rss_cut_replay_open_poisoned
  FtsEpochConsumeReq
  mirFtsEpochStep
  ftsEpochMealy
  fts_epoch_step_sim
  fts_guard_at_most_one_sig_per_epoch
  u8DigitsNatSum
  wots_cs_verify_68_w5_sum136_spec
  wots_cs_verify_68_array_spec
  wots_cs_68_sum136_incomparable_mir
  FtsMacStepInput
  FtsMacStepOutput
  wotsCsValidBool
  mirFtsMacStep
  ftsMacMealy
  fts_mac_step_sim
  ftsMacTraceSafe
  fts_spn_output_implies_intermediate_mac_ok
  tooth_fts_second_epoch_burn_rejected
  tooth_fts_unverified_mac_release_quarantined
  tooth_wots_cs_68_wrong_sum_rejected
  u128AmountsNatSum
  velocitySpendStep
  velocitySpendMealy
  velocity_spend_step_sim
  policy_velocity_guard_multiturn_cap_sound
  rotate_window_resets_spent_monotone_spec
  intent_codec_roundtrip_injective_mir
  hybridDomainMagic14
  hybridRoleByte
  check_hybrid_domain_framing_spec
  hybrid_domain_framing_role_disjoint_mir
  derive_hybrid_transcript_digest_total
  tooth_policy_cap_exceeded_rejected
  tooth_policy_u128_overflow_rejected
  tooth_intent_bad_magic_rejected
  tooth_hybrid_role_confusion_rejected
  mldsa44_eta2_nibble_uniform_spec
  check_mldsa44_norm_bounds_spec
  check_mldsa65_norm_bounds_spec
  mlDsaBarrierPassBool
  mlDsaGateMealy
  mldsa_gate_step_sim
  mldsa_gate_blocks_z_on_rejection_mir
  toprf_majority_corrects_any_single_fault_mir
  HdZeroStepInput
  HdZeroStepOutput
  mirHdZeroStep
  hdZeroMealy
  hd_zero_step_sim
  hdTraceSafe
  hd_zero_test_quarantine_mir
  tooth_mldsa_r0_norm_fail_blocks_z
  tooth_toprf_noncanonical_unanimous_rejected
  tooth_hd_premature_open_quarantined
  tooth_hd_nonzero_sum_quarantined
  ValidBeltQuorumConfigProp
  validate_belt_quorum_config_eq
  validate_belt_quorum_config_spec
  beltQuorumMealy
  belt_quorum_step_sim
  belt_poisoned_blocks_all_future_mir
  belt_quorum_guard_multiturn_sound
  belt_propose_bounded_jump_spec
  pureWotsC256Digit
  pureWotsC256Digits
  wotsc256_extract_digit_spec
  pureWotsC256Digits_sum_eq_prefix
  verified_wotsc256_verify_sum_eq
  verified_wotsc256_verify_sum_spec
  verified_wotsc256_extract_digits_spec
  wotsc256_guard_from_digest_spec
  wotsc256_128_sum192_incomparable_mir
  rssPoisonMealy
  rss_poison_latch_step_sim
  rss_poison_latch_failed_check_permanently_blocks_open_mir
  rss_poison_latch_multiturn_sound
  waistbandRootMealy
  waistband_root_guard_step_sim
  waistband_root_guard_multiturn_sound
  waistband_mismatch_fails_closed_mir
  tooth_belt_under_threshold_quorum_rejected
  tooth_belt_wal_and_conflict_poison
  inhabited_belt_quorum_trace
  tooth_wotsc256_wrong_sum_rejected_and_inhabited
  tooth_rss_failed_check_then_true_check_blocks_open
  inhabited_rss_poison_latch_trace
  tooth_waistband_corrupted_root_and_second_codeword_fail_closed
)

open Aeneas Aeneas.Std

example : GoldilocksP = 2^64 - 2^32 + 1 := rfl
example : digitsNatSum [3#u32, 4#u32] = 7 := rfl
example : traceGrants [] = [] := rfl

example : (traceAssignedEpochs
    [.advance ⟨0#u64, epochWitnessBytes⟩ (.Ok 0#u64)]).Pairwise (fun a b => a ≠ b) := by
  let initial : qsag_verified.threshold.EpochLatch := ⟨0#u64, 4#u64, epochWitnessBytes, .Unset⟩
  let final : qsag_verified.threshold.EpochLatch := ⟨1#u64, 4#u64, epochWitnessBytes, .Unset⟩
  have step : qsag_verified.threshold.epoch_latch_advance initial ⟨0#u64, epochWitnessBytes⟩ =
      .ok (.Ok (final, 0#u64)) := by
    simp [qsag_verified.threshold.epoch_latch_advance, initial, final, ct_eq_bytes32_spec, UScalar.val, UScalarTy.numBits]
  exact (epoch_latch_multiturn_safety 4#u64 epochWitnessBytes initial final _ rfl
    (.advance_ok step (.nil final))).2.2.2.2.1

end QsagMirProofs
