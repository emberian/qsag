module
/-
# Qsag.Tests.MigrationTeeth — teeth, witnesses and upstream audits for the migration modules

* Concrete `GF(2^128)` instances for the sacrifice, flush and ceremony counting theorems of
  `Protocol/Migration/ActiveMigrationZeroTest`: a mutant check that drops one test accepts a
  false claim the real check rejects, and one honest accepting run. They are proved in the
  owning modules (listed below) and audited and paired here.
* Premise and axiom audits of the `Math/EllipticCurves` and `Math/Gf2Pow128` theorems the
  migration modules build on.
-/

public import Qsag.Top.Migration
public import Qsag.Protocol.Migration.PallasAndBlsMigration
public import Qsag.Protocol.Migration.ActiveMigrationZeroTest
public import Qsag.Math.EllipticCurves
public import Qsag.Math.Gf2Pow128
public import Qsag.Math.Primality
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

#verify_constructive
  Qsag.pallas_and_bls381_limbs_and_bit_bounds Qsag.IsPrimeMod.dvd_mul Qsag.lucasPowMod_eq_pow_mod
  Qsag.isPrime_of_lucas_pratt Qsag.checkPrattStep_sound Qsag.checkPrattDAG_sound
  Qsag.p_pallas_isPrime Qsag.q_pallas_isPrime Qsag.r_bls381_isPrime Qsag.p_bls381_isPrime
  Qsag.pallas_and_bls381_moduli_prime Qsag.orchardSpendAuthG_onCurve_and_prime_subgroup_order
  Qsag.bls381G1_onCurve_and_prime_subgroup_order
  Qsag.projEqAffine_zk_constraint_sound

namespace MigrationExecution

/-! The executed teeth and witnesses audited and paired below are proved where the bodies they run
are visible:

* `Protocol/Migration/ActiveMigrationZeroTest`: `tooth_fold_message_after_coin_forges`,
  `baseAcceptsWithoutProductTest`, `tooth_sacrifice_without_product_test_accepts_false_claim`,
  `inhabited_sacrifice_accepted`, `flushBaseAcceptsLaneZeroOnly`,
  `tooth_flush_single_lane_check_accepts_false_lane`, `ceremonyAcceptsForkZeroOnly`,
  `tooth_ceremony_single_fork_check_accepts_false_repetition`,
  `tooth_rust_bit_check_numerator_62_too_small`, `tooth_rust_bit_check_numerator_54_too_small`,
  `inhabited_staged_sacrifice_hypotheses`;
* `Math/Gf2Pow128`: `tooth_identity_basis_conversion_wrong`. -/

#verify_constructive inhabited_staged_sacrifice_hypotheses

end MigrationExecution

#tooth_pair Qsag.MigrationExecution.foldRound_false_claim_survives_at_most_two_coins vs Qsag.MigrationExecution.tooth_fold_message_after_coin_forges

#tooth_pair Qsag.MigrationExecution.recursive_sacrifice_false_claim_accepting_coins_bound vs Qsag.MigrationExecution.tooth_sacrifice_without_product_test_accepts_false_claim

#verify_inhabited Qsag.MigrationExecution.sacrifice_accepted_coins_have_round_count Qsag.MigrationExecution.inhabited_sacrifice_accepted

#tooth_pair Qsag.MigrationExecution.flush_false_lane_accepting_coins_bound vs Qsag.MigrationExecution.tooth_flush_single_lane_check_accepts_false_lane

#tooth_pair Qsag.MigrationExecution.rustToTower_mul vs Qsag.MigrationExecution.tooth_identity_basis_conversion_wrong

#verify_constructive
  Qsag.MigrationExecution.tooth_identity_basis_conversion_wrong
  Qsag.MigrationExecution.rustGf128Mul_comm
  Qsag.MigrationExecution.rustGf128Mul_assoc
  Qsag.MigrationExecution.towerToRust_mul
  Qsag.MigrationExecution.towerToRust_injective
  Qsag.MigrationExecution.towerToRust_rustToTower
  Qsag.MigrationExecution.rustToTower_towerToRust
  Qsag.MigrationExecution.rustToTower_mul
  Qsag.MigrationExecution.rustGf128Mul_eq_zero
  Qsag.MigrationExecution.tooth_fold_message_after_coin_forges
  Qsag.MigrationExecution.tooth_sacrifice_without_product_test_accepts_false_claim
  Qsag.MigrationExecution.inhabited_sacrifice_accepted

#verify_constructive
  Qsag.curve_orders_match_le_limbs_and_bounds
  Qsag.canonical_scalar_boundaries_exact
  Qsag.secpNegScalar_props
  Qsag.taproot_even_y_parity_restores_canonical_injectivity
  Qsag.clampEd25519Bytes32_bits_and_range
  Qsag.slip0010_ed25519_clamped_canonical_nonzero
  Qsag.TaprootCurveProjection.compressed_injective
  Qsag.Weierstrass.IsPrime.dvd_mul
  Qsag.Weierstrass.Curve.neg_onCurve
  Qsag.Weierstrass.neg_y_parity
  Qsag.Weierstrass.Curve.eq_or_eq_neg_of_same_x
  Qsag.Weierstrass.Curve.add_eq_none_iff_neg
  Qsag.Weierstrass.Curve.PrimeOrderGroup.smul_neg_of_groupLaws
  Qsag.Weierstrass.Curve.PrimeOrderGroup.smul_injective_of_groupLaws
  Qsag.Weierstrass.Curve.PrimeOrderGroup.smul_y_ne_zero_of_groupLaws
  Qsag.Weierstrass.Curve.PrimeOrderGroup.xonly_parity_laws_of_groupLaws
  Qsag.Weierstrass.secp7Mod43_group
  Qsag.Weierstrass.secp7Mod43_projection_coordinates
  Qsag.Weierstrass.secp256k1_checked_parameters
  Qsag.secp256k1_xonly_parity_on_curve_points_of_groupLaws

#tooth_pair Qsag.MigrationExecution.ceremony_false_repetition_accepting_coins_bound vs Qsag.MigrationExecution.tooth_ceremony_single_fork_check_accepts_false_repetition

#verify_constructive
  Qsag.MigrationExecution.tooth_flush_single_lane_check_accepts_false_lane
  Qsag.MigrationExecution.tooth_ceremony_single_fork_check_accepts_false_repetition

#verify_constructive
  Qsag.MigrationExecution.tooth_rust_bit_check_numerator_62_too_small
  Qsag.MigrationExecution.tooth_rust_bit_check_numerator_54_too_small

#tooth_pair Qsag.MigrationExecution.rust_bit_check_numerator_63_bound vs Qsag.MigrationExecution.tooth_rust_bit_check_numerator_62_too_small

#tooth_pair Qsag.MigrationExecution.rust_bit_check_numerator_63_bound vs Qsag.MigrationExecution.tooth_rust_bit_check_numerator_54_too_small

/-- `#tooth` Regression against `gpt6pro` §2A: global injectivity `SwPoint → Spec.Digest256` is
    literally `False` by constructive Pigeonhole (`SwPoint` infinite, `Digest256 = BitVec 256`). -/
theorem tooth_global_swPoint_nullifier_injectivity_false :
    ¬ ∃ deriveNullifier : SwPoint → Spec.Digest256,
        ∀ {pk₁ pk₂ : SwPoint}, deriveNullifier pk₁ = deriveNullifier pk₂ → pk₁ = pk₂ :=
  tooth_unbounded_swPoint_no_injective_bitvec 256

#verify_constructive Qsag.tooth_global_swPoint_nullifier_injectivity_false
  Qsag.CanonicalSwPk.encodeCoordNat_lt_sq
  Qsag.CanonicalSwPk.encodeCoordNat_injective
  Qsag.tooth_unbounded_swPoint_no_injective_bitvec
  Qsag.tooth_bls381_width_no_injective_bitvec256
  Qsag.PrimeSubgroup.smulCanonicalPk_toSwPoint
  Qsag.PrimeSubgroup.smulCanonicalPk_injective
  Qsag.Spec.idealMigrateMachine_unclaimed_owner_accepts_or_collision
  Qsag.Spec.idealMigrate_step_eq_idealKeyMigrate_or_collision
  Qsag.Spec.tooth_idealMigrate_colliding_nullifier_blocks_second_key
  Qsag.Top.dlogSettlement_refinement_exists
  Qsag.Top.dlogSettlement_schedule_refines_or_nullifierCollision
  Qsag.Top.dlogSettlement_schedule_complete_of_injOn
  Qsag.Top.secp7Mod43Nullifier_injective
  Qsag.Top.secp7Mod43_dlogSettlement_complete_refinement_witness
  Qsag.Top.tooth_dlogSettlement_xOnlyNullifier_extracts_collision
  Qsag.Top.tooth_dlogSettlement_xOnlyNullifier_blocks_honest_owner
  Qsag.Top.tooth_dlogSettlement_xOnlyNullifier_snapshot_collision
  Qsag.Top.bls381_dlogSettlement_refines_or_nullifierCollision_of_groupLaws
  Qsag.Top.bls381_compressing_nullifier_nonvacuous
  Qsag.Top.singleChallengeZkBoo_two_transcript_extract_or_collision
  Qsag.Top.tooth_singleChallengeZkBoo_hides_scalar
  Qsag.Top.inhabited_singleChallengeZkBoo_two_transcript_extract

#verify_inhabited
  Qsag.Top.dlogOwnership_accepted_claim_has_unique_scalar
  Qsag.Top.inhabited_dlogOwnership_accepted_claim
#verify_inhabited
  Qsag.Top.zkboo_extracted_scalar_claims_enrolled_entitlement
  Qsag.Top.inhabited_zkboo_extracted_scalar_claim
#verify_inhabited
  Qsag.Top.dlogSettlement_schedule_complete_of_injOn
  Qsag.Top.inhabited_dlogSettlement_schedule_complete
#verify_inhabited
  Qsag.Top.singleChallengeZkBoo_two_transcript_extract_or_collision
  Qsag.Top.inhabited_singleChallengeZkBoo_two_transcript_extract


#tooth_pair Qsag.Top.singleChallengeZkBoo_two_transcript_extract_or_collision vs
  Qsag.Top.tooth_singleChallengeZkBoo_hides_scalar

end Qsag
