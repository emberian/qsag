module
/-
# Qsag.Tests.MigrationTeeth — teeth, witnesses and upstream audits for the migration modules

* Concrete `GF(2^128)` instances for the sacrifice, flush and ceremony counting theorems of
  `Protocol/Migration/ActiveMigrationZeroTest`: a mutant check that drops one test accepts a
  false claim the real check rejects, and one honest accepting run. They evaluate
  `rustGf128Mul` in the kernel, which needs the bodies of `Math/Gf2Pow128`.
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

/-- Commit order matters: for a false claim, every coin has a forging message
    when the message may be chosen after the coin. -/
theorem tooth_fold_message_after_coin_forges :
    ∃ s : IpClaim, s.err ≠ 0#128 ∧
      ∀ rk : RustGf128, ∃ m : FoldMessage, (foldRound s m rk).err = 0#128 := by
  refine ⟨⟨1, fun _ => 1#128, fun _ => 1#128, 0#128⟩, by decide +kernel, fun rk => ?_⟩
  exact ⟨_, fold_message_after_coin_cancels_defect _ rk⟩

/-- The mutant base case that keeps the length test and drops the opened
    product test. -/
def baseAcceptsWithoutProductTest (s : IpClaim) (_m : BaseMessage) (_rb : RustGf128) : Bool :=
  decide (s.len = 1)

/-- Without the product test a false claim is accepted on every coin, while
    the real base case rejects it. -/
theorem tooth_sacrifice_without_product_test_accepts_false_claim :
    ∃ (s : IpClaim) (m : BaseMessage),
      s.err ≠ 0#128 ∧
      (∀ rb : RustGf128, baseAcceptsWithoutProductTest s m rb = true) ∧
      sacrificeAccepts 0 m s [1#128] = false := by
  refine ⟨⟨1, fun _ => 1#128, fun _ => 1#128, 0#128⟩, ⟨0#128, 0#128, 0#128, 0#128⟩,
    by decide +kernel, fun _ => rfl, by decide +kernel⟩

/-- A true two-element claim is accepted through one honest fold and the
    honest base case. -/
theorem inhabited_sacrifice_accepted :
    ∃ (p : FoldProver 1) (s : IpClaim) (coins : List RustGf128),
      SacrificeAccepted 1 p s coins := by
  refine ⟨(⟨0#128, 0#128⟩, fun _ => ⟨0#128, 0#128, 0#128, 0#128⟩),
    ⟨2, fun _ => 1#128, fun _ => 1#128, 0#128⟩, [1#128, 1#128], ?_⟩
  show sacrificeAccepts 1 _ _ _ = true
  decide +kernel

/-- The mutant base case that checks lane `0` only. -/
def flushBaseAcceptsLaneZeroOnly (cl : FlushClaims) (bm : Fin 2 → Fin 64 → BaseMessage)
    (rb : CoinPair) : Bool :=
  finAll 2 (fun t => decide ((cl t 0).len = 1) && baseAccepts (cl t 0) (bm t 0) (coinAt rb t))

/-- Checking one lane lets a false claim in another lane through; the real base
    case rejects it. -/
theorem tooth_flush_single_lane_check_accepts_false_lane :
    ∃ (cl : FlushClaims) (bm : Fin 2 → Fin 64 → BaseMessage) (lane : Fin 64) (rb : CoinPair),
      (cl 0 lane).err ≠ 0#128 ∧ (cl 1 lane).err ≠ 0#128 ∧
      flushBaseAcceptsLaneZeroOnly cl bm rb = true ∧
      flushBaseAccepts cl bm rb = false := by
  refine ⟨fun _ lane => ⟨1, fun _ => 1#128, fun _ => 1#128, if lane.val = 0 then 1#128 else 0#128⟩,
    fun _ _ => ⟨0#128, 0#128, 0#128, 0#128⟩, 1, (1#128, 1#128),
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- Regression against treating Wiedemann coordinate bit-packing as the Rust polynomial basis
    (the verified conversion is `rustToTower`):
    under naive coordinate bit-packing, bit `1` (`x_0 ∈ Tower128`) squares to `x_0 + 1` (`3#128`),
    whereas in `RustGf128` bit `1` (`x`) squares to `x^2` (`4#128`). -/
theorem tooth_identity_basis_conversion_wrong :
    ∃ x : RustGf128,
      rustGf128Mul x x ≠
        wiedemannPack128 (towerMul 7 (wiedemannUnpack128 x) (wiedemannUnpack128 x)) ∧
      wiedemannUnpack128 (rustGf128Mul x x) ≠
        towerMul 7 (wiedemannUnpack128 x) (wiedemannUnpack128 x) := by
  refine ⟨2#128, ?_⟩
  have hK : towerMul 7 (wiedemannUnpack128 2#128) (wiedemannUnpack128 2#128) =
      wiedemannKaratsuba 7 (wiedemannUnpack128 2#128) (wiedemannUnpack128 2#128) :=
    (wiedemannKaratsuba_eq_towerMul 7 _ _).symm
  have hW : wiedemannPack128 (wiedemannKaratsuba 7 (wiedemannUnpack128 2#128) (wiedemannUnpack128 2#128)) = 3#128 := by
    decide
  have hR : rustGf128Mul 2#128 2#128 = 4#128 := by decide +kernel
  rw [hK]
  refine ⟨?_, ?_⟩
  · rw [hR, hW]; decide
  · intro hEq
    have hp := congrArg wiedemannPack128 hEq
    rw [hW] at hp
    have h4 : wiedemannPack128 (wiedemannUnpack128 (rustGf128Mul 2#128 2#128)) = 4#128 := by
      rw [hR]; decide
    rw [h4] at hp
    revert hp; decide

/-- The mutant ceremony gate that checks the flush of fork `0` only. -/
def ceremonyAcceptsForkZeroOnly (r : Nat) (p : CeremonyProver r) (cl : Fin 7 → FlushClaims)
    (coins : CeremonyCoins) : Bool :=
  flushAccepts r (p 0 coins) (cl 0) (coins 0)

/-- Checking one of the seven forks accepts a false repetition of another fork
    (repetition `64`, fork 1, lane 0); the seven-fork gate rejects it. -/
theorem tooth_ceremony_single_fork_check_accepts_false_repetition :
    ∃ (p : CeremonyProver 0) (cl : Fin 7 → FlushClaims) (rep : Fin 438) (coins : CeremonyCoins),
      FalseRepetition 0 p cl rep ∧
      ceremonyAcceptsForkZeroOnly 0 p cl coins = true ∧
      ceremonyAccepts 0 p cl coins = false := by
  refine ⟨fun _ _ => constFlushProver ⟨0#128, 0#128⟩ ⟨0#128, 0#128, 0#128, 0#128⟩ 0,
    fun b _ _ => ⟨1, fun _ => 1#128, fun _ => 1#128, if b.val = 0 then 1#128 else 0#128⟩,
    ⟨64, by decide⟩, fun _ => [(1#128, 1#128)],
    ⟨fun _ _ => rfl, by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩

/-- The numerator `63` is not slack: `62 / (2^128 - 1)` is below the staged count. -/
theorem tooth_rust_bit_check_numerator_62_too_small :
    ¬ (stagedBadCoinBound (2 ^ 128) ((2 ^ 128) ^ rustBitCheckHalvingRounds * (2 ^ 128 - 1))
        (sacrificeBadCoinBound (2 ^ 128) (2 ^ 128 - 1) rustBitCheckHalvingRounds)
        rustBitCheckStageNumerators * (2 ^ 128 - 1) ≤
      62 * ((2 ^ 128) ^ rustBitCheckStageNumerators.length *
        ((2 ^ 128) ^ rustBitCheckHalvingRounds * (2 ^ 128 - 1)))) := by
  decide +kernel

/-- The `D0_BITS = 16` numerator `54` does not bound the Rust geometry. -/
theorem tooth_rust_bit_check_numerator_54_too_small :
    ¬ (stagedBadCoinBound (2 ^ 128) ((2 ^ 128) ^ rustBitCheckHalvingRounds * (2 ^ 128 - 1))
        (sacrificeBadCoinBound (2 ^ 128) (2 ^ 128 - 1) rustBitCheckHalvingRounds)
        rustBitCheckStageNumerators * (2 ^ 128 - 1) ≤
      54 * ((2 ^ 128) ^ rustBitCheckStageNumerators.length *
        ((2 ^ 128) ^ rustBitCheckHalvingRounds * (2 ^ 128 - 1)))) := by
  decide +kernel

/-- The hypotheses of `staged_sacrifice_false_claim_accepting_coins_bound` are jointly
    satisfiable: a stage that leaves the claim unchanged is sound with degree `0`. -/
theorem inhabited_staged_sacrifice_hypotheses :
    ∃ (S Sb : List RustGf128) (stage : Nat → IpClaim → Unit → RustGf128 → IpClaim)
      (ds : List Nat) (s : IpClaim),
      S.Nodup ∧ Sb.Nodup ∧
      StagesSound S stage (fun s => decide (s.err ≠ 0#128)) ds ∧ s.err ≠ 0#128 :=
  ⟨[0#128, 1#128], [1#128], fun _ s _ _ => s, [0], ⟨1, fun _ => 1#128, fun _ => 1#128, 0#128⟩,
    by decide, by decide,
    ⟨fun s _ hs => by
      have h : (fun _ : RustGf128 => !decide (s.err ≠ 0#128)) = fun _ => false :=
        funext (fun _ => by rw [show decide (s.err ≠ 0#128) = true from hs]; rfl)
      show (List.filter (fun _ => !decide (s.err ≠ 0#128)) [0#128, 1#128]).length ≤ 0
      rw [h]; decide, trivial⟩,
    by decide +kernel⟩

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
  Qsag.Weierstrass.Curve.PrimeOrderGroup.smul_neg
  Qsag.Weierstrass.Curve.PrimeOrderGroup.smul_injective
  Qsag.Weierstrass.Curve.PrimeOrderGroup.smul_y_ne_zero
  Qsag.Weierstrass.Curve.PrimeOrderGroup.xonly_parity_laws
  Qsag.Weierstrass.secp7Mod43_group
  Qsag.Weierstrass.secp7Mod43_projection_coordinates
  Qsag.Weierstrass.secp256k1_checked_parameters
  Qsag.secp256k1_xonly_parity_on_curve_points

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

#verify_constructive
  Qsag.tooth_global_swPoint_nullifier_injectivity_false
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
  Qsag.Top.tooth_secp7Mod43DecodePk_rejects_offCurve_and_unreduced
  Qsag.Top.secp7Mod43_dlogSettlement_complete_refinement_witness
  Qsag.Top.tooth_dlogSettlement_xOnlyNullifier_extracts_collision
  Qsag.Top.bls381_dlogSettlement_refines_or_nullifierCollision
  Qsag.Top.bls381_compressing_nullifier_nonvacuous

#verify_inhabited
  Qsag.Top.dlogOwnership_accepted_claim_has_unique_scalar
  Qsag.Top.inhabited_dlogOwnership_accepted_claim
#verify_inhabited
  Qsag.Top.zkboo_extracted_scalar_claims_enrolled_entitlement
  Qsag.Top.inhabited_zkboo_extracted_scalar_claim
#verify_inhabited
  Qsag.Top.dlogSettlement_schedule_complete_of_injOn
  Qsag.Top.inhabited_dlogSettlement_schedule_complete

end Qsag
