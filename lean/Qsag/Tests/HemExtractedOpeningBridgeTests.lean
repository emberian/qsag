module
public import Qsag.Math.GoldilocksBase
public import Qsag.Protocol.Aggregation.QromSaltedMerkleStateRestoration
/- Executed, nonconstant decoder consuming openings and the actual Hem checker. -/
public import Qsag.Protocol.Aggregation.HemOpening
public import Qsag.Tests.OracleAndQrom
public import Qsag.Oracle.Qrom
public import Qsag.Protocol.Aggregation.MultiRoundFsQrom
public import Qsag.Protocol.Aggregation.HemRbrSoundness
public import Qsag.Protocol.Aggregation.ConcreteSecurityBudget
public import Qsag.Coding.Cwyz26
public import Qsag.Coding.GuruswamiSudan
public import Qsag.Coding.ReedSolomon
public import Qsag.Math.Counting
public import Qsag.Math.CoeffPoly
public import Qsag.Math.PolyRing
public import Qsag.Math.QuarticExt4
public import Qsag.Math.Goldilocks
public import Qsag.Math.Primality

public section
namespace Qsag
set_option autoImplicit false

-- The toy substitution fixtures and executed facts (`toyHemDecode`, `toyHemInstance`,
-- `toy_hem_substitution_execution`, `toy_hem_substitution_bound_instance`, `toyHemInstance_invalid`) are
-- proved in `Protocol/Aggregation/HemOpening`; `toyOpeningSlots` and `toy_batch_duplicate_execution` in
-- `Oracle/Qrom`.

#verify_constructive
  Qsag.toy_hem_substitution_execution
  Qsag.toy_batch_duplicate_execution
  Qsag.toy_hem_substitution_bound_instance
  Qsag.toyHemInstance_invalid
end Qsag
end

public section
namespace Qsag

-- `unsaltedFourAddressCanopy` and `tooth_unsalted_canopy_preprocessed_collision` are proved in
-- `Protocol/Aggregation/QromSaltedMerkleStateRestoration`, and paired there with
-- `saltedCanopy_fresh_salt_preprocessed_bound` (the shared `SaltedCanopyLayout.levels` sits under the
-- sealed `SaltedCanopyLayout.atSalt`).
#verify_constructive tooth_unsalted_canopy_preprocessed_collision
end Qsag
end

/-
Fixtures, teeth and inhabitation witnesses of `Protocol/Aggregation/HemOpening.lean`. Each one
evaluates the concrete Hem checker, the Guruswami–Sudan decoder or the deployed tables over
`QuarticGoldilocks` in the kernel, so it needs the bodies of those definitions.
-/

public section
namespace Qsag
set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxRecDepth 65536

#verify_constructive
  Qsag.tooth_missing_batch_claim_erases_oracle
  Qsag.tooth_core_agreement_is_stronger_than_checker
  Qsag.hemZeroOracle_acceptance_nontrivial

/-- The fixed-theta invalid-mixture premise cannot be dropped: two identical zero words
    with false claim one have a valid zero claim after theta=-1 mixing. This is a witness
    to the need for a theta-exception argument, not a counterexample to a bounded lift. -/
theorem tooth_equal_degree_invalid_mixture :
    let D : List QuarticGoldilocks := [CommRingOps.zero, CommRingOps.one]
    (∀ P : List QuarticGoldilocks,
      polyWitnessValid D 2 0 (fun _ => CommRingOps.zero) [CommRingOps.one] CommRingOps.one P = false) ∧
    polyWitnessValid D 2 0
      (fun _ => CommRingOps.add CommRingOps.zero
        (CommRingOps.mul (CommRingOps.sub CommRingOps.zero CommRingOps.one) CommRingOps.zero))
      [CommRingOps.one]
      (CommRingOps.add CommRingOps.one
        (CommRingOps.mul (CommRingOps.sub CommRingOps.zero CommRingOps.one) CommRingOps.one)) [] = true := by
  refine ⟨?_, polyWitnessValid_theta_neg_one_mixture_kat⟩
  intro P
  cases hv : polyWitnessValid [CommRingOps.zero, CommRingOps.one] 2 0
      (fun _ => (CommRingOps.zero : QuarticGoldilocks)) [CommRingOps.one] CommRingOps.one P with
  | false => rfl
  | true =>
    have h0 := polyWitnessValid_zeroOracle_claim [CommRingOps.zero, CommRingOps.one] 0 2
      [CommRingOps.one] P CommRingOps.one (by decide) (by decide) hv
    exact False.elim ((by decide : (CommRingOps.one : QuarticGoldilocks) ≠ CommRingOps.zero) h0)

#verify_constructive
  Qsag.tooth_equal_degree_invalid_mixture
  Qsag.tooth_sliced_nv24_profile_margin


-- `batchMerkleFailure_inhabited_256` is proved in `Oracle/Qrom` (it unfolds the measured-failure predicate).
#verify_constructive batchMerkleFailure_inhabited_256

/-! ## §4. Non-Vacuity Inhabitedness Witnesses & Assurance Gates -/

#tooth_pair Qsag.hemNextMinAgree_increments vs Qsag.tooth_incremented_cascade_rejects_old_attack
#verify_inhabited cdhz_recursive_sliced_stage_clears_128bits_at_2pow50 witness_cdhz_sliced_stage_clears_128bits_at_2pow50

#tooth_pair Qsag.equal_degree_three_challenge_bound Qsag.tooth_equal_degree_drop_theta_exception_unsound
#tooth_pair Qsag.arbitrary_batch_cascade_fiber_bound Qsag.tooth_verifyHemAffineWhir_unincremented_agree_accepts_all
#tooth_pair Qsag.arbitrary_batch_incremented_cascade_fiber_bound Qsag.tooth_verifyHemAffineWhir_unincremented_agree_accepts_all
#tooth_pair Qsag.cdhz_sliced_stage_clears_128bits_at_2pow50 Qsag.tooth_dfmRoundScale_fails_128bits_at_2pow50

#verify_inhabited Qsag.equal_degree_three_challenge_bound Qsag.witness_equal_degree_three_challenge_bound
#verify_inhabited Qsag.arbitrary_batch_cascade_fiber_bound Qsag.witness_arbitrary_batch_cascade_fiber_bound
#verify_inhabited Qsag.cdhz_sliced_stage_clears_128bits_at_2pow50 Qsag.witness_cdhz_sliced_stage_clears_128bits_at_2pow50

#verify_constructive
  Qsag.tooth_equal_degree_drop_theta_exception_unsound
  Qsag.tooth_verifyHemAffineWhir_unincremented_agree_accepts_all
  Qsag.tooth_dfmRoundScale_fails_128bits_at_2pow50

end Qsag
end
