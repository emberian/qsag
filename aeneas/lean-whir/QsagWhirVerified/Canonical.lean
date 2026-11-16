module
public import QsagWhirVerified.Proofs
public import Qsag.Exec.WhirKernels
import Qsag.Tactic.AssuranceKit
/-! Polynomial-basis MIR results transported to the canonical quartic field. -/
public section
namespace qsag_whir_verified.proofs
open Aeneas Aeneas.Std
/-- Representation map into the executable Goldilocks field. -/
def fieldAbs (x : U64) : Qsag.Goldilocks := Qsag.Goldilocks.ofNat x.val

theorem fieldAbs_add (x y : U64) :
    fieldAbs (fieldAdd x y) = Qsag.Goldilocks.add (fieldAbs x) (fieldAbs y) := by
  apply Qsag.Goldilocks.ext
  simp only [fieldAbs, Qsag.Goldilocks.ofNat_val, fieldAdd_val,
    Qsag.Goldilocks.add_val, Qsag.goldilocksPrime, Nat.mod_mod, Nat.add_mod_mod, Nat.mod_add_mod]

theorem fieldAbs_mul (x y : U64) :
    fieldAbs (fieldMul x y) = Qsag.Goldilocks.mul (fieldAbs x) (fieldAbs y) := by
  apply Qsag.Goldilocks.ext
  simp only [fieldAbs, Qsag.Goldilocks.ofNat_val, fieldMul_val,
    Qsag.Goldilocks.mul_val, Qsag.goldilocksPrime, Nat.mod_mod, Nat.mul_mod_mod, Nat.mod_mul_mod]

theorem fieldAbs_sub (x y : U64) :
    fieldAbs (fieldSub x y) = Qsag.Goldilocks.sub (fieldAbs x) (fieldAbs y) := by
  apply Qsag.Goldilocks.ext
  simp only [fieldAbs, Qsag.Goldilocks.ofNat_val, fieldSub_val,
    Qsag.Goldilocks.sub_val, Qsag.goldilocksPrime, Nat.mod_mod]
  rw [Nat.add_sub_assoc (Nat.le_of_lt (Nat.mod_lt y.val (by decide)))]
  exact (Nat.mod_add_mod _ _ _).symm

/-- Polynomial-to-tower basis map shared with `Math.QuarticExt4`, whose result is exactly
    the carrier consumed by `Exec.Aggregation.hemDuetFold`. -/
def ext4Abs (x : Ext4) : Qsag.Aggregation.GoldilocksExt4 :=
  Qsag.Math.aggOfPolynomial ⟨fieldAbs x.a, fieldAbs x.b, fieldAbs x.c, fieldAbs x.d⟩

theorem ext4Abs_add (x y : Ext4) :
    ext4Abs (extAdd x y) = Qsag.Aggregation.GoldilocksExt4.add (ext4Abs x) (ext4Abs y) := by
  simp only [ext4Abs, extAdd, fieldAbs_add, Qsag.Math.aggOfPolynomial_add]

theorem ext4Abs_sub (x y : Ext4) :
    ext4Abs (extSub x y) = Qsag.Aggregation.GoldilocksExt4.sub (ext4Abs x) (ext4Abs y) := by
  simp only [ext4Abs, extSub, fieldAbs_sub, Qsag.Math.aggOfPolynomial_sub]

theorem ext4Abs_mul (x y : Ext4) :
    ext4Abs (extMul x y) = Qsag.Aggregation.GoldilocksExt4.mul (ext4Abs x) (ext4Abs y) := by
  simp only [ext4Abs, extMul, fieldAbs_add, fieldAbs_mul, Qsag.Math.aggOfPolynomial_mul]
  simp only [Qsag.GoldilocksField.GoldilocksExt4.Ext4Poly.mul]
  rfl

/-- The extracted quartic multiplication refines the same field multiplication used by
    `Exec.Aggregation`, including the polynomial/tower limb permutation. -/
theorem ext_mul_refines_exec (x y : Ext4) :
    (ext4Abs <$> ext_mul x y) =
      .ok (Qsag.Aggregation.GoldilocksExt4.mul (ext4Abs x) (ext4Abs y)) := by
  rw [ext_mul_refines]
  change Result.ok (ext4Abs (extMul x y)) = _
  rw [ext4Abs_mul]

/-- The extracted CWYZ claim update reaches the executable aggregation runner. -/
theorem cwyz_bridge_refines_exec
    (e0 e1 e2 e3 e4 claim phi theta alpha beta : Ext4) :
    (ext4Abs <$> cwyz_bridge_claim_step e0 e1 e2 e3 e4 claim phi theta alpha beta) =
      .ok (Qsag.Exec.hemBridgeClaimStep
        (ext4Abs e0) (ext4Abs e1) (ext4Abs e2) (ext4Abs e3) (ext4Abs e4)
        (ext4Abs claim) (ext4Abs phi) (ext4Abs theta) (ext4Abs alpha) (ext4Abs beta)) := by
  rw [cwyz_bridge_claim_step_refines]
  change Result.ok (ext4Abs (cwyzBridgeValue e0 e1 e2 e3 e4 claim phi theta alpha beta)) = _
  simp only [cwyzBridgeValue.public_eqs, ext4Abs_add, ext4Abs_sub, ext4Abs_mul,
    Qsag.Exec.hemBridgeClaimStep.public_eqs]
end qsag_whir_verified.proofs

namespace qsag_whir_verified.proofs
open Aeneas Aeneas.Std

theorem ext4Abs_scale (x : Ext4) (s : U64) :
    ext4Abs (extScale x s) = Qsag.Aggregation.GoldilocksExt4.mul (ext4Abs x)
      (Qsag.Aggregation.GoldilocksExt4.embedBase (fieldAbs s)) := by
  simp only [ext4Abs, extScale, fieldAbs_mul, Qsag.Math.aggOfPolynomial_scale]

theorem fieldAbs_zero : fieldAbs 0#u64 = Qsag.Goldilocks.zero := by
  apply Qsag.Goldilocks.ext
  simp only [fieldAbs, Qsag.Goldilocks.ofNat_val, Qsag.Goldilocks.zero_val]
  rfl

theorem ext4Abs_zero : ext4Abs extZero = Qsag.Aggregation.GoldilocksExt4.zero := by
  have hz : fieldAbs (UScalar.ofNat UScalarTy.U64 0) = Qsag.Goldilocks.zero := by
    apply Qsag.Goldilocks.ext
    simp only [fieldAbs, Qsag.Goldilocks.ofNat_val, Qsag.Goldilocks.zero_val]
    rfl
  simp only [ext4Abs, extZero]
  rw [hz, Qsag.Math.aggOfPolynomial_zero]

theorem duet_fold_refines_exec (v0 v1 : Ext4) (iy it : U64) (alpha : Ext4) :
    (ext4Abs <$> duet_fold v0 v1 iy it alpha) =
      .ok (Qsag.Exec.hemDuetFold (ext4Abs v0) (ext4Abs v1)
        (fieldAbs iy) (fieldAbs it) (ext4Abs alpha)) := by
  rw [duet_refines]
  change Result.ok (ext4Abs (duetValue v0 v1 iy it alpha)) = _
  simp only [duetValue.public_eqs, ext4Abs_add, ext4Abs_sub, ext4Abs_mul, ext4Abs_scale,
    Qsag.Exec.hemDuetFold.public_eqs]

theorem hornerSpec_refines_exec (coeffs : List Ext4) (z : U64) (init : Ext4) :
    ext4Abs (hornerSpec coeffs z init) =
      Qsag.Exec.hemHorner (coeffs.map ext4Abs) (fieldAbs z) (ext4Abs init) := by
  induction coeffs with
  | nil => simp only [hornerSpec_nil, List.map_nil, Qsag.Exec.hemHorner_nil]
  | cons c rest ih =>
    simp only [hornerSpec_cons, List.map_cons, Qsag.Exec.hemHorner_cons,
      ext4Abs_add, ext4Abs_scale, ih]

theorem eval_ext4_univariate_refines_exec (coeffs : Slice Ext4) (z : U64) :
    (ext4Abs <$> eval_ext4_univariate_at_base coeffs z) =
      .ok (Qsag.Exec.hemHorner (coeffs.val.map ext4Abs) (fieldAbs z)) := by
  rw [eval_ext4_univariate_at_base_spec]
  change Result.ok (ext4Abs (hornerSpec coeffs.val z extZero)) = _
  rw [hornerSpec_refines_exec, ext4Abs_zero]
end qsag_whir_verified.proofs

namespace qsag_whir_verified.proofs
open Aeneas Aeneas.Std
/-- The supplied MIR twiddles must be the inverses computed by the executable specification;
`yy` is the square of the coset point. No assumption is made about the evaluations or challenges. -/
theorem fold_duet_affine_ext4_refines_exec
    (v0 v1 : Ext4) (iy it yy : U64) (theta alpha beta : Ext4) (x : Qsag.Goldilocks)
    (hit : fieldAbs it = Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2))
    (hiy : fieldAbs iy = Qsag.Goldilocks.mul (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2))
      (Qsag.Goldilocks.inv x))
    (hyy : fieldAbs yy = Qsag.Goldilocks.mul x x) :
    (ext4Abs <$> fold_duet_affine_ext4 v0 v1 iy it yy theta alpha beta) =
      .ok (Qsag.Exec.hemAffineDuetFold (ext4Abs v0) (ext4Abs v1) x
        (ext4Abs theta) (ext4Abs alpha) (ext4Abs beta)) := by
  rw [fold_duet_affine_ext4_spec]
  change Result.ok (ext4Abs (cwyzValue v0 v1 iy it yy theta alpha beta)) = _
  simp only [cwyzValue.public_eqs, ext4Abs_add, ext4Abs_sub, ext4Abs_mul, ext4Abs_scale,
    hit, hiy, hyy, Qsag.Exec.hemAffineDuetFold.public_eqs, Qsag.Aggregation.foldDuetExt4.public_eqs, Qsag.QuarticGoldilocks.ring_add, Qsag.QuarticGoldilocks.ring_sub, Qsag.QuarticGoldilocks.ring_mul]
end qsag_whir_verified.proofs

namespace qsag_whir_verified.proofs
open Aeneas Aeneas.Std

/-- Canonical scalar encoding used at the verifier/twiddle boundary. This does not assert
that the WHIR extraction contains an inverse implementation: its kernels accept twiddles. -/
def canonicalFieldWord (x : Qsag.Goldilocks) : U64 := ⟨BitVec.ofNat 64 x.val⟩

theorem fieldAbs_canonicalFieldWord (x : Qsag.Goldilocks) :
    fieldAbs (canonicalFieldWord x) = x := by
  apply Qsag.Goldilocks.ext
  simp only [fieldAbs, Qsag.Goldilocks.ofNat_val, canonicalFieldWord, UScalar.val,
    BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (Qsag.Goldilocks.val_lt_two_pow_64 x), Nat.mod_eq_of_lt x.isLt]

/-- The production-named extracted fold, supplied with the canonical inverses and square,
refines the canonical verifier expression without caller-supplied inverse/square equalities.
This closes the algebraic adapter obligation; inversion itself is outside this extraction. -/
theorem fold_duet_affine_ext4_canonical_twiddles
    (v0 v1 : Ext4) (x : Qsag.Goldilocks) (theta alpha beta : Ext4) :
    (ext4Abs <$> fold_duet_affine_ext4 v0 v1
      (canonicalFieldWord (Qsag.Goldilocks.mul
        (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)) (Qsag.Goldilocks.inv x)))
      (canonicalFieldWord (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)))
      (canonicalFieldWord (Qsag.Goldilocks.mul x x)) theta alpha beta) =
      .ok (Qsag.Exec.hemAffineDuetFold (ext4Abs v0) (ext4Abs v1) x
        (ext4Abs theta) (ext4Abs alpha) (ext4Abs beta)) :=
  fold_duet_affine_ext4_refines_exec v0 v1 _ _ _ theta alpha beta x
    (fieldAbs_canonicalFieldWord _) (fieldAbs_canonicalFieldWord _)
    (fieldAbs_canonicalFieldWord _)

#verify_constructive fieldAbs_canonicalFieldWord fold_duet_affine_ext4_canonical_twiddles
end qsag_whir_verified.proofs

namespace qsag_whir_verified.proofs
open Aeneas Aeneas.Std
/-- The extracted production mask is exactly the canonical WHIR mask predicate.
This statement does not identify the caller-provided word with a transcript hash. -/
theorem verify_stage_pow_mask_refines_canonical (word : U64) (bits : U32) :
    verify_stage_pow_mask word bits =
      .ok (Qsag.Aggregation.whirStagePowMask word.val bits.val) := by
  have h := verify_stage_pow_mask_mod_sound word bits
  rw [verify_stage_pow_mask_spec] at h ⊢
  simp only [Result.ok.injEq, decide_eq_true_eq] at h
  simp only [Qsag.Aggregation.whirStagePowMask.public_eqs]
  apply congrArg Result.ok
  exact decide_eq_decide.mpr h
#verify_constructive verify_stage_pow_mask_refines_canonical
end qsag_whir_verified.proofs
