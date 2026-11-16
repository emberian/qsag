module
public import QsagWhirVerified.Proofs
public import Qsag.Exec.WhirKernels
public import Qsag.Exec.Tactic.SimulationKit
public import Qsag.Protocol.Aggregation.HemRbrSoundness
import Qsag.Tactic.AssuranceKit
/-!
# Canonical `Qsag` soundness and refinement welds for `qsag-whir-verified`

Transports the polynomial-basis MIR functions and refinement theorems in
`QsagWhirVerified.{Arithmetic,Proofs}` directly to the canonical `Qsag` mathematical
and protocol specifications in `Qsag.Math.QuarticExt4`, `Qsag.Protocol.Aggregation.Aggregation`,
`Qsag.Protocol.Aggregation.MultiRoundFsQrom`, `Qsag.Protocol.Aggregation.HemRbrSoundness`,
and `Qsag.Exec.WhirKernels`:

1. **Field & Quartic Extension Isomorphism (`fieldAbs`, `ext4Abs`, `canonicalExt4`, `extInv`):**
   Homomorphisms for `+`, `-`, `*`, scalar scaling, `0`, `1`, and multiplicative inversion `inv`,
   together with canonical inverse twiddle discharge (`canonicalFieldWord_two_inv`,
   `canonicalFieldWord_two_x_inv`, `embedBase_inv`).
2. **Canonical Wire Decoding (`decode_canonical_u64`, `decode_canonical_ext4`):**
   Exact refinement to `Qsag.Goldilocks` and `Qsag.Aggregation.GoldilocksExt4` (`aggOfPolynomial`).
3. **Production WHIR Fold Gates (`fold_duet_affine_ext4`, `verify_cwyz_duet_fold_step`,
   `verify_affine_duet_fold_step`):**
   Direct soundness welds into `Qsag.hemVirtualFoldOracle`, `Qsag.Exec.hemAffineDuetFold`,
   `Qsag.Exec.hemDuetFold`, and `Qsag.Aggregation.ext4_poly_roots_le_degree`.
4. **CWYZ Dual Bridge, Cascade & Quadratic Sumcheck Wire (`verify_cwyz_bridge_claim_step`,
   `affine_cascade_claim_step`, `eval_quadratic_sumcheck_wire`):**
   Direct welds into `Qsag.hemBridgeFoldClaim`, `Qsag.evalCascadeClaim`, and
   `Qsag.hemSumcheck_polynomial_collision_count`.
5. **Horner & Polynomial Pinning (`eval_ext4_univariate_at_base`,
   `verify_ext4_univariate_at_base_pin`):**
   Direct welds into `Qsag.RoundPoly.evalCoeffs` and `Qsag.Aggregation.whir_ood_pin_roots_le_degree`.
6. **OOD-Pin (`verify_ood_pin_eq`), Stage PoW (`verify_stage_pow_mask`), Merkle Pair Order
   (`step_merkle_pair_order`), & Quorum Sum (`checked_quorum_sum`):**
   Direct welds into canonical `GoldilocksExt4` OOD limb slices, `Qsag.Aggregation.whirStagePowMask` /
   `Qsag.Aggregation.verifyWhirStagePow`, canonical Merkle parity framing, and overflow-free quorum
   summation, paired with `#tooth` mutation-sensitivity witnesses.
-/

public section
namespace qsag_whir_verified.proofs
open Aeneas Aeneas.Std

/-! ## 0. Private Ring Dictionary Bridges (Respecting `LAW-M1` Encapsulation) -/

private theorem agg_embedBase (a : Qsag.Goldilocks) :
    Qsag.Aggregation.GoldilocksExt4.embedBase a =
      Qsag.GoldilocksField.GoldilocksExt4.embedBase a := rfl

private theorem agg_add (x y : Qsag.Aggregation.GoldilocksExt4) :
    Qsag.Aggregation.GoldilocksExt4.add x y = Qsag.QuarticGoldilocks.add x y := rfl

private theorem agg_sub (x y : Qsag.Aggregation.GoldilocksExt4) :
    Qsag.Aggregation.GoldilocksExt4.sub x y = Qsag.QuarticGoldilocks.sub x y := rfl

private theorem agg_mul (x y : Qsag.Aggregation.GoldilocksExt4) :
    Qsag.Aggregation.GoldilocksExt4.mul x y = Qsag.QuarticGoldilocks.mul x y := rfl

private theorem gf_embedBase (a : Qsag.Goldilocks) :
    Qsag.GoldilocksExt4.embedBase a =
      Qsag.GoldilocksField.GoldilocksExt4.embedBase a := rfl

private theorem quartic_ring_zero :
    (Qsag.CommRingOps.zero : Qsag.Aggregation.GoldilocksExt4) =
      Qsag.Aggregation.GoldilocksExt4.zero :=
  Qsag.GoldilocksField.GoldilocksExt4.zero_eq_ringZero.symm

private theorem quartic_ring_one :
    (Qsag.CommRingOps.one : Qsag.Aggregation.GoldilocksExt4) =
      Qsag.Aggregation.GoldilocksExt4.one :=
  Qsag.GoldilocksField.GoldilocksExt4.one_eq_ringOne.symm

private theorem embedBase_eq_aggOfPoly (a : Qsag.Goldilocks) :
    Qsag.GoldilocksField.GoldilocksExt4.embedBase a =
      Qsag.Math.aggOfPolynomial ⟨a, Qsag.Goldilocks.zero, Qsag.Goldilocks.zero, Qsag.Goldilocks.zero⟩ := by
  simp only [Qsag.GoldilocksField.GoldilocksExt4.embedBase,
    Qsag.QuarticGoldilocks.ofExt2, Qsag.GoldilocksExt2.ofBase,
    Qsag.Goldilocks.ring_zero, Qsag.GoldilocksExt2.ring_zero,
    Qsag.GoldilocksExt2.zero, Qsag.Math.aggOfPolynomial]

private theorem goldilocks_ring_add (a b : Qsag.Goldilocks) :
    Qsag.CommRingOps.add a b = Qsag.Goldilocks.add a b := by
  have h1 := Qsag.GoldilocksField.GoldilocksExt4.embedBase_add a b
  rw [Qsag.QuarticGoldilocks.ring_add, ← agg_add, embedBase_eq_aggOfPoly a, embedBase_eq_aggOfPoly b,
    Qsag.Math.aggOfPolynomial_add] at h1
  have h2 := congrArg (fun z : Qsag.QuarticGoldilocks => z.c0.c0) h1
  simpa only [Qsag.GoldilocksField.GoldilocksExt4.embedBase_c0_c0, Qsag.Math.aggOfPolynomial] using h2

private theorem goldilocks_ring_sub (a b : Qsag.Goldilocks) :
    Qsag.CommRingOps.sub a b = Qsag.Goldilocks.sub a b := by
  have h1 := Qsag.GoldilocksField.GoldilocksExt4.embedBase_sub a b
  rw [Qsag.QuarticGoldilocks.ring_sub, ← agg_sub, embedBase_eq_aggOfPoly a, embedBase_eq_aggOfPoly b,
    Qsag.Math.aggOfPolynomial_sub] at h1
  have h2 := congrArg (fun z : Qsag.QuarticGoldilocks => z.c0.c0) h1
  simpa only [Qsag.GoldilocksField.GoldilocksExt4.embedBase_c0_c0, Qsag.Math.aggOfPolynomial] using h2

private theorem goldilocks_ring_mul (a b : Qsag.Goldilocks) :
    Qsag.CommRingOps.mul a b = Qsag.Goldilocks.mul a b := by
  have h1 := Qsag.GoldilocksField.GoldilocksExt4.embedBase_mul a b
  have hs := Qsag.Math.aggOfPolynomial_scale
    ⟨a, Qsag.Goldilocks.zero, Qsag.Goldilocks.zero, Qsag.Goldilocks.zero⟩ b
  rw [agg_embedBase] at hs
  rw [Qsag.QuarticGoldilocks.ring_mul, ← agg_mul, embedBase_eq_aggOfPoly a, hs] at h1
  have h2 := congrArg (fun z : Qsag.QuarticGoldilocks => z.c0.c0) h1
  simpa only [Qsag.GoldilocksField.GoldilocksExt4.embedBase_c0_c0, Qsag.Math.aggOfPolynomial] using h2

/-! ## 1. Field & Quartic Extension Homomorphisms (`fieldAbs`, `ext4Abs`, `canonicalExt4`, `extInv`) -/

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
    the carrier consumed by `Exec.WhirKernels` and `Protocol.Aggregation`. -/
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
    `Protocol.Aggregation`, including the polynomial/tower limb permutation. -/
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

theorem ext4Abs_scale (x : Ext4) (s : U64) :
    ext4Abs (extScale x s) = Qsag.Aggregation.GoldilocksExt4.mul (ext4Abs x)
      (Qsag.Aggregation.GoldilocksExt4.embedBase (fieldAbs s)) := by
  simp only [ext4Abs, extScale, fieldAbs_mul, Qsag.Math.aggOfPolynomial_scale]

theorem fieldAbs_zero : fieldAbs 0#u64 = Qsag.Goldilocks.zero := by
  apply Qsag.Goldilocks.ext
  simp only [fieldAbs, Qsag.Goldilocks.ofNat_val, Qsag.Goldilocks.zero_val]
  rfl

theorem fieldAbs_one : fieldAbs 1#u64 = Qsag.Goldilocks.one := by
  apply Qsag.Goldilocks.ext
  simp only [fieldAbs, Qsag.Goldilocks.ofNat_val, Qsag.Goldilocks.one_val]
  rfl

theorem ext4Abs_zero : ext4Abs extZero = Qsag.Aggregation.GoldilocksExt4.zero := by
  have hz : fieldAbs (UScalar.ofNat UScalarTy.U64 0) = Qsag.Goldilocks.zero := by
    apply Qsag.Goldilocks.ext
    simp only [fieldAbs, Qsag.Goldilocks.ofNat_val, Qsag.Goldilocks.zero_val]
    rfl
  simp only [ext4Abs, extZero]
  rw [hz, Qsag.Math.aggOfPolynomial_zero]

theorem ext4Abs_one : ext4Abs extOne = Qsag.Aggregation.GoldilocksExt4.one := by
  have h0 : fieldAbs 0#u64 = Qsag.Goldilocks.zero := fieldAbs_zero
  have h1 : fieldAbs 1#u64 = Qsag.Goldilocks.one := fieldAbs_one
  change Qsag.Math.aggOfPolynomial _ = Qsag.QuarticGoldilocks.one
  simp only [extOne, h0, h1, Qsag.Math.aggOfPolynomial, Qsag.QuarticGoldilocks.one,
    Qsag.GoldilocksExt2.ring_zero, Qsag.GoldilocksExt2.ring_one,
    Qsag.GoldilocksExt2.zero, Qsag.GoldilocksExt2.one,
    Qsag.Goldilocks.ring_zero, Qsag.Goldilocks.ring_one]

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
    hit, hiy, hyy, Qsag.Exec.hemAffineDuetFold.public_eqs,
    Qsag.Aggregation.foldDuetExt4.public_eqs, Qsag.QuarticGoldilocks.ring_add,
    Qsag.QuarticGoldilocks.ring_sub, Qsag.QuarticGoldilocks.ring_mul]

/-- Canonical scalar encoding used at the verifier/twiddle boundary. -/
def canonicalFieldWord (x : Qsag.Goldilocks) : U64 := ⟨BitVec.ofNat 64 x.val⟩

theorem canonicalFieldWord_val (x : Qsag.Goldilocks) :
    (canonicalFieldWord x).val = x.val := by
  simp only [canonicalFieldWord, UScalar.val, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Qsag.Goldilocks.val_lt_two_pow_64 x)

theorem isCanonical_canonicalFieldWord (x : Qsag.Goldilocks) :
    IsCanonical (canonicalFieldWord x) := by
  rw [IsCanonical, canonicalFieldWord_val]
  exact x.isLt

theorem fieldAbs_canonicalFieldWord (x : Qsag.Goldilocks) :
    fieldAbs (canonicalFieldWord x) = x := by
  apply Qsag.Goldilocks.ext
  rw [fieldAbs, Qsag.Goldilocks.ofNat_val, canonicalFieldWord_val, Nat.mod_eq_of_lt x.isLt]

theorem canonicalFieldWord_fieldAbs {x : U64} (hx : IsCanonical x) :
    canonicalFieldWord (fieldAbs x) = x := by
  apply UScalar.eq_of_val_eq
  rw [canonicalFieldWord_val, fieldAbs, Qsag.Goldilocks.ofNat_val]
  exact Nat.mod_eq_of_lt hx

theorem fieldAbs_inj {x y : U64} (hx : IsCanonical x) (hy : IsCanonical y) :
    fieldAbs x = fieldAbs y ↔ x = y := by
  constructor
  · intro h
    rw [← canonicalFieldWord_fieldAbs hx, h, canonicalFieldWord_fieldAbs hy]
  · exact congrArg fieldAbs

/-- Canonical polynomial-basis `Ext4` encoding of a canonical `GoldilocksExt4` tower element
    (inverse of `ext4Abs` under the `[0, 2, 1, 3]` limb bijection). -/
def canonicalExt4 (z : Qsag.Aggregation.GoldilocksExt4) : Ext4 :=
  ⟨canonicalFieldWord z.c0.c0, canonicalFieldWord z.c1.c0,
   canonicalFieldWord z.c0.c1, canonicalFieldWord z.c1.c1⟩

theorem isCanonicalExt4_canonicalExt4 (z : Qsag.Aggregation.GoldilocksExt4) :
    IsCanonicalExt4 (canonicalExt4 z) :=
  ⟨isCanonical_canonicalFieldWord _, isCanonical_canonicalFieldWord _,
   isCanonical_canonicalFieldWord _, isCanonical_canonicalFieldWord _⟩

theorem ext4Abs_canonicalExt4 (z : Qsag.Aggregation.GoldilocksExt4) :
    ext4Abs (canonicalExt4 z) = z := by
  cases z with
  | mk c0 c1 =>
    cases c0
    cases c1
    simp only [ext4Abs, canonicalExt4, fieldAbs_canonicalFieldWord]

theorem canonicalExt4_ext4Abs {x : Ext4} (hx : IsCanonicalExt4 x) :
    canonicalExt4 (ext4Abs x) = x := by
  rcases hx with ⟨ha, hb, hc, hd⟩
  cases x
  simp only [ext4Abs, canonicalExt4, Qsag.Math.aggOfPolynomial,
    canonicalFieldWord_fieldAbs ha, canonicalFieldWord_fieldAbs hb,
    canonicalFieldWord_fieldAbs hc, canonicalFieldWord_fieldAbs hd]

theorem ext4Abs_inj {x y : Ext4} (hx : IsCanonicalExt4 x) (hy : IsCanonicalExt4 y) :
    ext4Abs x = ext4Abs y ↔ x = y := by
  constructor
  · intro h
    rw [← canonicalExt4_ext4Abs hx, h, canonicalExt4_ext4Abs hy]
  · exact congrArg ext4Abs

/-- Canonical multiplicative inverse on MIR `Ext4`, transported from `QuarticGoldilocks.inv`. -/
def extInv (x : Ext4) : Ext4 :=
  canonicalExt4 (Qsag.Aggregation.GoldilocksExt4.inv (ext4Abs x))

theorem isCanonicalExt4_extInv (x : Ext4) : IsCanonicalExt4 (extInv x) :=
  isCanonicalExt4_canonicalExt4 _

theorem ext4Abs_inv (x : Ext4) :
    ext4Abs (extInv x) = Qsag.Aggregation.GoldilocksExt4.inv (ext4Abs x) :=
  ext4Abs_canonicalExt4 _

private theorem isCanonicalExt4_extMul (x y : Ext4) : IsCanonicalExt4 (extMul x y) := by
  simp only [extMul]
  exact ⟨fieldAdd_canonical _ _, fieldAdd_canonical _ _,
    fieldAdd_canonical _ _, fieldAdd_canonical _ _⟩

private theorem isCanonicalExt4_extOne : IsCanonicalExt4 extOne := by
  unfold extOne IsCanonicalExt4 IsCanonical
  exact ⟨by decide, by decide, by decide, by decide⟩

/-- Extracted `ext_mul` cancels `extInv` to `extOne` for every nonzero quartic field element. -/
theorem ext_mul_extInv_ok_one {x : Ext4}
    (hz : ext4Abs x ≠ Qsag.Aggregation.GoldilocksExt4.zero) :
    ext_mul x (extInv x) = .ok extOne := by
  rw [ext_mul_refines]
  congr 1
  apply (ext4Abs_inj (isCanonicalExt4_extMul x (extInv x)) isCanonicalExt4_extOne).mp
  rw [ext4Abs_mul, ext4Abs_inv, ext4Abs_one]
  have hc := Qsag.Aggregation.goldilocksExt4_mul_inv_cancel hz
  rw [Qsag.QuarticGoldilocks.ring_mul, quartic_ring_one] at hc
  exact hc

/-- Canonical discharge of the `hit : fieldMul 2#u64 it = 1#u64` twiddle premise. -/
theorem canonicalFieldWord_two_inv :
    fieldMul 2#u64 (canonicalFieldWord (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2))) = 1#u64 := by
  apply (fieldAbs_inj (fieldMul_canonical _ _) (by decide : IsCanonical 1#u64)).mp
  rw [fieldAbs_mul, fieldAbs_canonicalFieldWord, fieldAbs_one]
  have h2 : fieldAbs 2#u64 = Qsag.Goldilocks.ofNat 2 := rfl
  rw [h2, ← goldilocks_ring_mul, ← Qsag.Goldilocks.ring_one]
  have hnz : Qsag.Goldilocks.ofNat 2 ≠ Qsag.Goldilocks.zero := by decide
  exact Qsag.Goldilocks.mul_inv_cancel hnz

/-- Canonical discharge of the `hiy : fieldMul (fieldMul 2#u64 y0) iy = 1#u64` coset-twiddle premise
    for every nonzero coset point `x ∈ F_p^*`. -/
theorem canonicalFieldWord_two_x_inv {x : Qsag.Goldilocks} (hx : x ≠ Qsag.Goldilocks.zero) :
    fieldMul (fieldMul 2#u64 (canonicalFieldWord x))
      (canonicalFieldWord (Qsag.Goldilocks.mul
        (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)) (Qsag.Goldilocks.inv x))) = 1#u64 := by
  apply (fieldAbs_inj (fieldMul_canonical _ _) (by decide : IsCanonical 1#u64)).mp
  rw [fieldAbs_mul, fieldAbs_mul, fieldAbs_canonicalFieldWord, fieldAbs_canonicalFieldWord,
    fieldAbs_one]
  have h2 : fieldAbs 2#u64 = Qsag.Goldilocks.ofNat 2 := rfl
  rw [h2, ← goldilocks_ring_mul, ← goldilocks_ring_mul, ← goldilocks_ring_mul,
    ← Qsag.Goldilocks.ring_one]
  have h2nz : Qsag.Goldilocks.ofNat 2 ≠ Qsag.Goldilocks.zero := by decide
  have hc1 := Qsag.Goldilocks.mul_inv_cancel h2nz
  have hc2 := Qsag.Goldilocks.mul_inv_cancel hx
  calc
    Qsag.CommRingOps.mul (Qsag.CommRingOps.mul (Qsag.Goldilocks.ofNat 2) x)
        (Qsag.CommRingOps.mul (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)) (Qsag.Goldilocks.inv x))
      = Qsag.CommRingOps.mul
          (Qsag.CommRingOps.mul (Qsag.Goldilocks.ofNat 2)
            (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)))
          (Qsag.CommRingOps.mul x (Qsag.Goldilocks.inv x)) := by constructive_ring
    _ = Qsag.CommRingOps.mul Qsag.CommRingOps.one Qsag.CommRingOps.one := by rw [hc1, hc2]
    _ = Qsag.CommRingOps.one := Qsag.LawfulCommRing.one_mul _

/-- The production-named extracted fold, supplied with the canonical inverses and square,
refines the canonical verifier expression without caller-supplied inverse/square equalities. -/
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

/-! ## 2. Canonical Wire Decoding Welds (`decode_canonical_u64`, `decode_canonical_ext4`) -/

theorem decode_canonical_u64_refines_qsag (x : U64) :
    (Option.map fieldAbs <$> decode_canonical_u64 x) =
      .ok (if x.val < Qsag.goldilocksPrime then some (Qsag.Goldilocks.ofNat x.val) else none) := by
  rw [decode_canonical_u64_spec]
  change Result.ok (Option.map fieldAbs (if x.val < goldilocksMod then some x else none)) = _
  have hp : goldilocksMod = Qsag.goldilocksPrime := rfl
  rw [hp]
  by_cases h : x.val < Qsag.goldilocksPrime <;> simp [h, fieldAbs]

theorem decode_canonical_ext4_refines_qsag (a b c d : U64) :
    (Option.map ext4Abs <$> decode_canonical_ext4 a b c d) =
      .ok (if a.val < Qsag.goldilocksPrime ∧ b.val < Qsag.goldilocksPrime ∧
              c.val < Qsag.goldilocksPrime ∧ d.val < Qsag.goldilocksPrime
           then some (Qsag.Math.aggOfPolynomial ⟨fieldAbs a, fieldAbs b, fieldAbs c, fieldAbs d⟩)
           else none) := by
  rw [decode_canonical_ext4_spec]
  change Result.ok (Option.map ext4Abs
    (if IsCanonical a ∧ IsCanonical b ∧ IsCanonical c ∧ IsCanonical d
     then some ⟨a, b, c, d⟩ else none)) = _
  have hp : IsCanonical a ∧ IsCanonical b ∧ IsCanonical c ∧ IsCanonical d ↔
      a.val < Qsag.goldilocksPrime ∧ b.val < Qsag.goldilocksPrime ∧
      c.val < Qsag.goldilocksPrime ∧ d.val < Qsag.goldilocksPrime := Iff.rfl
  by_cases h : IsCanonical a ∧ IsCanonical b ∧ IsCanonical c ∧ IsCanonical d
  · have h' := hp.mp h
    simp [h, h', ext4Abs]
  · have h' : ¬ (a.val < Qsag.goldilocksPrime ∧ b.val < Qsag.goldilocksPrime ∧
        c.val < Qsag.goldilocksPrime ∧ d.val < Qsag.goldilocksPrime) := fun hc => h (hp.mpr hc)
    simp [h, h']

theorem decode_canonical_ext4_canonicalExt4 (z : Qsag.Aggregation.GoldilocksExt4) :
    decode_canonical_ext4
      (canonicalFieldWord z.c0.c0) (canonicalFieldWord z.c1.c0)
      (canonicalFieldWord z.c0.c1) (canonicalFieldWord z.c1.c1) =
      .ok (some (canonicalExt4 z)) := by
  rw [decode_canonical_ext4_some_iff]
  exact ⟨isCanonical_canonicalFieldWord _, isCanonical_canonicalFieldWord _,
    isCanonical_canonicalFieldWord _, isCanonical_canonicalFieldWord _, rfl⟩

/-! ## 3. Canonical WHIR Fold Welds (`hemVirtualFoldOracle`, `verify_cwyz_duet_fold_step`) -/

/-- Base-field inversion commutes with canonical embedding `Goldilocks ↪ GoldilocksExt4`. -/
theorem embedBase_inv (a : Qsag.Goldilocks) :
    Qsag.Aggregation.GoldilocksExt4.embedBase (Qsag.Goldilocks.inv a) =
      Qsag.LawfulField.inv (Qsag.Aggregation.GoldilocksExt4.embedBase a) := by
  by_cases ha : a = Qsag.Goldilocks.zero
  · subst ha
    have hz1 : Qsag.Goldilocks.inv Qsag.Goldilocks.zero = Qsag.Goldilocks.zero := rfl
    have hz2 : Qsag.Aggregation.GoldilocksExt4.embedBase Qsag.Goldilocks.zero =
        Qsag.CommRingOps.zero := by
      rw [agg_embedBase, Qsag.GoldilocksField.GoldilocksExt4.embedBase_zero]
      exact Qsag.GoldilocksField.GoldilocksExt4.zero_eq_ringZero
    rw [hz1, hz2, Qsag.LawfulField.inv_zero]
  · let ea := Qsag.Aggregation.GoldilocksExt4.embedBase a
    have hea : ea ≠ Qsag.CommRingOps.zero := fun h0 => by
      dsimp only [ea] at h0
      apply ha
      apply Qsag.GoldilocksField.GoldilocksExt4.embedBase_injective
      rw [← agg_embedBase, h0, quartic_ring_zero]
      exact Qsag.GoldilocksField.GoldilocksExt4.embedBase_zero.symm
    have hmul : Qsag.CommRingOps.mul ea
        (Qsag.Aggregation.GoldilocksExt4.embedBase (Qsag.Goldilocks.inv a)) =
        Qsag.CommRingOps.one := by
      dsimp only [ea]
      rw [agg_embedBase, agg_embedBase, ← Qsag.GoldilocksField.GoldilocksExt4.embedBase_mul,
        Qsag.Goldilocks.mul_inv_cancel ha, Qsag.Goldilocks.ring_one,
        Qsag.GoldilocksField.GoldilocksExt4.embedBase_one]
      exact Qsag.GoldilocksField.GoldilocksExt4.one_eq_ringOne
    calc
      Qsag.Aggregation.GoldilocksExt4.embedBase (Qsag.Goldilocks.inv a)
        = Qsag.CommRingOps.mul Qsag.CommRingOps.one
            (Qsag.Aggregation.GoldilocksExt4.embedBase (Qsag.Goldilocks.inv a)) :=
          (Qsag.LawfulCommRing.one_mul _).symm
      _ = Qsag.CommRingOps.mul (Qsag.CommRingOps.mul (Qsag.LawfulField.inv ea) ea)
            (Qsag.Aggregation.GoldilocksExt4.embedBase (Qsag.Goldilocks.inv a)) := by
          rw [Qsag.LawfulCommRing.mul_comm (Qsag.LawfulField.inv ea) ea,
            Qsag.LawfulField.mul_inv_cancel hea]
      _ = Qsag.CommRingOps.mul (Qsag.LawfulField.inv ea)
            (Qsag.CommRingOps.mul ea
              (Qsag.Aggregation.GoldilocksExt4.embedBase (Qsag.Goldilocks.inv a))) :=
          Qsag.LawfulCommRing.mul_assoc _ _ _
      _ = Qsag.LawfulField.inv ea := by rw [hmul, Qsag.LawfulCommRing.mul_one]

private theorem field_inv_mul {F : Type} [Qsag.LawfulField F] [Qsag.NoZeroDivisors F]
    [DecidableEq F] (a b : F) :
    Qsag.LawfulField.inv (Qsag.CommRingOps.mul a b) =
      Qsag.CommRingOps.mul (Qsag.LawfulField.inv a) (Qsag.LawfulField.inv b) := by
  by_cases ha : a = Qsag.CommRingOps.zero
  · subst ha
    rw [Qsag.LawfulCommRing.zero_mul, Qsag.LawfulField.inv_zero, Qsag.LawfulCommRing.zero_mul]
  · by_cases hb : b = Qsag.CommRingOps.zero
    · subst hb
      rw [Qsag.LawfulCommRing.mul_zero, Qsag.LawfulField.inv_zero, Qsag.LawfulCommRing.mul_zero]
    · have hab : Qsag.CommRingOps.mul a b ≠ Qsag.CommRingOps.zero := fun h0 =>
        match Qsag.NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h0 with
        | Or.inl h => ha h
        | Or.inr h => hb h
      have hprod : Qsag.CommRingOps.mul (Qsag.CommRingOps.mul a b)
          (Qsag.CommRingOps.mul (Qsag.LawfulField.inv a) (Qsag.LawfulField.inv b)) =
          Qsag.CommRingOps.one := by
        calc
          Qsag.CommRingOps.mul (Qsag.CommRingOps.mul a b)
              (Qsag.CommRingOps.mul (Qsag.LawfulField.inv a) (Qsag.LawfulField.inv b))
            = Qsag.CommRingOps.mul (Qsag.CommRingOps.mul a (Qsag.LawfulField.inv a))
                (Qsag.CommRingOps.mul b (Qsag.LawfulField.inv b)) := by constructive_ring
          _ = Qsag.CommRingOps.mul Qsag.CommRingOps.one Qsag.CommRingOps.one := by
              rw [Qsag.LawfulField.mul_inv_cancel ha, Qsag.LawfulField.mul_inv_cancel hb]
          _ = Qsag.CommRingOps.one := Qsag.LawfulCommRing.one_mul _
      calc
        Qsag.LawfulField.inv (Qsag.CommRingOps.mul a b)
          = Qsag.CommRingOps.mul (Qsag.LawfulField.inv (Qsag.CommRingOps.mul a b))
              (Qsag.CommRingOps.mul (Qsag.CommRingOps.mul a b)
                (Qsag.CommRingOps.mul (Qsag.LawfulField.inv a) (Qsag.LawfulField.inv b))) := by
            rw [hprod, Qsag.LawfulCommRing.mul_one]
        _ = Qsag.CommRingOps.mul
              (Qsag.CommRingOps.mul (Qsag.LawfulField.inv (Qsag.CommRingOps.mul a b))
                (Qsag.CommRingOps.mul a b))
              (Qsag.CommRingOps.mul (Qsag.LawfulField.inv a) (Qsag.LawfulField.inv b)) := by
            constructive_ring
        _ = Qsag.CommRingOps.mul (Qsag.LawfulField.inv a) (Qsag.LawfulField.inv b) := by
            rw [Qsag.LawfulCommRing.mul_comm (Qsag.LawfulField.inv (Qsag.CommRingOps.mul a b)) _,
              Qsag.LawfulField.mul_inv_cancel hab, Qsag.LawfulCommRing.one_mul]

private theorem affine_fold_ring_ident
    (v0 v1 theta alpha beta halfE invTwoXE xxE : Qsag.Aggregation.GoldilocksExt4) :
    Qsag.Aggregation.GoldilocksExt4.add
      (Qsag.Aggregation.GoldilocksExt4.mul (Qsag.Aggregation.GoldilocksExt4.sub v0 v1) invTwoXE)
      (Qsag.Aggregation.GoldilocksExt4.mul
        (Qsag.Aggregation.GoldilocksExt4.add alpha
          (Qsag.Aggregation.GoldilocksExt4.mul beta xxE))
        (Qsag.CommRingOps.add
          (Qsag.CommRingOps.mul (Qsag.CommRingOps.add v0 v1) halfE)
          (Qsag.CommRingOps.mul theta
            (Qsag.CommRingOps.mul (Qsag.CommRingOps.sub v0 v1) invTwoXE)))) =
    Qsag.CommRingOps.add
      (Qsag.CommRingOps.mul invTwoXE (Qsag.CommRingOps.sub v0 v1))
      (Qsag.CommRingOps.mul
        (Qsag.CommRingOps.add alpha (Qsag.CommRingOps.mul beta xxE))
        (Qsag.CommRingOps.add
          (Qsag.CommRingOps.mul halfE (Qsag.CommRingOps.add v0 v1))
          (Qsag.CommRingOps.mul theta
            (Qsag.CommRingOps.mul invTwoXE (Qsag.CommRingOps.sub v0 v1))))) := by
  simp only [agg_add, agg_sub, agg_mul,
    ← Qsag.QuarticGoldilocks.ring_add, ← Qsag.QuarticGoldilocks.ring_sub,
    ← Qsag.QuarticGoldilocks.ring_mul]
  constructive_ring

/-- `Exec.hemAffineDuetFold` coincides identically with `Qsag.hemVirtualFoldOracle` in
    `Protocol.Aggregation.HemRbrSoundness` on any coset pair `(x, x^2)`. -/
theorem hemAffineDuetFold_eq_hemVirtualFoldOracle
    (v0 v1 theta alpha beta : Qsag.Aggregation.GoldilocksExt4)
    (x : Qsag.Goldilocks)
    (curDom foldDom : List Qsag.Aggregation.GoldilocksExt4)
    (curOracle : Nat → Qsag.Aggregation.GoldilocksExt4) (idx : Nat)
    (hx : curDom.getD (2 * idx) Qsag.CommRingOps.one =
      Qsag.Aggregation.GoldilocksExt4.embedBase x)
    (hy : foldDom.getD idx Qsag.CommRingOps.zero =
      Qsag.Aggregation.GoldilocksExt4.embedBase (Qsag.Goldilocks.mul x x))
    (ha : curOracle (2 * idx) = v0)
    (hb : curOracle (2 * idx + 1) = v1) :
    Qsag.Exec.hemAffineDuetFold v0 v1 x theta alpha beta =
      Qsag.hemVirtualFoldOracle theta alpha beta curDom foldDom curOracle idx := by
  rw [Qsag.hemVirtualFoldOracle_def, hx, hy, ha, hb,
    Qsag.Exec.hemAffineDuetFold.public_eqs, Qsag.Aggregation.foldDuetExt4.public_eqs,
    gf_embedBase, gf_embedBase, ← agg_embedBase, ← agg_embedBase]
  have htwo_g : Qsag.Goldilocks.ofNat 2 =
      Qsag.CommRingOps.add (Qsag.CommRingOps.one : Qsag.Goldilocks) Qsag.CommRingOps.one := by
    rw [goldilocks_ring_add, Qsag.Goldilocks.ring_one]
    decide
  have htwo : Qsag.Aggregation.GoldilocksExt4.embedBase (Qsag.Goldilocks.ofNat 2) =
      Qsag.CommRingOps.add (Qsag.CommRingOps.one : Qsag.Aggregation.GoldilocksExt4)
        Qsag.CommRingOps.one := by
    rw [agg_embedBase, htwo_g, Qsag.GoldilocksField.GoldilocksExt4.embedBase_add,
      Qsag.Goldilocks.ring_one, Qsag.GoldilocksField.GoldilocksExt4.embedBase_one,
      Qsag.GoldilocksField.GoldilocksExt4.one_eq_ringOne]
  have hhalf : Qsag.Aggregation.GoldilocksExt4.embedBase
      (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)) =
      Qsag.LawfulField.inv (Qsag.CommRingOps.add
        (Qsag.CommRingOps.one : Qsag.Aggregation.GoldilocksExt4) Qsag.CommRingOps.one) := by
    rw [embedBase_inv, htwo]
  have hinv2x : Qsag.Aggregation.GoldilocksExt4.embedBase
      (Qsag.Goldilocks.mul (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2))
        (Qsag.Goldilocks.inv x)) =
      Qsag.LawfulField.inv (Qsag.CommRingOps.mul
        (Qsag.CommRingOps.add (Qsag.CommRingOps.one : Qsag.Aggregation.GoldilocksExt4)
          Qsag.CommRingOps.one)
        (Qsag.Aggregation.GoldilocksExt4.embedBase x)) := by
    rw [← goldilocks_ring_mul, agg_embedBase,
      Qsag.GoldilocksField.GoldilocksExt4.embedBase_mul,
      ← agg_embedBase, ← agg_embedBase, hhalf, embedBase_inv, ← field_inv_mul]
  rw [hinv2x, hhalf]
  exact affine_fold_ring_ident v0 v1 theta alpha beta _ _ _

/-- Extracted `fold_duet_affine_ext4` refines `Qsag.hemVirtualFoldOracle` directly. -/
theorem fold_duet_affine_ext4_refines_hemVirtualFoldOracle
    (v0 v1 : Ext4) (x : Qsag.Goldilocks) (theta alpha beta : Ext4)
    (curDom foldDom : List Qsag.Aggregation.GoldilocksExt4)
    (curOracle : Nat → Qsag.Aggregation.GoldilocksExt4) (idx : Nat)
    (hx : curDom.getD (2 * idx) Qsag.CommRingOps.one =
      Qsag.Aggregation.GoldilocksExt4.embedBase x)
    (hy : foldDom.getD idx Qsag.CommRingOps.zero =
      Qsag.Aggregation.GoldilocksExt4.embedBase (Qsag.Goldilocks.mul x x))
    (ha : curOracle (2 * idx) = ext4Abs v0)
    (hb : curOracle (2 * idx + 1) = ext4Abs v1) :
    (ext4Abs <$> fold_duet_affine_ext4 v0 v1
      (canonicalFieldWord (Qsag.Goldilocks.mul
        (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)) (Qsag.Goldilocks.inv x)))
      (canonicalFieldWord (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)))
      (canonicalFieldWord (Qsag.Goldilocks.mul x x)) theta alpha beta) =
      .ok (Qsag.hemVirtualFoldOracle
        (ext4Abs theta) (ext4Abs alpha) (ext4Abs beta) curDom foldDom curOracle idx) := by
  rw [fold_duet_affine_ext4_canonical_twiddles,
    hemAffineDuetFold_eq_hemVirtualFoldOracle _ _ _ _ _ x curDom foldDom curOracle idx hx hy ha hb]

private theorem isCanonicalExt4_cwyzValue
    (v0 v1 : Ext4) (iy it yy : U64) (theta alpha beta : Ext4) :
    IsCanonicalExt4 (cwyzValue v0 v1 iy it yy theta alpha beta) := by
  rw [cwyzValue.public_eqs]
  exact extAdd_canonical _ _

private theorem isCanonicalExt4_duetValue
    (v0 v1 : Ext4) (iy it : U64) (alpha : Ext4) :
    IsCanonicalExt4 (duetValue v0 v1 iy it alpha) := by
  rw [duetValue.public_eqs]
  exact extAdd_canonical _ _

private theorem isCanonicalExt4_cwyzBridgeValue
    (w0 w1 w2 w3 w4 claim phi theta alpha beta : Ext4) :
    IsCanonicalExt4 (cwyzBridgeValue w0 w1 w2 w3 w4 claim phi theta alpha beta) := by
  rw [cwyzBridgeValue.public_eqs]
  exact extAdd_canonical _ _

/-- With canonical inverse twiddles and coset square, `verify_cwyz_duet_fold_step` accepts
    `claimed` if and only if `claimed` has canonical limbs (`< p`) AND `ext4Abs claimed`
    equals `Qsag.hemVirtualFoldOracle` in `Protocol.Aggregation.HemRbrSoundness`. -/
theorem verify_cwyz_duet_fold_step_sound_qsag
    (v0 v1 : Ext4) (x : Qsag.Goldilocks) (theta alpha beta claimed : Ext4)
    (curDom foldDom : List Qsag.Aggregation.GoldilocksExt4)
    (curOracle : Nat → Qsag.Aggregation.GoldilocksExt4) (idx : Nat)
    (hx : curDom.getD (2 * idx) Qsag.CommRingOps.one =
      Qsag.Aggregation.GoldilocksExt4.embedBase x)
    (hy : foldDom.getD idx Qsag.CommRingOps.zero =
      Qsag.Aggregation.GoldilocksExt4.embedBase (Qsag.Goldilocks.mul x x))
    (ha : curOracle (2 * idx) = ext4Abs v0)
    (hb : curOracle (2 * idx + 1) = ext4Abs v1) :
    verify_cwyz_duet_fold_step v0 v1
      (canonicalFieldWord (Qsag.Goldilocks.mul
        (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)) (Qsag.Goldilocks.inv x)))
      (canonicalFieldWord (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)))
      (canonicalFieldWord (Qsag.Goldilocks.mul x x))
      theta alpha beta claimed = .ok true ↔
      (IsCanonicalExt4 claimed ∧
       ext4Abs claimed = Qsag.hemVirtualFoldOracle
         (ext4Abs theta) (ext4Abs alpha) (ext4Abs beta) curDom foldDom curOracle idx) := by
  rw [verify_cwyz_duet_fold_step_sound]
  have href := fold_duet_affine_ext4_refines_hemVirtualFoldOracle
    v0 v1 x theta alpha beta curDom foldDom curOracle idx hx hy ha hb
  rw [fold_duet_affine_ext4_spec] at href
  have hval : ext4Abs (cwyzValue v0 v1
      (canonicalFieldWord (Qsag.Goldilocks.mul
        (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)) (Qsag.Goldilocks.inv x)))
      (canonicalFieldWord (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)))
      (canonicalFieldWord (Qsag.Goldilocks.mul x x)) theta alpha beta) =
      Qsag.hemVirtualFoldOracle
        (ext4Abs theta) (ext4Abs alpha) (ext4Abs beta) curDom foldDom curOracle idx :=
    Result.ok.inj href
  constructor
  · intro heq
    subst heq
    exact ⟨isCanonicalExt4_cwyzValue _ _ _ _ _ _ _ _, hval⟩
  · rintro ⟨hcan, habs⟩
    exact (ext4Abs_inj hcan (isCanonicalExt4_cwyzValue _ _ _ _ _ _ _ _)).mp (habs.trans hval.symm)

/-- Canonical bidirectional soundness of `verify_affine_duet_fold_step` against `Exec.hemDuetFold`. -/
theorem verify_affine_duet_fold_step_sound_qsag
    (v0 v1 : Ext4) (iy it : U64) (alpha claimed : Ext4) :
    verify_affine_duet_fold_step v0 v1 iy it alpha claimed = .ok true ↔
      (IsCanonicalExt4 claimed ∧
       ext4Abs claimed = Qsag.Exec.hemDuetFold
         (ext4Abs v0) (ext4Abs v1) (fieldAbs iy) (fieldAbs it) (ext4Abs alpha)) := by
  rw [verify_affine_duet_fold_step_sound]
  have href := duet_fold_refines_exec v0 v1 iy it alpha
  rw [duet_refines] at href
  have hval : ext4Abs (duetValue v0 v1 iy it alpha) =
      Qsag.Exec.hemDuetFold (ext4Abs v0) (ext4Abs v1) (fieldAbs iy) (fieldAbs it) (ext4Abs alpha) :=
    Result.ok.inj href
  constructor
  · intro heq
    subst heq
    exact ⟨isCanonicalExt4_duetValue _ _ _ _ _, hval⟩
  · rintro ⟨hcan, habs⟩
    exact (ext4Abs_inj hcan (isCanonicalExt4_duetValue _ _ _ _ _)).mp (habs.trans hval.symm)

private theorem evalCoeffs_const (c r : Qsag.Aggregation.GoldilocksExt4) :
    Qsag.RoundPoly.evalCoeffs [c] r = c := by
  rw [Qsag.RoundPoly.evalCoeffs_cons, Qsag.RoundPoly.evalCoeffs_nil,
    Qsag.LawfulCommRing.mul_zero, Qsag.LawfulCommRing.add_zero]

private theorem evalCoeffs_linear (a b r : Qsag.Aggregation.GoldilocksExt4) :
    Qsag.RoundPoly.evalCoeffs [a, b] r =
      Qsag.Aggregation.GoldilocksExt4.add a (Qsag.Aggregation.GoldilocksExt4.mul r b) := by
  rw [Qsag.RoundPoly.evalCoeffs_cons, evalCoeffs_const, Qsag.QuarticGoldilocks.ring_add,
    Qsag.QuarticGoldilocks.ring_mul]

private theorem filter_imp_length_le {α : Type} (p q : α → Bool)
    (himp : ∀ x, p x = true → q x = true) :
    ∀ xs : List α, (xs.filter p).length ≤ (xs.filter q).length
  | [] => Nat.le_refl 0
  | x :: xs => by
    simp only [List.filter_cons]
    cases hp : p x
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases q x
      · exact filter_imp_length_le p q himp xs
      · exact Nat.le_succ_of_le (filter_imp_length_le p q himp xs)
    · rw [himp x hp]
      simp only [↓reduceIte, List.length_cons]
      exact Nat.succ_le_succ (filter_imp_length_le p q himp xs)

/-- Schwartz–Zippel coset duet soundness for `verify_affine_duet_fold_step`:
    at most `1` challenge `r` in any duplicate-free pool `S` accepts a cheated `claimed`. -/
theorem verify_affine_duet_fold_step_roots_le_one
    (v0 v1 claimed : Ext4) (iy it : U64)
    (S : List Qsag.Aggregation.GoldilocksExt4) (hS : S.Nodup)
    (hne : ∃ r : Qsag.Aggregation.GoldilocksExt4,
      Qsag.Exec.hemDuetFold (ext4Abs v0) (ext4Abs v1) (fieldAbs iy) (fieldAbs it) r ≠
        ext4Abs claimed) :
    (S.filter (fun r => decide
      (verify_affine_duet_fold_step v0 v1 iy it (canonicalExt4 r) claimed = .ok true))).length ≤ 1 := by
  let even := Qsag.Aggregation.GoldilocksExt4.mul
    (Qsag.Aggregation.GoldilocksExt4.add (ext4Abs v0) (ext4Abs v1))
    (Qsag.Aggregation.GoldilocksExt4.embedBase (fieldAbs it))
  let odd := Qsag.Aggregation.GoldilocksExt4.mul
    (Qsag.Aggregation.GoldilocksExt4.sub (ext4Abs v0) (ext4Abs v1))
    (Qsag.Aggregation.GoldilocksExt4.embedBase (fieldAbs iy))
  have heval : ∀ r : Qsag.Aggregation.GoldilocksExt4,
      Qsag.RoundPoly.evalCoeffs [odd, even] r =
        Qsag.Exec.hemDuetFold (ext4Abs v0) (ext4Abs v1) (fieldAbs iy) (fieldAbs it) r := by
    intro r
    rw [evalCoeffs_linear, Qsag.Exec.hemDuetFold.public_eqs]
  have hd : ∃ r, Qsag.RoundPoly.evalCoeffs [odd, even] r ≠
      Qsag.RoundPoly.evalCoeffs [ext4Abs claimed] r := by
    obtain ⟨r₀, hr₀⟩ := hne
    refine ⟨r₀, ?_⟩
    rw [heval, evalCoeffs_const]
    exact hr₀
  have hbound := Qsag.Aggregation.ext4_poly_roots_le_degree 1 [odd, even] [ext4Abs claimed] S hS
    (by simp) (by simp) hd
  refine Nat.le_trans (filter_imp_length_le _ _ ?_ S) hbound
  intro r hr
  have hacc := of_decide_eq_true hr
  have hval := ((verify_affine_duet_fold_step_sound_qsag v0 v1 iy it (canonicalExt4 r) claimed).mp hacc).2
  rw [ext4Abs_canonicalExt4] at hval
  rw [heval, evalCoeffs_const]
  exact decide_eq_true hval.symm

/-! ## 4. Canonical CWYZ Bridge, Cascade & Quadratic Sumcheck Wire Welds -/

theorem hemBridgeClaimStep_eq_hemBridgeFoldClaim
    (e0 e1 e2 e3 e4 claim phi theta alpha beta : Qsag.Aggregation.GoldilocksExt4) :
    Qsag.Exec.hemBridgeClaimStep e0 e1 e2 e3 e4 claim phi theta alpha beta =
      Qsag.hemBridgeFoldClaim claim e0 e1 e2 e3 e4 phi theta alpha beta := by
  rw [Qsag.Exec.hemBridgeClaimStep.public_eqs, Qsag.hemBridgeFoldClaim_def]
  simp only [← Qsag.QuarticGoldilocks.ring_add, ← Qsag.QuarticGoldilocks.ring_sub,
    ← Qsag.QuarticGoldilocks.ring_mul]
  constructive_ring

/-- Accepts `claimed_next` if and only if `claimed_next` is limb-canonical and `ext4Abs claimed_next`
    equals `Qsag.hemBridgeFoldClaim` in `Protocol.Aggregation.MultiRoundFsQrom`. -/
theorem verify_cwyz_bridge_claim_step_sound_qsag
    (w0 w1 w2 w3 w4 claim phi theta alpha beta claimed_next : Ext4) :
    verify_cwyz_bridge_claim_step w0 w1 w2 w3 w4 claim phi theta alpha beta claimed_next = .ok true ↔
      (IsCanonicalExt4 claimed_next ∧
       ext4Abs claimed_next = Qsag.hemBridgeFoldClaim
         (ext4Abs claim) (ext4Abs w0) (ext4Abs w1) (ext4Abs w2) (ext4Abs w3) (ext4Abs w4)
         (ext4Abs phi) (ext4Abs theta) (ext4Abs alpha) (ext4Abs beta)) := by
  rw [verify_cwyz_bridge_claim_step_sound]
  have href := cwyz_bridge_refines_exec w0 w1 w2 w3 w4 claim phi theta alpha beta
  rw [cwyz_bridge_claim_step_refines] at href
  have hval : ext4Abs (cwyzBridgeValue w0 w1 w2 w3 w4 claim phi theta alpha beta) =
      Qsag.hemBridgeFoldClaim (ext4Abs claim) (ext4Abs w0) (ext4Abs w1) (ext4Abs w2)
        (ext4Abs w3) (ext4Abs w4) (ext4Abs phi) (ext4Abs theta) (ext4Abs alpha) (ext4Abs beta) :=
    (Result.ok.inj href).trans (hemBridgeClaimStep_eq_hemBridgeFoldClaim _ _ _ _ _ _ _ _ _ _)
  constructor
  · intro heq
    subst heq
    exact ⟨isCanonicalExt4_cwyzBridgeValue _ _ _ _ _ _ _ _ _ _, hval⟩
  · rintro ⟨hcan, habs⟩
    exact (ext4Abs_inj hcan (isCanonicalExt4_cwyzBridgeValue _ _ _ _ _ _ _ _ _ _)).mp
      (habs.trans hval.symm)

private theorem cascade_step_ring_ident
    (acc w0 e w1 s : Qsag.Aggregation.GoldilocksExt4) :
    Qsag.Aggregation.GoldilocksExt4.add
      (Qsag.Aggregation.GoldilocksExt4.add acc (Qsag.Aggregation.GoldilocksExt4.mul w0 e))
      (Qsag.Aggregation.GoldilocksExt4.mul w1 s) =
    Qsag.CommRingOps.add
      (Qsag.CommRingOps.add (Qsag.CommRingOps.mul w0 e) (Qsag.CommRingOps.mul w1 s)) acc := by
  simp only [← Qsag.QuarticGoldilocks.ring_add, ← Qsag.QuarticGoldilocks.ring_mul]
  constructive_ring

/-- Extracted `affine_cascade_claim_step` refines one step of `Qsag.evalCascadeClaim`
    (`MultiRoundFsQrom.evalCascadeClaim_cons`). -/
theorem affine_cascade_claim_step_refines_evalCascadeClaim
    (w0 w1 eval_at_point shifted_eval : Ext4)
    (es ss : List Qsag.Aggregation.GoldilocksExt4)
    (abs : List (Qsag.Aggregation.GoldilocksExt4 × Qsag.Aggregation.GoldilocksExt4)) :
    (ext4Abs <$> affine_cascade_claim_step
      (canonicalExt4 (Qsag.evalCascadeClaim es ss abs)) w0 w1 eval_at_point shifted_eval) =
      .ok (Qsag.evalCascadeClaim
        (ext4Abs eval_at_point :: es)
        (ext4Abs shifted_eval :: ss)
        ((ext4Abs w0, ext4Abs w1) :: abs)) := by
  rw [affine_cascade_claim_step_spec]
  change Result.ok (ext4Abs (extAdd (extAdd (canonicalExt4 (Qsag.evalCascadeClaim es ss abs))
    (extMul w0 eval_at_point)) (extMul w1 shifted_eval))) = _
  rw [ext4Abs_add, ext4Abs_add, ext4Abs_mul, ext4Abs_mul, ext4Abs_canonicalExt4,
    Qsag.evalCascadeClaim_cons]
  exact congrArg Result.ok (cascade_step_ring_ident _ _ _ _ _)

/-- Canonical quadratic coefficient list reconstructed by `eval_quadratic_sumcheck_wire`. -/
def canonicalQuadraticWirePoly (c0 c2 claim : Qsag.Aggregation.GoldilocksExt4) :
    List Qsag.Aggregation.GoldilocksExt4 :=
  [c0, Qsag.Aggregation.GoldilocksExt4.sub
         (Qsag.Aggregation.GoldilocksExt4.sub claim (Qsag.Aggregation.GoldilocksExt4.add c0 c0))
         c2, c2]

private theorem quadratic_wire_eval_ident
    (a c s r : Qsag.Aggregation.GoldilocksExt4) :
    Qsag.Aggregation.GoldilocksExt4.add
      (Qsag.Aggregation.GoldilocksExt4.mul
        (Qsag.Aggregation.GoldilocksExt4.add
          (Qsag.Aggregation.GoldilocksExt4.mul c r)
          (Qsag.Aggregation.GoldilocksExt4.sub
            (Qsag.Aggregation.GoldilocksExt4.sub s (Qsag.Aggregation.GoldilocksExt4.add a a)) c))
        r) a =
    Qsag.RoundPoly.evalCoeffs (canonicalQuadraticWirePoly a c s) r := by
  unfold canonicalQuadraticWirePoly
  rw [Qsag.RoundPoly.evalCoeffs_cons, Qsag.RoundPoly.evalCoeffs_cons, evalCoeffs_const]
  simp only [← Qsag.QuarticGoldilocks.ring_add, ← Qsag.QuarticGoldilocks.ring_sub,
    ← Qsag.QuarticGoldilocks.ring_mul]
  constructive_ring

private theorem canonicalQuadraticWirePoly_sum
    (a c s : Qsag.Aggregation.GoldilocksExt4) :
    Qsag.CommRingOps.add
      (Qsag.RoundPoly.evalCoeffs (canonicalQuadraticWirePoly a c s) Qsag.CommRingOps.zero)
      (Qsag.RoundPoly.evalCoeffs (canonicalQuadraticWirePoly a c s) Qsag.CommRingOps.one) = s := by
  unfold canonicalQuadraticWirePoly
  rw [Qsag.RoundPoly.evalCoeffs_cons, Qsag.RoundPoly.evalCoeffs_cons, evalCoeffs_const,
    Qsag.RoundPoly.evalCoeffs_cons, Qsag.RoundPoly.evalCoeffs_cons, evalCoeffs_const]
  simp only [agg_add, agg_sub, ← Qsag.QuarticGoldilocks.ring_add,
    ← Qsag.QuarticGoldilocks.ring_sub]
  constructive_ring

/-- Extracted `eval_quadratic_sumcheck_wire` refines `RoundPoly.evalCoeffs` on
    `canonicalQuadraticWirePoly`. -/
theorem eval_quadratic_sumcheck_wire_refines_qsag
    (c0 c2 sum_claim r : Ext4) :
    (ext4Abs <$> eval_quadratic_sumcheck_wire c0 c2 sum_claim r) =
      .ok (Qsag.RoundPoly.evalCoeffs
        (canonicalQuadraticWirePoly (ext4Abs c0) (ext4Abs c2) (ext4Abs sum_claim))
        (ext4Abs r)) := by
  rw [eval_quadratic_sumcheck_wire_refines]
  change Result.ok (ext4Abs (quadraticWireValue c0 c2 sum_claim r)) = _
  rw [quadraticWireValue.public_eqs, ext4Abs_add, ext4Abs_mul, ext4Abs_add,
    ext4Abs_mul, ext4Abs_sub, ext4Abs_sub, ext4Abs_add]
  exact congrArg Result.ok (quadratic_wire_eval_ident _ _ _ _)

/-- Schwartz–Zippel soundness of extracted `eval_quadratic_sumcheck_wire` via
    `Qsag.hemSumcheck_polynomial_collision_count`: against any genuine quadratic `G`
    (`G.length ≤ 3`) whose boolean hypercube sum `G(0) + G(1)` differs from `ext4Abs sum_claim`,
    at most `2` challenges `r ∈ S` collide with `G(r)`. -/
theorem eval_quadratic_sumcheck_wire_bad_challenges_le_two
    (G S : List Qsag.Aggregation.GoldilocksExt4) (c0 c2 sum_claim : Ext4)
    (hS : S.Nodup) (hG : G.length ≤ 3)
    (hFalse : ext4Abs sum_claim ≠ Qsag.CommRingOps.add
      (Qsag.RoundPoly.evalCoeffs G Qsag.CommRingOps.zero)
      (Qsag.RoundPoly.evalCoeffs G Qsag.CommRingOps.one)) :
    (S.filter (fun r => decide
      ((ext4Abs <$> eval_quadratic_sumcheck_wire c0 c2 sum_claim (canonicalExt4 r)) =
        .ok (Qsag.RoundPoly.evalCoeffs G r)))).length ≤ 2 := by
  let H := canonicalQuadraticWirePoly (ext4Abs c0) (ext4Abs c2) (ext4Abs sum_claim)
  have hbound := Qsag.hemSumcheck_polynomial_collision_count 2 G H S (ext4Abs sum_claim)
    hS hG (Nat.le_refl 3) (canonicalQuadraticWirePoly_sum _ _ _) hFalse
  refine Nat.le_trans (filter_imp_length_le _ _ ?_ S) hbound
  intro r hr
  have hacc := of_decide_eq_true hr
  rw [eval_quadratic_sumcheck_wire_refines_qsag, ext4Abs_canonicalExt4] at hacc
  exact decide_eq_true (Result.ok.inj hacc)

/-! ## 5. Canonical Horner & Polynomial Pin Welds (`RoundPoly.evalCoeffs`) -/

theorem hemHorner_zero_eq_evalCoeffs
    (cs : List Qsag.Aggregation.GoldilocksExt4) (z : Qsag.Goldilocks) :
    Qsag.Exec.hemHorner cs z Qsag.Aggregation.GoldilocksExt4.zero =
      Qsag.RoundPoly.evalCoeffs cs (Qsag.Aggregation.GoldilocksExt4.embedBase z) := by
  induction cs with
  | nil =>
    rw [Qsag.Exec.hemHorner_nil, Qsag.RoundPoly.evalCoeffs_nil, quartic_ring_zero]
  | cons c rest ih =>
    rw [Qsag.Exec.hemHorner_cons, ih, Qsag.RoundPoly.evalCoeffs_cons]
    simp only [← Qsag.QuarticGoldilocks.ring_add, ← Qsag.QuarticGoldilocks.ring_mul]
    rw [Qsag.LawfulCommRing.mul_comm _ (Qsag.Aggregation.GoldilocksExt4.embedBase z),
      Qsag.LawfulCommRing.add_comm]

/-- Refines `Qsag.RoundPoly.evalCoeffs` at `embedBase (fieldAbs z)` unconditionally. -/
theorem eval_ext4_univariate_at_base_refines_evalCoeffs (coeffs : Slice Ext4) (z : U64) :
    (ext4Abs <$> eval_ext4_univariate_at_base coeffs z) =
      .ok (Qsag.RoundPoly.evalCoeffs (coeffs.val.map ext4Abs)
        (Qsag.Aggregation.GoldilocksExt4.embedBase (fieldAbs z))) := by
  rw [eval_ext4_univariate_refines_exec, hemHorner_zero_eq_evalCoeffs]

/-- Accepts `expected` iff `expected` is limb-canonical and `ext4Abs expected` equals
    `Qsag.RoundPoly.evalCoeffs (coeffs.val.map ext4Abs) (embedBase (fieldAbs z))`. -/
theorem verify_ext4_univariate_at_base_pin_sound_qsag
    (coeffs : Slice Ext4) (z : U64) (expected : Ext4) :
    verify_ext4_univariate_at_base_pin coeffs z expected = .ok true ↔
      (IsCanonicalExt4 expected ∧
       ext4Abs expected = Qsag.RoundPoly.evalCoeffs (coeffs.val.map ext4Abs)
         (Qsag.Aggregation.GoldilocksExt4.embedBase (fieldAbs z))) := by
  rw [verify_ext4_univariate_at_base_pin_sound]
  have hval : ext4Abs (hornerSpec coeffs.val z extZero) =
      Qsag.RoundPoly.evalCoeffs (coeffs.val.map ext4Abs)
        (Qsag.Aggregation.GoldilocksExt4.embedBase (fieldAbs z)) := by
    rw [hornerSpec_refines_exec, ext4Abs_zero, hemHorner_zero_eq_evalCoeffs]
  constructor
  · intro heq
    subst heq
    exact ⟨hornerSpec_canonical coeffs.val z, hval⟩
  · rintro ⟨hcan, habs⟩
    exact (ext4Abs_inj hcan (hornerSpec_canonical coeffs.val z)).mp (habs.trans hval.symm)

private theorem nodup_map_of_inj {α β : Type} {f : α → β}
    (hinj : ∀ x y, f x = f y → x = y) :
    ∀ {xs : List α}, xs.Nodup → (xs.map f).Nodup
  | [], _ => List.Pairwise.nil
  | x :: xs, h => by
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, nodup_map_of_inj hinj h.2⟩
    intro hm
    obtain ⟨y, hy, heq⟩ := List.mem_map.mp hm
    exact h.1 (hinj y x heq ▸ hy)

/-- List-pinning Schwartz–Zippel bound for `verify_ext4_univariate_at_base_pin`:
    two distinct degree-`≤ d` candidate slices `candA, candB` can both accept `candA`'s canonical
    evaluation pin for at most `d` base-field evaluation points `z ∈ S` (`S.Nodup`). -/
theorem verify_ext4_univariate_at_base_pin_roots_le_degree
    (d : Nat) (candA candB : Slice Ext4) (S : List Qsag.Goldilocks)
    (hNodup : S.Nodup)
    (hLenA : candA.val.length ≤ d + 1) (hLenB : candB.val.length ≤ d + 1)
    (hDiff : ∃ z₀ : Qsag.Aggregation.GoldilocksExt4,
      Qsag.RoundPoly.evalCoeffs (candA.val.map ext4Abs) z₀ ≠
        Qsag.RoundPoly.evalCoeffs (candB.val.map ext4Abs) z₀) :
    (S.filter (fun z =>
      let pinA := canonicalExt4 (Qsag.RoundPoly.evalCoeffs (candA.val.map ext4Abs)
        (Qsag.Aggregation.GoldilocksExt4.embedBase z))
      decide (verify_ext4_univariate_at_base_pin candB (canonicalFieldWord z) pinA = .ok true))).length ≤
      d := by
  let SE : List Qsag.Aggregation.GoldilocksExt4 :=
    S.map Qsag.Aggregation.GoldilocksExt4.embedBase
  have hSENodup : SE.Nodup :=
    nodup_map_of_inj (fun _ _ h => Qsag.GoldilocksField.GoldilocksExt4.embedBase_injective h) hNodup
  have hBound := Qsag.Aggregation.whir_ood_pin_roots_le_degree d
    (candA.val.map ext4Abs) (candB.val.map ext4Abs) SE hSENodup
    (by simpa [List.length_map] using hLenA)
    (by simpa [List.length_map] using hLenB) hDiff
  rw [List.filter_map, List.length_map] at hBound
  refine Nat.le_trans (filter_imp_length_le _ _ ?_ S) hBound
  intro z hz
  have hacc := of_decide_eq_true hz
  have eB := ((verify_ext4_univariate_at_base_pin_sound_qsag candB (canonicalFieldWord z) _).mp hacc).2
  rw [ext4Abs_canonicalExt4, fieldAbs_canonicalFieldWord] at eB
  exact decide_eq_true eB

/-! ## 6. Canonical OOD-Pin, Stage PoW, Merkle Pair Order, & Quorum Sum Welds -/

/-- Canonical `4 * k`-word slice representation of a list of `GoldilocksExt4` OOD evaluations. -/
def ext4SliceWords (xs : List Qsag.Aggregation.GoldilocksExt4) : List U64 :=
  xs.flatMap (fun z =>
    [canonicalFieldWord z.c0.c0, canonicalFieldWord z.c0.c1,
     canonicalFieldWord z.c1.c0, canonicalFieldWord z.c1.c1])

theorem ext4SliceWords_injective :
    ∀ {xs ys : List Qsag.Aggregation.GoldilocksExt4},
      ext4SliceWords xs = ext4SliceWords ys → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: xs, y :: ys, h => by
    simp only [ext4SliceWords, List.flatMap_cons, List.cons_append, List.nil_append,
      List.cons.injEq] at h
    rcases h with ⟨h0, h1, h2, h3, hrest⟩
    have e0 : x.c0.c0 = y.c0.c0 := by
      rw [← fieldAbs_canonicalFieldWord x.c0.c0, h0, fieldAbs_canonicalFieldWord]
    have e1 : x.c0.c1 = y.c0.c1 := by
      rw [← fieldAbs_canonicalFieldWord x.c0.c1, h1, fieldAbs_canonicalFieldWord]
    have e2 : x.c1.c0 = y.c1.c0 := by
      rw [← fieldAbs_canonicalFieldWord x.c1.c0, h2, fieldAbs_canonicalFieldWord]
    have e3 : x.c1.c1 = y.c1.c1 := by
      rw [← fieldAbs_canonicalFieldWord x.c1.c1, h3, fieldAbs_canonicalFieldWord]
    have hxy : x = y := Qsag.QuarticGoldilocks.ext
      (Qsag.GoldilocksExt2.ext e0 e1) (Qsag.GoldilocksExt2.ext e2 e3)
    have htail := ext4SliceWords_injective hrest
    subst hxy htail
    rfl

/-- Over canonical `GoldilocksExt4` OOD pin word slices, `verify_ood_pin_eq` accepts if and only
    if the underlying `List GoldilocksExt4` OOD vectors are equal. -/
theorem verify_ood_pin_eq_canonical_ext4_iff
    (expected supplied : Slice U64)
    (expPins supPins : List Qsag.Aggregation.GoldilocksExt4)
    (he : expected.val = ext4SliceWords expPins)
    (hs : supplied.val = ext4SliceWords supPins) :
    verify_ood_pin_eq expected supplied = .ok true ↔ expPins = supPins := by
  rw [verify_ood_pin_eq_sound, he, hs]
  exact ⟨ext4SliceWords_injective, congrArg ext4SliceWords⟩

/-- The extracted production mask is exactly the canonical WHIR mask predicate. -/
theorem verify_stage_pow_mask_refines_canonical (word : U64) (bits : U32) :
    verify_stage_pow_mask word bits =
      .ok (Qsag.Aggregation.whirStagePowMask word.val bits.val) := by
  have h := verify_stage_pow_mask_mod_sound word bits
  rw [verify_stage_pow_mask_spec] at h ⊢
  simp only [Result.ok.injEq, decide_eq_true_eq] at h
  simp only [Qsag.Aggregation.whirStagePowMask.public_eqs]
  apply congrArg Result.ok
  exact decide_eq_decide.mpr h

/-- For any 32-byte challenge `chal` and `u64` `powNonce`, when `word` carries the little-endian
    low 16 bits of `cshake256Bytes whirPowCustomization (chal ++ leBytes 8 powNonce)`,
    `verify_stage_pow_mask word 16#u32 = .ok true` is equivalent to
    `Qsag.Aggregation.verifyWhirStagePow chal powNonce.val 16 = true`. -/
theorem verify_stage_pow_mask_16_iff_verifyWhirStagePow
    (chal : List UInt8) (powNonce word : U64)
    (hLen : chal.length = 32)
    (hLow16 : word.val % 65536 =
      let dig := Qsag.cshake256Bytes Qsag.Aggregation.whirPowCustomization
        (chal ++ Qsag.Aggregation.leBytes 8 powNonce.val)
      (dig.getD 0 0).toNat + 256 * (dig.getD 1 0).toNat) :
    verify_stage_pow_mask word 16#u32 = .ok true ↔
      Qsag.Aggregation.verifyWhirStagePow chal powNonce.val 16 = true := by
  rw [verify_stage_pow_mask_mod_sound,
    Qsag.Aggregation.verifyWhirStagePow_16_iff chal powNonce.val hLen powNonce.bv.isLt]
  have h16 : (16#u32).val = 16 := rfl
  rw [h16]
  have hpow : (2 : Nat) ^ 16 = 65536 := by decide
  rw [hpow, hLow16]
  have hDigLen := Qsag.cshake256Bytes_length Qsag.Aggregation.whirPowCustomization
    (chal ++ Qsag.Aggregation.leBytes 8 powNonce.val)
  generalize Qsag.cshake256Bytes Qsag.Aggregation.whirPowCustomization
    (chal ++ Qsag.Aggregation.leBytes 8 powNonce.val) = dig at hDigLen ⊢
  rcases dig with _ | ⟨b0, _ | ⟨b1, rest⟩⟩
  · cases hDigLen
  · cases hDigLen
  · simp only [Nat.le_of_lt (by decide : 16 < 32), true_and, List.getD_cons_zero,
      List.getD_cons_succ, List.take_succ_cons, List.take_zero, List.all_cons, List.all_nil,
      Bool.and_true, Bool.and_eq_true, beq_iff_eq]
    have hb0 : b0.toNat < 256 := b0.toBitVec.isLt
    have hb1 : b1.toNat < 256 := b1.toBitVec.isLt
    constructor
    · intro hz
      have h0 : b0.toNat = 0 := by omega
      have h1 : b1.toNat = 0 := by omega
      exact ⟨UInt8.toNat_inj.mp h0, UInt8.toNat_inj.mp h1⟩
    · rintro ⟨rfl, rfl⟩
      rfl

/-- A returned pair has `level < 64`, tag `0`, and frames `(left, right)` in the order chosen
    by the parity of `idx / 2^level`: the framed pair is
    `Qsag.Aggregation.merkleNodeFrame (idx / 2^level) node sibling`. -/
theorem step_merkle_pair_order_canonical_parity
    (idx : U64) (level : U32) (node sibling : Array U8 32#usize) (pair : MerklePair)
    (h : step_merkle_pair_order idx level node sibling = .ok (some pair)) :
    level.val < 64 ∧
    pair.tag = 0#u8 ∧
    Qsag.encodeMultiFrame [pair.left.val.map (fun b => UInt8.ofNat b.val),
                           pair.right.val.map (fun b => UInt8.ofNat b.val)] =
      Qsag.Aggregation.merkleNodeFrame (idx.val / 2 ^ level.val)
        (node.val.map (fun b => UInt8.ofNat b.val))
        (sibling.val.map (fun b => UInt8.ofNat b.val)) := by
  obtain ⟨hlt, htag, hord⟩ := (step_merkle_pair_order_some_iff idx level node sibling pair).mp h
  refine ⟨hlt, htag, ?_⟩
  rw [Nat.shiftRight_eq_div_pow] at hord
  rw [Qsag.Aggregation.merkleNodeFrame.public_eq_1]
  by_cases hpar : (idx.val / 2 ^ level.val) % 2 = 0
  · simp only [hpar, ↓reduceIte] at hord ⊢
    rw [hord.1, hord.2]
  · simp only [hpar, ↓reduceIte] at hord ⊢
    rw [hord.1, hord.2]

private theorem foldl_add_u64_eq_sum :
    ∀ (xs : List U64) (acc : Nat),
      xs.foldl (fun a x => a + x.val) acc = acc + (xs.map UScalar.val).sum
  | [], acc => by simp
  | x :: xs, acc => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, foldl_add_u64_eq_sum xs]
    omega

/-- `checked_quorum_sum` returns `some total` iff `counts` and `minimums` are non-empty,
    equal-length slices, `0 < minimum_global`, every shard meets its per-shard threshold
    `minimums[i] ≤ counts[i]`, and the exact mathematical natural-number sum `∑ counts[i]`
    satisfies `minimum_global ≤ ∑ counts[i] < 2^64` with `total.val = ∑ counts[i]`. -/
theorem checked_quorum_sum_sound_qsag
    (counts minimums : Slice U64) (minimum_global total : U64) :
    checked_quorum_sum counts minimums minimum_global = .ok (some total) ↔
      (counts.val ≠ [] ∧
       counts.val.length = minimums.val.length ∧
       0 < minimum_global.val ∧
       (∀ i (hi : i < counts.val.length) (hmi : i < minimums.val.length),
         0 < (minimums.val[i]'hmi).val ∧ (minimums.val[i]'hmi).val ≤ (counts.val[i]'hi).val) ∧
       total.val = (counts.val.map UScalar.val).sum ∧
       minimum_global.val ≤ total.val ∧
       (counts.val.map UScalar.val).sum < 2 ^ 64) := by
  rw [checked_quorum_sum_sound]
  unfold QuorumSumSpec
  have hsum : ∀ xs : List U64, natSumU64 xs = (xs.map UScalar.val).sum := by
    intro xs
    unfold natSumU64
    rw [foldl_add_u64_eq_sum, Nat.zero_add]
  rw [hsum]
  constructor
  · rintro ⟨hne, hlen, hg, hall, htot, hle, hmin⟩
    exact ⟨hne, hlen, hg, hall, htot, hmin, by omega⟩
  · rintro ⟨hne, hlen, hg, hall, htot, hmin, hlt⟩
    exact ⟨hne, hlen, hg, hall, htot, by omega, hmin⟩

/-! ## 7. `#tooth` Mutation-Sensitivity & Inhabitedness Witness for Canonical Welds -/

/-- 1. Exhibits a concrete nonzero coset point `x = 3 ∈ F_p^*` where `verify_cwyz_duet_fold_step`
       with canonical twiddles accepts `canonicalExt4 (hemVirtualFoldOracle ...)`;
    2. Perturbing the claimed `GoldilocksExt4` fold evaluation by `+1` causes `.ok false`;
    3. Replacing the canonical coset inverse twiddle `(2 * x)^-1` with `2^-1` causes `.ok false`. -/
theorem tooth_canonical_cwyz_fold_rejects_wrong_twiddle_and_forged_claim :
    let x := Qsag.Goldilocks.ofNat 3
    let v0 := canonicalExt4 Qsag.Aggregation.GoldilocksExt4.one
    let v1 := canonicalExt4 Qsag.Aggregation.GoldilocksExt4.zero
    let honest := Qsag.Exec.hemAffineDuetFold
      Qsag.Aggregation.GoldilocksExt4.one Qsag.Aggregation.GoldilocksExt4.zero
      x Qsag.Aggregation.GoldilocksExt4.zero
      Qsag.Aggregation.GoldilocksExt4.zero Qsag.Aggregation.GoldilocksExt4.zero
    let forged := Qsag.Aggregation.GoldilocksExt4.add honest Qsag.Aggregation.GoldilocksExt4.one
    let iyGood := canonicalFieldWord (Qsag.Goldilocks.mul
      (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)) (Qsag.Goldilocks.inv x))
    let iyBad := canonicalFieldWord (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2))
    let it := canonicalFieldWord (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2))
    let yy := canonicalFieldWord (Qsag.Goldilocks.mul x x)
    verify_cwyz_duet_fold_step v0 v1 iyGood it yy extZero extZero extZero
      (canonicalExt4 honest) = .ok true ∧
    verify_cwyz_duet_fold_step v0 v1 iyGood it yy extZero extZero extZero
      (canonicalExt4 forged) = .ok false ∧
    verify_cwyz_duet_fold_step v0 v1 iyBad it yy extZero extZero extZero
      (canonicalExt4 honest) = .ok false := by
  intro x v0 v1 honest forged iyGood iyBad it yy
  have hDomX : ([Qsag.Aggregation.GoldilocksExt4.embedBase x]).getD (2 * 0) Qsag.CommRingOps.one =
      Qsag.Aggregation.GoldilocksExt4.embedBase x := rfl
  have hDomY : ([Qsag.Aggregation.GoldilocksExt4.embedBase (Qsag.Goldilocks.mul x x)]).getD 0
      Qsag.CommRingOps.zero = Qsag.Aggregation.GoldilocksExt4.embedBase (Qsag.Goldilocks.mul x x) := rfl
  let curO : Nat → Qsag.Aggregation.GoldilocksExt4 :=
    fun i => if i = 0 then Qsag.Aggregation.GoldilocksExt4.one else Qsag.Aggregation.GoldilocksExt4.zero
  have ha : curO (2 * 0) = ext4Abs v0 := by simp [curO, v0, ext4Abs_canonicalExt4]
  have hb : curO (2 * 0 + 1) = ext4Abs v1 := by simp [curO, v1, ext4Abs_canonicalExt4]
  have hEqOracle := hemAffineDuetFold_eq_hemVirtualFoldOracle
    Qsag.Aggregation.GoldilocksExt4.one Qsag.Aggregation.GoldilocksExt4.zero
    Qsag.Aggregation.GoldilocksExt4.zero Qsag.Aggregation.GoldilocksExt4.zero
    Qsag.Aggregation.GoldilocksExt4.zero x
    [Qsag.Aggregation.GoldilocksExt4.embedBase x]
    [Qsag.Aggregation.GoldilocksExt4.embedBase (Qsag.Goldilocks.mul x x)]
    curO 0 hDomX hDomY rfl rfl
  have hAccept : verify_cwyz_duet_fold_step v0 v1 iyGood it yy extZero extZero extZero
      (canonicalExt4 honest) = .ok true := by
    apply (verify_cwyz_duet_fold_step_sound_qsag v0 v1 x extZero extZero extZero
      (canonicalExt4 honest)
      [Qsag.Aggregation.GoldilocksExt4.embedBase x]
      [Qsag.Aggregation.GoldilocksExt4.embedBase (Qsag.Goldilocks.mul x x)]
      curO 0 hDomX hDomY ha hb).mpr
    refine ⟨isCanonicalExt4_canonicalExt4 _, ?_⟩
    simp only [ext4Abs_canonicalExt4, ext4Abs_zero]
    exact hEqOracle
  have hRejectForged : verify_cwyz_duet_fold_step v0 v1 iyGood it yy extZero extZero extZero
      (canonicalExt4 forged) = .ok false := by
    rw [verify_cwyz_duet_fold_step_spec]
    congr 1
    apply decide_eq_false
    intro hEq
    have h1 : verify_cwyz_duet_fold_step v0 v1 iyGood it yy extZero extZero extZero
        (canonicalExt4 forged) = .ok true := by
      rw [verify_cwyz_duet_fold_step_spec]
      exact congrArg Result.ok (decide_eq_true hEq)
    have h2 := ((verify_cwyz_duet_fold_step_sound_qsag v0 v1 x extZero extZero extZero
      (canonicalExt4 forged)
      [Qsag.Aggregation.GoldilocksExt4.embedBase x]
      [Qsag.Aggregation.GoldilocksExt4.embedBase (Qsag.Goldilocks.mul x x)]
      curO 0 hDomX hDomY ha hb).mp h1).2
    simp only [ext4Abs_canonicalExt4, ext4Abs_zero] at h2
    have h3 : forged = honest := h2.trans hEqOracle.symm
    have hOneZero : Qsag.Aggregation.GoldilocksExt4.one = Qsag.Aggregation.GoldilocksExt4.zero := by
      have hsub := congrArg (fun w => Qsag.CommRingOps.sub w honest) h3
      have hlhs : Qsag.CommRingOps.sub
          (Qsag.Aggregation.GoldilocksExt4.add honest Qsag.Aggregation.GoldilocksExt4.one) honest =
          Qsag.Aggregation.GoldilocksExt4.one := by
        rw [agg_add, ← Qsag.QuarticGoldilocks.ring_add]
        constructive_ring
      have hrhs : Qsag.CommRingOps.sub honest honest = Qsag.Aggregation.GoldilocksExt4.zero := by
        rw [Qsag.LawfulCommRing.sub_self, quartic_ring_zero]
      exact hlhs.symm.trans (hsub.trans hrhs)
    rw [← quartic_ring_one, ← quartic_ring_zero] at hOneZero
    exact Qsag.LawfulField.zero_ne_one (F := Qsag.QuarticGoldilocks) hOneZero.symm
  have hRejectTwiddle : verify_cwyz_duet_fold_step v0 v1 iyBad it yy extZero extZero extZero
      (canonicalExt4 honest) = .ok false := by
    rw [verify_cwyz_duet_fold_step_spec]
    congr 1
    apply decide_eq_false
    intro hEq
    have hGoodEq : cwyzValue v0 v1 iyGood it yy extZero extZero extZero = canonicalExt4 honest :=
      ((verify_cwyz_duet_fold_step_sound v0 v1 iyGood it yy extZero extZero extZero
        (canonicalExt4 honest)).mp hAccept).symm
    have hSame := congrArg ext4Abs (hEq.trans hGoodEq.symm)
    -- Under theta = alpha = beta = 0, cwyzValue simplifies to (v0 - v1) * iy = 1 * iy = embedBase iy
    have hEval : ∀ iyW : U64,
        ext4Abs (cwyzValue v0 v1 iyW it yy extZero extZero extZero) =
          Qsag.Aggregation.GoldilocksExt4.embedBase (fieldAbs iyW) := by
      intro iyW
      rw [cwyzValue.public_eqs, ext4Abs_add, ext4Abs_mul, ext4Abs_add, ext4Abs_scale,
        ext4Abs_scale, ext4Abs_sub]
      simp only [v0, v1, ext4Abs_canonicalExt4, ext4Abs_zero, agg_add, agg_sub, agg_mul,
        ← Qsag.QuarticGoldilocks.ring_add, ← Qsag.QuarticGoldilocks.ring_sub,
        ← Qsag.QuarticGoldilocks.ring_mul, ← quartic_ring_zero, ← quartic_ring_one]
      constructive_ring
    rw [hEval iyBad, hEval iyGood] at hSame
    have hBase := Qsag.GoldilocksField.GoldilocksExt4.embedBase_injective hSame
    simp only [iyBad, iyGood, fieldAbs_canonicalFieldWord] at hBase
    -- Multiply (2^-1 = 2^-1 * 3^-1) on the left by 2 and right by 3 in Goldilocks: 3 = 1!
    have h2nz : Qsag.Goldilocks.ofNat 2 ≠ Qsag.Goldilocks.zero := by decide
    have h3nz : x ≠ Qsag.Goldilocks.zero := by decide
    have hm1 := congrArg (fun g => Qsag.CommRingOps.mul (Qsag.Goldilocks.ofNat 2)
      (Qsag.CommRingOps.mul g x)) hBase
    rw [← goldilocks_ring_mul] at hm1
    have hlhs : Qsag.CommRingOps.mul (Qsag.Goldilocks.ofNat 2)
        (Qsag.CommRingOps.mul (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)) x) = x := by
      rw [← Qsag.LawfulCommRing.mul_assoc, Qsag.Goldilocks.mul_inv_cancel h2nz,
        Qsag.LawfulCommRing.one_mul]
    have hrhs : Qsag.CommRingOps.mul (Qsag.Goldilocks.ofNat 2)
        (Qsag.CommRingOps.mul
          (Qsag.CommRingOps.mul (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2))
            (Qsag.Goldilocks.inv x)) x) = Qsag.CommRingOps.one := by
      calc
        Qsag.CommRingOps.mul (Qsag.Goldilocks.ofNat 2)
            (Qsag.CommRingOps.mul
              (Qsag.CommRingOps.mul (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2))
                (Qsag.Goldilocks.inv x)) x)
          = Qsag.CommRingOps.mul
              (Qsag.CommRingOps.mul (Qsag.Goldilocks.ofNat 2)
                (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)))
              (Qsag.CommRingOps.mul (Qsag.Goldilocks.inv x) x) := by constructive_ring
        _ = Qsag.CommRingOps.mul Qsag.CommRingOps.one Qsag.CommRingOps.one := by
            rw [Qsag.Goldilocks.mul_inv_cancel h2nz,
              Qsag.LawfulCommRing.mul_comm (Qsag.Goldilocks.inv x) x,
              Qsag.Goldilocks.mul_inv_cancel h3nz]
        _ = Qsag.CommRingOps.one := Qsag.LawfulCommRing.one_mul _
    have h3eq1 : x = Qsag.Goldilocks.one := by
      rw [hlhs, hrhs, Qsag.Goldilocks.ring_one] at hm1
      exact hm1
    exact absurd (congrArg Qsag.Goldilocks.val h3eq1) (by decide)
  exact ⟨hAccept, hRejectForged, hRejectTwiddle⟩

/-! ## 8. Composable `DataRefinement` (`FieldRefines`, `Ext4Refines`) & `WhirWp` Hoare-Triple Bridge

Connects `qsag-whir-verified`'s Aeneas `Std.Result` verifier kernels directly to
`Qsag.Exec.Tactic.SimulationKit`'s relational `DataRefinement` / `Rel1` / `Rel2` algebra
(`0 import all`, `0 Classical.choice`). -/

/-- Canonical relational refinement between `Qsag.Goldilocks` and limb-canonical MIR `U64`. -/
@[expose] def FieldRefines : Qsag.DataRefinement Qsag.Goldilocks U64 where
  Rel x w := IsCanonical w ∧ fieldAbs w = x

/-- Canonical relational refinement between `Qsag.Aggregation.GoldilocksExt4` (tower basis)
    and limb-canonical MIR `Ext4` (polynomial basis). -/
@[expose] def Ext4Refines : Qsag.DataRefinement Qsag.Aggregation.GoldilocksExt4 Ext4 where
  Rel z w := IsCanonicalExt4 w ∧ ext4Abs w = z

/-- Canonical relational refinement between bounded mathematical `Nat` and Aeneas `U64`. -/
@[expose] def U64NatRefines : Qsag.DataRefinement Nat U64 where
  Rel n w := n = w.val

/-- Total-correctness weakest precondition over `Aeneas.Std.Result` (`∃ v, m = .ok v ∧ post v`). -/
@[expose] def WhirWp {α : Type} (m : Result α) (post : α → Prop) : Prop :=
  ∃ v : α, m = .ok v ∧ post v

theorem whirWp_ok {α : Type} (v : α) (post : α → Prop) :
    WhirWp (.ok v) post ↔ post v := by
  constructor
  · rintro ⟨w, hEq, hPost⟩
    cases hEq
    exact hPost
  · intro hPost
    exact ⟨v, rfl, hPost⟩

theorem whirWp_mono {α : Type} {m : Result α} {P Q : α → Prop}
    (h : WhirWp m P) (hImp : ∀ v, P v → Q v) : WhirWp m Q := by
  rcases h with ⟨v, hEq, hP⟩
  exact ⟨v, hEq, hImp v hP⟩

theorem FieldRefines_canonicalFieldWord (x : Qsag.Goldilocks) :
    FieldRefines.Rel x (canonicalFieldWord x) :=
  ⟨isCanonical_canonicalFieldWord x, fieldAbs_canonicalFieldWord x⟩

theorem FieldRefines_iff_eq_canonicalFieldWord (x : Qsag.Goldilocks) (w : U64) :
    FieldRefines.Rel x w ↔ w = canonicalFieldWord x := by
  constructor
  · rintro ⟨hw, rfl⟩
    exact (canonicalFieldWord_fieldAbs hw).symm
  · rintro rfl
    exact FieldRefines_canonicalFieldWord x

theorem Ext4Refines_canonicalExt4 (z : Qsag.Aggregation.GoldilocksExt4) :
    Ext4Refines.Rel z (canonicalExt4 z) :=
  ⟨isCanonicalExt4_canonicalExt4 z, ext4Abs_canonicalExt4 z⟩

theorem Ext4Refines_iff_eq_canonicalExt4 (z : Qsag.Aggregation.GoldilocksExt4) (w : Ext4) :
    Ext4Refines.Rel z w ↔ w = canonicalExt4 z := by
  constructor
  · rintro ⟨hw, rfl⟩
    exact (canonicalExt4_ext4Abs hw).symm
  · rintro rfl
    exact Ext4Refines_canonicalExt4 z

theorem extAdd_rel2 :
    Qsag.Rel2 Ext4Refines Ext4Refines Ext4Refines Qsag.Aggregation.GoldilocksExt4.add extAdd := by
  rintro _ x _ y ⟨_, rfl⟩ ⟨_, rfl⟩
  exact ⟨extAdd_canonical x y, ext4Abs_add x y⟩

theorem extSub_rel2 :
    Qsag.Rel2 Ext4Refines Ext4Refines Ext4Refines Qsag.Aggregation.GoldilocksExt4.sub extSub := by
  rintro _ x _ y ⟨_, rfl⟩ ⟨_, rfl⟩
  exact ⟨extSub_canonical x y, ext4Abs_sub x y⟩

theorem extMul_rel2 :
    Qsag.Rel2 Ext4Refines Ext4Refines Ext4Refines Qsag.Aggregation.GoldilocksExt4.mul extMul := by
  rintro _ x _ y ⟨_, rfl⟩ ⟨_, rfl⟩
  exact ⟨extMul_canonical x y, ext4Abs_mul x y⟩

theorem extInv_rel1 :
    Qsag.Rel1 Ext4Refines Ext4Refines Qsag.Aggregation.GoldilocksExt4.inv extInv := by
  rintro _ x ⟨_, rfl⟩
  exact ⟨isCanonicalExt4_extInv x, ext4Abs_inv x⟩

private theorem isCanonicalExt4_quadraticWireValue (c0 c2 sum_claim r : Ext4) :
    IsCanonicalExt4 (quadraticWireValue c0 c2 sum_claim r) := by
  rw [quadraticWireValue.public_eqs]
  exact extAdd_canonical _ _

/-- `WhirWp` + `Ext4Refines.option` specification for `decode_canonical_ext4`. -/
theorem decode_canonical_ext4_wp_ext4Refines (a b c d : U64) :
    WhirWp (decode_canonical_ext4 a b c d)
      (Ext4Refines.option.Rel
        (if a.val < Qsag.goldilocksPrime ∧ b.val < Qsag.goldilocksPrime ∧
            c.val < Qsag.goldilocksPrime ∧ d.val < Qsag.goldilocksPrime
         then some (Qsag.Math.aggOfPolynomial ⟨fieldAbs a, fieldAbs b, fieldAbs c, fieldAbs d⟩)
         else none)) := by
  rw [decode_canonical_ext4_spec, whirWp_ok]
  have hp : IsCanonical a ∧ IsCanonical b ∧ IsCanonical c ∧ IsCanonical d ↔
      a.val < Qsag.goldilocksPrime ∧ b.val < Qsag.goldilocksPrime ∧
      c.val < Qsag.goldilocksPrime ∧ d.val < Qsag.goldilocksPrime := Iff.rfl
  by_cases h : IsCanonical a ∧ IsCanonical b ∧ IsCanonical c ∧ IsCanonical d
  · have h' := hp.mp h
    simp only [h, h', Qsag.DataRefinement.option, Ext4Refines]
    exact ⟨h, rfl⟩
  · have h' : ¬ (a.val < Qsag.goldilocksPrime ∧ b.val < Qsag.goldilocksPrime ∧
        c.val < Qsag.goldilocksPrime ∧ d.val < Qsag.goldilocksPrime) := fun hc => h (hp.mpr hc)
    simp only [h, h', ↓reduceIte, Qsag.DataRefinement.option]

/-- `WhirWp` + `Ext4Refines` specification for `fold_duet_affine_ext4`, discharging the
    `hit`/`hiy`/`hyy` inverse twiddle obligations directly from `FieldRefines`. -/
theorem fold_duet_affine_ext4_wp_ext4Refines
    {v0s v1s ts as_ bs : Qsag.Aggregation.GoldilocksExt4}
    {v0 v1 theta alpha beta : Ext4}
    {x : Qsag.Goldilocks} {iy it yy : U64}
    (hv0 : Ext4Refines.Rel v0s v0) (hv1 : Ext4Refines.Rel v1s v1)
    (ht : Ext4Refines.Rel ts theta) (ha : Ext4Refines.Rel as_ alpha)
    (hb : Ext4Refines.Rel bs beta)
    (hiy : FieldRefines.Rel
      (Qsag.Goldilocks.mul (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)) (Qsag.Goldilocks.inv x)) iy)
    (hit : FieldRefines.Rel (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)) it)
    (hyy : FieldRefines.Rel (Qsag.Goldilocks.mul x x) yy) :
    WhirWp (fold_duet_affine_ext4 v0 v1 iy it yy theta alpha beta)
      (Ext4Refines.Rel (Qsag.Exec.hemAffineDuetFold v0s v1s x ts as_ bs)) := by
  have hMap := fold_duet_affine_ext4_refines_exec v0 v1 iy it yy theta alpha beta x
    hit.2 hiy.2 hyy.2
  rw [fold_duet_affine_ext4_spec] at hMap ⊢
  rw [whirWp_ok]
  have hVal : ext4Abs (cwyzValue v0 v1 iy it yy theta alpha beta) =
      Qsag.Exec.hemAffineDuetFold v0s v1s x ts as_ bs := by
    have hInj : ext4Abs (cwyzValue v0 v1 iy it yy theta alpha beta) =
        Qsag.Exec.hemAffineDuetFold (ext4Abs v0) (ext4Abs v1) x
          (ext4Abs theta) (ext4Abs alpha) (ext4Abs beta) := Result.ok.inj hMap
    rw [hv0.2, hv1.2, ht.2, ha.2, hb.2] at hInj
    exact hInj
  exact ⟨isCanonicalExt4_cwyzValue v0 v1 iy it yy theta alpha beta, hVal⟩

/-- `WhirWp` + `Ext4Refines` specification for `cwyz_bridge_claim_step` into canonical
    `Qsag.hemBridgeFoldClaim`. -/
theorem cwyz_bridge_claim_step_wp_ext4Refines
    {w0s w1s w2s w3s w4s claims phis thetas alphas betas : Qsag.Aggregation.GoldilocksExt4}
    {w0 w1 w2 w3 w4 claim phi theta alpha beta : Ext4}
    (hw0 : Ext4Refines.Rel w0s w0) (hw1 : Ext4Refines.Rel w1s w1)
    (hw2 : Ext4Refines.Rel w2s w2) (hw3 : Ext4Refines.Rel w3s w3)
    (hw4 : Ext4Refines.Rel w4s w4) (hc : Ext4Refines.Rel claims claim)
    (hp : Ext4Refines.Rel phis phi) (ht : Ext4Refines.Rel thetas theta)
    (ha : Ext4Refines.Rel alphas alpha) (hb : Ext4Refines.Rel betas beta) :
    WhirWp (cwyz_bridge_claim_step w0 w1 w2 w3 w4 claim phi theta alpha beta)
      (Ext4Refines.Rel
        (Qsag.hemBridgeFoldClaim claims w0s w1s w2s w3s w4s phis thetas alphas betas)) := by
  have hExec := cwyz_bridge_refines_exec w0 w1 w2 w3 w4 claim phi theta alpha beta
  rw [cwyz_bridge_claim_step_refines] at hExec ⊢
  rw [whirWp_ok]
  have hVal : ext4Abs (cwyzBridgeValue w0 w1 w2 w3 w4 claim phi theta alpha beta) =
      Qsag.hemBridgeFoldClaim claims w0s w1s w2s w3s w4s phis thetas alphas betas := by
    have h1 := (Result.ok.inj hExec).trans
      (hemBridgeClaimStep_eq_hemBridgeFoldClaim _ _ _ _ _ _ _ _ _ _)
    rw [hw0.2, hw1.2, hw2.2, hw3.2, hw4.2, hc.2, hp.2, ht.2, ha.2, hb.2] at h1
    exact h1
  exact ⟨isCanonicalExt4_cwyzBridgeValue w0 w1 w2 w3 w4 claim phi theta alpha beta, hVal⟩

/-- `WhirWp` + `Ext4Refines` specification for `eval_quadratic_sumcheck_wire` into
    `Qsag.RoundPoly.evalCoeffs`. -/
theorem eval_quadratic_sumcheck_wire_wp_ext4Refines
    {c0s c2s claims rs : Qsag.Aggregation.GoldilocksExt4}
    {c0 c2 sum_claim r : Ext4}
    (hc0 : Ext4Refines.Rel c0s c0) (hc2 : Ext4Refines.Rel c2s c2)
    (hcl : Ext4Refines.Rel claims sum_claim) (hr : Ext4Refines.Rel rs r) :
    WhirWp (eval_quadratic_sumcheck_wire c0 c2 sum_claim r)
      (Ext4Refines.Rel
        (Qsag.RoundPoly.evalCoeffs (canonicalQuadraticWirePoly c0s c2s claims) rs)) := by
  have hRef := eval_quadratic_sumcheck_wire_refines_qsag c0 c2 sum_claim r
  rw [eval_quadratic_sumcheck_wire_refines] at hRef ⊢
  rw [whirWp_ok]
  have hVal : ext4Abs (quadraticWireValue c0 c2 sum_claim r) =
      Qsag.RoundPoly.evalCoeffs (canonicalQuadraticWirePoly c0s c2s claims) rs := by
    have h1 := Result.ok.inj hRef
    rw [hc0.2, hc2.2, hcl.2, hr.2] at h1
    exact h1
  exact ⟨isCanonicalExt4_quadraticWireValue c0 c2 sum_claim r, hVal⟩

/-- `WhirWp` Hoare-triple specification for `verify_ood_pin_eq` over canonical `GoldilocksExt4` OOD vectors. -/
theorem verify_ood_pin_eq_wp_ext4Refines
    (expected supplied : Slice U64)
    (expPins supPins : List Qsag.Aggregation.GoldilocksExt4)
    (he : expected.val = ext4SliceWords expPins)
    (hs : supplied.val = ext4SliceWords supPins) :
    WhirWp (verify_ood_pin_eq expected supplied) (fun ok => ok = true ↔ expPins = supPins) := by
  rw [verify_ood_pin_eq_spec, whirWp_ok, he, hs, decide_eq_true_eq]
  exact ⟨ext4SliceWords_injective, congrArg ext4SliceWords⟩

/-- `WhirWp` + `U64NatRefines` specification for `checked_quorum_sum`. -/
theorem checked_quorum_sum_wp_u64NatRefines
    (counts minimums : Slice U64) (minimum_global : U64) :
    WhirWp (checked_quorum_sum counts minimums minimum_global)
      (fun out => ∀ total : U64, out = some total ↔
        (counts.val ≠ [] ∧
         counts.val.length = minimums.val.length ∧
         0 < minimum_global.val ∧
         (∀ i (hi : i < counts.val.length) (hmi : i < minimums.val.length),
           0 < (minimums.val[i]'hmi).val ∧ (minimums.val[i]'hmi).val ≤ (counts.val[i]'hi).val) ∧
         U64NatRefines.Rel (counts.val.map UScalar.val).sum total ∧
         minimum_global.val ≤ total.val ∧
         (counts.val.map UScalar.val).sum < 2 ^ 64)) := by
  obtain ⟨out, hOut⟩ := checked_quorum_sum_total counts minimums minimum_global
  refine ⟨out, hOut, fun total => ?_⟩
  have hIff := checked_quorum_sum_sound_qsag counts minimums minimum_global total
  rw [hOut, Result.ok.injEq] at hIff
  refine hIff.trans ?_
  simp only [U64NatRefines, eq_comm (a := total.val)]

#verify_constructive
  fieldAbs_canonicalFieldWord
  ext4Abs_canonicalExt4
  ext4Abs_inv
  ext_mul_extInv_ok_one
  canonicalFieldWord_two_inv
  canonicalFieldWord_two_x_inv
  decode_canonical_u64_refines_qsag
  decode_canonical_ext4_refines_qsag
  embedBase_inv
  hemAffineDuetFold_eq_hemVirtualFoldOracle
  fold_duet_affine_ext4_canonical_twiddles
  fold_duet_affine_ext4_refines_hemVirtualFoldOracle
  verify_cwyz_duet_fold_step_sound_qsag
  verify_affine_duet_fold_step_sound_qsag
  verify_affine_duet_fold_step_roots_le_one
  verify_cwyz_bridge_claim_step_sound_qsag
  affine_cascade_claim_step_refines_evalCascadeClaim
  eval_quadratic_sumcheck_wire_refines_qsag
  eval_quadratic_sumcheck_wire_bad_challenges_le_two
  eval_ext4_univariate_at_base_refines_evalCoeffs
  verify_ext4_univariate_at_base_pin_sound_qsag
  verify_ext4_univariate_at_base_pin_roots_le_degree
  verify_ood_pin_eq_canonical_ext4_iff
  verify_stage_pow_mask_refines_canonical
  verify_stage_pow_mask_16_iff_verifyWhirStagePow
  step_merkle_pair_order_canonical_parity
  checked_quorum_sum_sound_qsag
  tooth_canonical_cwyz_fold_rejects_wrong_twiddle_and_forged_claim
  whirWp_ok
  whirWp_mono
  FieldRefines_canonicalFieldWord
  FieldRefines_iff_eq_canonicalFieldWord
  Ext4Refines_canonicalExt4
  Ext4Refines_iff_eq_canonicalExt4
  extAdd_rel2
  extSub_rel2
  extMul_rel2
  extInv_rel1
  decode_canonical_ext4_wp_ext4Refines
  fold_duet_affine_ext4_wp_ext4Refines
  cwyz_bridge_claim_step_wp_ext4Refines
  eval_quadratic_sumcheck_wire_wp_ext4Refines
  verify_ood_pin_eq_wp_ext4Refines
  checked_quorum_sum_wp_u64NatRefines

end qsag_whir_verified.proofs
end
