module
/-
# The same claim-preserving fold relation in the coding and transcript representations

The incidence development uses canonical `UPoly`; the Hem state-function development uses
coefficient lists. Their polynomial explanation predicates are equivalent, including the
identity of the selected post-fold polynomial. No uniqueness-radius premise is required.
-/
public import Qsag.HemWhirRbrSoundness
public import Qsag.CodingTheory.PersistentPairsBound
import all Qsag.HemWhirRbrSoundness
import all Qsag.CodingTheory.PolyMv3
import all Qsag.MultiRoundFsQrom
import all Qsag.AffineProximityGaps

public section
namespace Qsag
set_option autoImplicit false

private theorem polyAddVar_eq_rawAddCoeffs {F : Type} [CommRingOps F] :
    ∀ a b : List F, polyAddVar a b = rawAddCoeffs a b
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => congrArg (CommRingOps.add a b :: ·) (polyAddVar_eq_rawAddCoeffs as bs)

theorem ofList_polyAddVar {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) :
    UPoly.ofList (polyAddVar a b) = CommRingOps.add (UPoly.ofList a) (UPoly.ofList b) := by
  apply UPoly.ext_coeffAt
  intro k
  rw [UPoly.coeffAt_ofList, UPoly.coeffAt_add, UPoly.coeffAt_ofList, UPoly.coeffAt_ofList,
    polyAddVar_eq_rawAddCoeffs, coeffAt_addCoeffs]

theorem ofList_polyScaleVar {F : Type} [LawfulCommRing F] [DecidableEq F] (c : F) (a : List F) :
    UPoly.ofList (polyScaleVar c a) = CommRingOps.mul (UPoly.C c) (UPoly.ofList a) := by
  apply UPoly.ext_coeffAt
  intro k
  rw [UPoly.coeffAt_ofList, UPoly.coeffAt_C_mul, UPoly.coeffAt_ofList]
  exact coeffAt_map_mul c a k

theorem ofList_shiftPoly {F : Type} [LawfulCommRing F] [DecidableEq F] (a : List F) :
    UPoly.ofList (shiftPoly a) = CommRingOps.mul UPoly.X (UPoly.ofList a) := by
  apply UPoly.ext_coeffAt
  intro k
  rw [UPoly.coeffAt_ofList]
  cases k with
  | zero => rw [UPoly.coeffAt_X_mul_zero]; rfl
  | succ k => rw [UPoly.coeffAt_X_mul_succ, UPoly.coeffAt_ofList]; rfl

theorem ofList_affineClaimCombine {F : Type} [LawfulCommRing F] [DecidableEq F]
    (α β : F) (Fp Gp : List F) :
    UPoly.ofList (polyAddVar Fp
      (polyAddVar (polyScaleVar α Gp) (polyScaleVar β (shiftPoly Gp)))) =
    CommRingOps.add (UPoly.ofList Fp)
      (CommRingOps.mul (Poly3.line α β) (UPoly.ofList Gp)) := by
  rw [ofList_polyAddVar, ofList_polyAddVar, ofList_polyScaleVar, ofList_polyScaleVar,
    ofList_shiftPoly, Poly3.line, UPoly.ofList_cons]
  change CommRingOps.add (UPoly.ofList Fp)
    (CommRingOps.add (CommRingOps.mul (UPoly.C α) (UPoly.ofList Gp))
      (CommRingOps.mul (UPoly.C β) (CommRingOps.mul UPoly.X (UPoly.ofList Gp)))) =
    CommRingOps.add (UPoly.ofList Fp)
      (CommRingOps.mul (CommRingOps.add (UPoly.C α) (CommRingOps.mul UPoly.X (UPoly.C β)))
        (UPoly.ofList Gp))
  constructive_ring

/-- The selected-polynomial incidence predicate is exactly the transcript decomposition
    predicate. Ordinary existential proximity alone would not establish this equivalence. -/
theorem hasPolynomialExplanation_iff_decomposes {F : Type} [LawfulField F] [DecidableEq F]
    (x : (F → F) × (F → F)) (D : List F) (d B : Nat) (α β : F) (P : List F) :
    HasPolynomialExplanation x D d B α β (UPoly.ofList P) ↔
      DecomposesViaCorrelatedPair d B x.1 x.2 D α β P := by
  constructor
  · rintro ⟨Fp, Gp, hF, hG, hAg, hEq⟩
    refine ⟨Fp, Gp, ⟨hF, hG, hAg⟩, ?_⟩
    have he := (ofList_affineClaimCombine α β Fp Gp).trans hEq
    exact (congrArg UPoly.coeffs he).symm
  · rintro ⟨Fp, Gp, ⟨hF, hG, hAg⟩, hEq⟩
    refine ⟨Fp, Gp, hF, hG, hAg, ?_⟩
    rw [← ofList_affineClaimCombine]
    exact UPoly.ext hEq.symm

#verify_constructive
  Qsag.ofList_polyAddVar
  Qsag.ofList_polyScaleVar
  Qsag.ofList_shiftPoly
  Qsag.ofList_affineClaimCombine
  Qsag.hasPolynomialExplanation_iff_decomposes
end Qsag
