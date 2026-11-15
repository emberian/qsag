module
/-
# Constructive finite plane intersection count

A primitive plane curve has no vertical component. Its intersection with a curve coprime
in the vertical variable is bounded by counting projected resultant roots and then roots
in each fiber. This gives a cubic degree bound, avoiding a separating shear or an infinite
base field. Repeated first coordinates are permitted; primitivity is essential.
-/
public import Qsag.CodingTheory.BivariateGauss
public import Qsag.CodingTheory.SylvesterElimination
public import Qsag.CodingTheory.JohnsonSetSystem
public import Qsag.CodingTheory.AffineIncidenceBound
import all Qsag.CodingTheory.BivariateGauss
import all Qsag.CodingTheory.SylvesterElimination
import all Qsag.CodingTheory.SylvesterResultant
import all Qsag.CodingTheory.DynamicGcdSplit
import all Qsag.CodingTheory.AffineIncidenceBound
import all Qsag.Goldilocks

public section
namespace Qsag
open CommRingOps RoundPoly UPoly
namespace Poly2
variable {F : Type} [LawfulField F] [DecidableEq F]
local instance planeNoZeroDivisors : NoZeroDivisors F := LawfulField.toNoZeroDivisors F

/-- Every vertical specialization of a primitive curve is a nonzero polynomial. -/
theorem IsPrimY.specialize_ne_zero {A : Poly2 F} (hA : IsPrimY A) (y : F) :
    (mapHom (evalHom y)).toFun A ≠ zero := by
  intro hzero
  have hcoeff : ∀ k, (coeffAt A.coeffs k).eval y = zero := by
    intro k
    have he := congrArg (fun p : UPoly F => coeffAt p.coeffs k) hzero
    simpa only [coeffAt_mapHom, evalHom_apply, coeffs_zero, coeffAt_nil] using he
  have hdeg := hA.2 (sub X (C y)) (fun k => by
    obtain ⟨he, _⟩ := SylElim.divXSub_spec (coeffAt A.coeffs k) y
    rw [hcoeff k, C_zero_eq, LawfulCommRing.zero_add] at he
    exact ⟨_, he⟩)
  have htop := (sub X (C y)).coeffAt_eq_zero_of_natDeg_lt (k := 1) (by omega)
  rw [coeffAt_sub, coeffAt_C_succ] at htop
  have hx : coeffAt (X : UPoly F).coeffs 1 = one := by
    change coeffAt (ofList [zero, one]).coeffs 1 = one
    rw [coeffAt_ofList]; rfl
  rw [hx, LawfulCommRing.sub_zero] at htop
  exact LawfulField.one_ne_zero htop

/-- A primitive curve of vertical degree `m` has at most `m` points in each vertical fiber. -/
theorem IsPrimY.fiber_card_le {A : Poly2 F} (hA : IsPrimY A) (y : F)
    (pts : List (F × F)) (hnd : pts.Nodup)
    (hy : ∀ p ∈ pts, p.1 = y)
    (hroot : ∀ p ∈ pts, A.eval2 p.1 p.2 = zero) :
    pts.length ≤ A.natDeg := by
  let Ay := (mapHom (evalHom y)).toFun A
  have hAy := hA.specialize_ne_zero y
  have hndy : (pts.map Prod.snd).Nodup := by
    apply (List.pairwise_map.mpr ?_)
    exact JohnsonBound.pairwise_of_nodup hnd (fun p hp q hq hne he =>
      hne (Prod.ext ((hy p hp).trans (hy q hq).symm) he))
  have hbound := gs_formal_root_bound A.natDeg Ay.coeffs (pts.map Prod.snd)
    (by have hd := natDeg_mapHom_le (evalHom y) A
        change Ay.coeffs.length - 1 ≤ A.natDeg at hd
        omega)
    (exists_mem_ne_zero_of_coeffAt _ _ (lead_ne_zero hAy)) hndy
    (fun z hz => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
      rw [← UPoly.eval_eq]
      change eval₂ (RingHom.id F) p.2 ((mapHom (evalHom y)).toFun A) = zero
      rw [eval₂_mapHom]
      have hr := hroot p hp
      rw [hy p hp] at hr
      exact hr)
  rwa [List.length_map] at hbound

/-- A finite intersection bound with no distinct-projection premise. The extra vertical
factor is the price of using a fiber count rather than a generic separating shear. -/
theorem primitive_common_roots_card_le (A B : Poly2 F) (hprim : IsPrimY A)
    (hA : 1 ≤ A.natDeg) (hB : B ≠ zero) (hcop : CoprimeZ A B)
    (pts : List (F × F)) (hnd : pts.Nodup)
    (hroots : ∀ p ∈ pts, A.eval2 p.1 p.2 = zero ∧ B.eval2 p.1 p.2 = zero) :
    pts.length ≤ tdeg A * tdeg B * A.natDeg := by
  let ys := JohnsonBound.dedupFirst (pts.map Prod.fst)
  have hys : ys.length ≤ tdeg A * tdeg B := by
    have hr := (resZ_ne_zero_iff A B hA hB).mpr hcop
    have hd := natDeg_resZ_le A B hA
    apply gs_formal_root_bound (tdeg A * tdeg B) (resZ A B).coeffs ys
      (by change (resZ A B).coeffs.length - 1 ≤ _ at hd; omega)
      (exists_mem_ne_zero_of_coeffAt _ _ (lead_ne_zero hr))
      (JohnsonBound.dedupFirst_nodup _)
    intro y hy
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ((JohnsonBound.mem_dedupFirst_iff y _).mp hy)
    rw [← UPoly.eval_eq]
    exact eval_resZ_eq_zero A B hA p.1 p.2 (hroots p hp).1 (hroots p hp).2
  have hcount := JohnsonBound.count_partition_le Prod.fst A.natDeg pts ys
    (fun p hp => (JohnsonBound.mem_dedupFirst_iff p.1 _).mpr (List.mem_map.mpr ⟨p, hp, rfl⟩))
    (fun y _ => hprim.fiber_card_le y (pts.filter (fun p => decide (p.1 = y)))
      (nodup_filter _ pts hnd)
      (fun p hp => of_decide_eq_true (List.mem_filter.mp hp).2)
      (fun p hp => (hroots p (List.mem_filter.mp hp).1).1))
  exact Nat.le_trans hcount (Nat.mul_le_mul_right _ hys)

#verify_constructive IsPrimY.specialize_ne_zero IsPrimY.fiber_card_le primitive_common_roots_card_le
end Poly2

namespace PlaneBezoutTests
open Poly2
private theorem primitive_of_monic (A : Poly2 Goldilocks) (k : Nat)
    (hk : coeffAt A.coeffs k = one) : IsPrimY A := by
  refine ⟨fun he => NontrivialRing.one_ne_zero (by
    rw [← hk, he, coeffs_zero, coeffAt_nil]), fun g hg => ?_⟩
  obtain ⟨q, hq⟩ := hg k
  rw [hk] at hq
  have hg0 : g ≠ zero := fun e => NontrivialRing.one_ne_zero (by
    rw [hq, e, LawfulCommRing.zero_mul])
  have hq0 : q ≠ zero := fun e => NontrivialRing.one_ne_zero (by
    rw [hq, e, LawfulCommRing.mul_zero])
  have hd := UPoly.natDeg_mul hg0 hq0
  rw [← hq, natDeg_one] at hd
  omega

/-- Two intersections sharing their first coordinate: the new theorem applies where
`common_roots_card_le_mul_deg`'s distinct-projection premise does not. -/
theorem inhabited_primitive_common_roots :
    ∃ (A B : Poly2 Goldilocks) (pts : List (Goldilocks × Goldilocks)),
      IsPrimY A ∧ 1 ≤ A.natDeg ∧ B ≠ zero ∧ CoprimeZ A B ∧ pts.Nodup ∧
      (∀ p ∈ pts, A.eval2 p.1 p.2 = zero ∧ B.eval2 p.1 p.2 = zero) ∧
      pts.length = 2 ∧ ¬ (pts.map Prod.fst).Nodup := by
  let A : Poly2 Goldilocks := ofList [zero, neg one, one]
  let B : Poly2 Goldilocks := C X
  refine ⟨A, B, [(zero, zero), (zero, one)],
    primitive_of_monic A 2 (by decide +kernel), by decide +kernel,
    by decide +kernel, ?_, by decide +kernel, by decide +kernel, rfl, by decide +kernel⟩
  refine ⟨zero, one, X, by decide +kernel, ?_⟩
  rw [LawfulCommRing.zero_mul, LawfulCommRing.one_mul, LawfulCommRing.zero_add]

/-- Vertical common components show why coprimality over the rational-function field
alone cannot bound finite plane intersections. -/
theorem tooth_common_roots_needs_primitive :
    ∃ (A B : Poly2 Goldilocks) (pts : List (Goldilocks × Goldilocks)),
      1 ≤ A.natDeg ∧ B ≠ zero ∧ CoprimeZ A B ∧ pts.Nodup ∧
      (∀ p ∈ pts, A.eval2 p.1 p.2 = zero ∧ B.eval2 p.1 p.2 = zero) ∧
      ¬ pts.length ≤ tdeg A * tdeg B * A.natDeg := by
  let A : Poly2 Goldilocks := ofList [zero, X]
  let B : Poly2 Goldilocks := C X
  refine ⟨A, B, [(zero, zero), (zero, one), (zero, Goldilocks.ofNat 2)],
    by decide +kernel, by decide +kernel, ?_, by decide +kernel,
    by decide +kernel, by decide +kernel⟩
  refine ⟨zero, one, X, by decide +kernel, ?_⟩
  rw [LawfulCommRing.zero_mul, LawfulCommRing.one_mul, LawfulCommRing.zero_add]

#verify_constructive inhabited_primitive_common_roots tooth_common_roots_needs_primitive
#verify_inhabited primitive_common_roots_card_le inhabited_primitive_common_roots
#tooth_pair primitive_common_roots_card_le vs tooth_common_roots_needs_primitive
end PlaneBezoutTests
end Qsag
end
