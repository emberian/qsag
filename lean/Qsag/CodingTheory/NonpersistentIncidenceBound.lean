module
/-
# Constructive curve incidence bound

This is the dimension-one incidence step of CWYZ Claim 4.8. A primitive curve already
refined against the coordinate equations has either a contained coordinate or a finite
intersection certified by a coprime eliminant. Pairwise agreement bounds control the
contained coordinates; double counting controls all remaining incidences.

The surface-to-curve projection and its multiple-root components are not proved here.
-/
public import Qsag.CodingTheory.PlaneBezoutResultant
public import Qsag.CodingTheory.PersistentPairsBound
public import Qsag.CodingTheory.BivariateFactorSplit
import all Qsag.CodingTheory.PlaneBezoutResultant
import all Qsag.CodingTheory.PersistentPairsBound
import all Qsag.CodingTheory.JohnsonSetSystem
import all Qsag.CodingTheory.PolyMv3
import all Qsag.CodingTheory.SylvesterResultant
import all Qsag.Goldilocks
import all Qsag.AffineProximityGaps
import all Qsag.CodingTheory.DynamicGcdSplit
import all Qsag.CodingTheory.BivariateGauss
import all Qsag.CodingTheory.BivariateFactorSplit

public section
namespace Qsag
open CommRingOps RoundPoly UPoly
namespace NonpersistentIncidence

/-- Incidence double counting with the coordinates common to every candidate removed.
The pairwise hypothesis is used only to bound those common coordinates. -/
theorem incidence_mul_le {Point Coord : Type} [DecidableEq Coord]
    (pts : List Point) (D : List Coord) (agree : Point → Coord → Bool)
    (A B K : Nat) (hD : D.Nodup) (hnd : pts.Nodup) (htwo : 2 ≤ pts.length)
    (hsize : ∀ p ∈ pts, A ≤ (D.filter (agree p)).length)
    (hshared : ∀ p ∈ pts, ∀ q ∈ pts, p ≠ q →
      (D.filter (fun z => agree p z && agree q z)).length ≤ B)
    (hfiber : ∀ z ∈ D, ¬ (∀ p ∈ pts, agree p z = true) →
      (pts.filter (fun p => agree p z)).length ≤ K) :
    pts.length * (A - B) ≤ D.length * K := by
  let inside : Coord → Bool := fun z => pts.all (fun p => agree p z)
  have hins : ∀ z, inside z = true ↔ ∀ p ∈ pts, agree p z = true := by
    intro z
    exact List.all_eq_true
  have hcommon : (D.filter inside).length ≤ B := by
    cases pts with
    | nil => simp at htwo
    | cons p tail =>
      cases tail with
      | nil => simp at htwo
      | cons q rest =>
        have hpq : p ≠ q := (List.pairwise_cons.mp hnd).1 q (.head _)
        have hb := hshared p (.head _) q (.tail _ (.head _)) hpq
        apply Nat.le_trans (nodup_length_le_of_subset (nodup_filter _ D hD) ?_) hb
        intro z hz
        obtain ⟨hzD, hzall⟩ := List.mem_filter.mp hz
        exact List.mem_filter.mpr ⟨hzD, Bool.and_eq_true_iff.mpr
          ⟨(hins z).mp hzall p (.head _), (hins z).mp hzall q (.tail _ (.head _))⟩⟩
  let remaining : Point → Coord → Bool := fun p z => !inside z && agree p z
  have hremain : ∀ p ∈ pts, A - B ≤ (D.filter (remaining p)).length := by
    intro p hp
    have hc := JohnsonBound.filter_length_le_add (agree p) inside (remaining p) D
      (fun z _ hz => by
        cases hi : inside z with
        | true => exact .inl rfl
        | false => exact .inr (by simp only [remaining, hi]; exact hz))
    have ha := hsize p hp
    omega
  have hfib : ∀ z ∈ D, JohnsonBound.ptDeg remaining pts z ≤ K := by
    intro z hz
    cases hi : inside z with
    | true =>
      have he : pts.filter (fun p => remaining p z) = [] := by
        have hf : ∀ xs : List Point, xs.filter (fun _ => false) = [] := by
          intro xs
          induction xs with
          | nil => rfl
          | cons _ _ ih => exact ih
        simpa only [remaining, hi, Bool.not_true, Bool.false_and] using hf pts
      change (pts.filter (fun p => remaining p z)).length ≤ K
      rw [he]; exact Nat.zero_le _
    | false =>
      have hn : ¬ (∀ p ∈ pts, agree p z = true) := fun h =>
        Bool.false_ne_true (hi.symm.trans ((hins z).mpr h))
      have he : (fun p => remaining p z) = (fun p => agree p z) := by
        funext p; simp only [remaining, hi, Bool.not_false, Bool.true_and]
      change (pts.filter (fun p => remaining p z)).length ≤ K
      rw [he]; exact hfiber z hz hn
  have hlo := JohnsonBound.sumNat_map_le (fun _ => A - B)
    (fun p => (D.filter (remaining p)).length) pts hremain
  rw [JohnsonBound.sumNat_map_const] at hlo
  have hhi := JohnsonBound.sumNat_map_le (JohnsonBound.ptDeg remaining pts)
    (fun _ => K) D hfib
  rw [JohnsonBound.sumNat_map_const, JohnsonBound.sum_ptDeg_eq] at hhi
  exact Nat.le_trans hlo hhi

variable {F : Type} [LawfulField F] [DecidableEq F]
local instance : NoZeroDivisors F := LawfulField.toNoZeroDivisors F
open Poly2

/-- Dimension-one incidence count on a primitive component refined against each coordinate
polynomial. The denominator is `A-B`, not a unique-decoding overlap requirement. -/
theorem curve_incidence_card_le {Coord : Type} [DecidableEq Coord] (C : Poly2 F) (hprim : IsPrimY C) (hC : 1 ≤ C.natDeg)
    (D : List Coord) (hD : D.Nodup) (equation : Coord → Poly2 F) (M A B : Nat)
    (hAB : B < A) (hdegree : ∀ z ∈ D, tdeg (equation z) ≤ M)
    (hrefined : ∀ z ∈ D, (∃ Q, equation z = mul C Q) ∨ CoprimeZ C (equation z))
    (pts : List (F × F)) (hnd : pts.Nodup)
    (hcurve : ∀ p ∈ pts, C.eval2 p.1 p.2 = zero)
    (hsize : ∀ p ∈ pts,
      A ≤ (D.filter (fun z => decide ((equation z).eval2 p.1 p.2 = zero))).length)
    (hshared : ∀ p ∈ pts, ∀ q ∈ pts, p ≠ q →
      (D.filter (fun z => decide ((equation z).eval2 p.1 p.2 = zero) &&
        decide ((equation z).eval2 q.1 q.2 = zero))).length ≤ B) :
    pts.length ≤ Nat.max 1 ((D.length * (tdeg C * M * C.natDeg)) / (A - B)) := by
  if hsmall : pts.length ≤ 1 then exact Nat.le_trans hsmall (Nat.le_max_left _ _)
  else
    have htwo : 2 ≤ pts.length := by omega
    have hm := incidence_mul_le pts D (fun p z => decide ((equation z).eval2 p.1 p.2 = zero))
      A B (tdeg C * M * C.natDeg) hD hnd htwo hsize hshared (fun z hz hnonfull => by
        rcases hrefined z hz with ⟨Q, hQ⟩ | hcop
        · exact False.elim (hnonfull (fun p hp => decide_eq_true (by
            rw [hQ]
            change (eval₂Hom (evalHom p.1) p.2).toFun (mul C Q) = zero
            rw [RingHom.map_mul]
            change mul (C.eval2 p.1 p.2) (Q.eval2 p.1 p.2) = zero
            rw [hcurve p hp, LawfulCommRing.zero_mul])))
        · have hne : equation z ≠ zero := fun hzero =>
            hnonfull (fun p _ => decide_eq_true (by rw [hzero]; rfl))
          have hb := primitive_common_roots_card_le C (equation z) hprim hC hne hcop
            (pts.filter (fun p => decide ((equation z).eval2 p.1 p.2 = zero)))
            (nodup_filter _ pts hnd) (fun p hp =>
              ⟨hcurve p (List.mem_filter.mp hp).1, of_decide_eq_true (List.mem_filter.mp hp).2⟩)
          exact Nat.le_trans hb (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hdegree z hz))))
    exact Nat.le_trans ((Nat.le_div_iff_mul_le (by omega)).mpr hm) (Nat.le_max_right _ _)

/-- Nonpersistent accepted polynomials on a refined primitive curve satisfy the curve
incidence bound. The geometry may live over an extension field; the words and challenges
remain over their original field. The labels retain the specific accepted polynomial. -/
theorem nonpersistent_curve_card_le {E : Type} [LawfulField E] [DecidableEq E]
    (x : (E → E) × (E → E)) (D : List E) (hD : D.Nodup) (d A B M : Nat)
    (hAB : B < A) (hB : d + 1 ≤ B)
    (C : Poly2 F) (hprim : IsPrimY C) (hC : 1 ≤ C.natDeg)
    (equation : E → Poly2 F) (hdegree : ∀ z ∈ D, tdeg (equation z) ≤ M)
    (hrefined : ∀ z ∈ D, (∃ Q, equation z = mul C Q) ∨ CoprimeZ C (equation z))
    (pts : List (F × F)) (hnd : pts.Nodup)
    (α β : (F × F) → E) (P : (F × F) → UPoly E)
    (hinj : ∀ p ∈ pts, ∀ q ∈ pts, (α p, β p, P p) = (α q, β q, P q) → p = q)
    (hcurve : ∀ p ∈ pts, C.eval2 p.1 p.2 = zero)
    (hdeg : ∀ p ∈ pts, (P p).natDeg ≤ d)
    (haccept : ∀ p ∈ pts, A ≤ (D.filter (foldAgreePt x (α p) (β p) (P p))).length)
    (hnonpers : ∀ p ∈ pts, ¬ IsPersistent x D d B (α p) (β p) (P p))
    (hmatch : ∀ p ∈ pts, ∀ z ∈ D,
      decide ((equation z).eval2 p.1 p.2 = zero) = foldAgreePt x (α p) (β p) (P p) z) :
    pts.length ≤ Nat.max 1 ((D.length * (tdeg C * M * C.natDeg)) / (A - B)) := by
  apply curve_incidence_card_le C hprim hC D hD equation M A B hAB hdegree hrefined
    pts hnd hcurve
  · intro p hp
    have he : D.filter (fun z => decide ((equation z).eval2 p.1 p.2 = zero)) =
        D.filter (foldAgreePt x (α p) (β p) (P p)) :=
      List.filter_congr (hmatch p hp)
    rw [he]; exact haccept p hp
  · intro p hp q hq hne
    apply nonpersistent_common_agree_le x D d B hB (α p) (β p) (P p) (hdeg p hp)
      (α q) (β q) (P q) (hdeg q hq) (fun he => hne (hinj p hp q hq he)) (hnonpers p hp)
      (D.filter (fun z => decide ((equation z).eval2 p.1 p.2 = zero) &&
        decide ((equation z).eval2 q.1 q.2 = zero))) (nodup_filter _ D hD)
      (fun _ hz => (List.mem_filter.mp hz).1)
    · intro z hz
      obtain ⟨hzD, hpair⟩ := List.mem_filter.mp hz
      rw [hmatch p hp z hzD] at hpair
      exact (Bool.and_eq_true_iff.mp hpair).1
    · intro z hz
      obtain ⟨hzD, hpair⟩ := List.mem_filter.mp hz
      rw [hmatch q hq z hzD] at hpair
      exact (Bool.and_eq_true_iff.mp hpair).2

private theorem root_of_prodList (Cs : List (Poly2 F)) (y z : F)
    (hzero : Poly2.eval2 (UPoly.prodList Cs) y z = zero) :
    ∃ C ∈ Cs, C.eval2 y z = zero := by
  induction Cs with
  | nil =>
    have hone : Poly2.eval2 (UPoly.prodList ([] : List (Poly2 F))) y z = one := by
      change (eval₂Hom (evalHom y) z).toFun one = one
      exact RingHom.map_one _
    rw [hone] at hzero
    exact False.elim (LawfulField.one_ne_zero hzero)
  | cons C Cs ih =>
    have he : Poly2.eval2 (UPoly.prodList (C :: Cs)) y z =
        mul (C.eval2 y z) (Poly2.eval2 (UPoly.prodList Cs) y z) :=
      (eval₂Hom (evalHom y) z).map_mul C (UPoly.prodList Cs)
    rw [he] at hzero
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hzero with hC | hCs
    · exact ⟨C, .head _, hC⟩
    · obtain ⟨Q, hQ, hroot⟩ := ih hCs
      exact ⟨Q, .tail _ hQ, hroot⟩

/-- Construct the coordinate-refined curve cover, preserving total degree, and prove
its nonpersistent incidence bounds. No refinement certificate is required from callers. -/
theorem nonpersistent_curve_cover {E : Type} [LawfulField E] [DecidableEq E]
    (x : (E → E) × (E → E)) (D : List E) (hD : D.Nodup) (d A B M : Nat)
    (hAB : B < A) (hB : d + 1 ≤ B)
    (C : Poly2 F) (hprim : IsPrimY C) (hC : 1 ≤ C.natDeg)
    (equation : E → Poly2 F) (hdegree : ∀ z ∈ D, tdeg (equation z) ≤ M)
    (pts : List (F × F)) (hnd : pts.Nodup)
    (α β : (F × F) → E) (P : (F × F) → UPoly E)
    (hinj : ∀ p ∈ pts, ∀ q ∈ pts, (α p, β p, P p) = (α q, β q, P q) → p = q)
    (hcurve : ∀ p ∈ pts, C.eval2 p.1 p.2 = zero)
    (hdeg : ∀ p ∈ pts, (P p).natDeg ≤ d)
    (haccept : ∀ p ∈ pts, A ≤ (D.filter (foldAgreePt x (α p) (β p) (P p))).length)
    (hnonpers : ∀ p ∈ pts, ¬ IsPersistent x D d B (α p) (β p) (P p))
    (hmatch : ∀ p ∈ pts, ∀ z ∈ D,
      decide ((equation z).eval2 p.1 p.2 = zero) = foldAgreePt x (α p) (β p) (P p) z) :
    ∃ Cs : List (Poly2 F), C = UPoly.prodList Cs ∧ (Cs.map tdeg).sum = tdeg C ∧
      (∀ p ∈ pts, ∃ Ci ∈ Cs, Ci.eval2 p.1 p.2 = zero) ∧
      ∀ Ci ∈ Cs, IsPrimY Ci ∧ 1 ≤ Ci.natDeg ∧
        (pts.filter (fun p => decide (Ci.eval2 p.1 p.2 = zero))).length ≤
          Nat.max 1 ((D.length * (tdeg Ci * M * Ci.natDeg)) / (A - B)) := by
  obtain ⟨Cs, hprod, hsum, hvalid, hrefined⟩ := splitAgainstList C (D.map equation) hprim hC
  refine ⟨Cs, hprod, hsum, ?_, ?_⟩
  · intro p hp
    apply root_of_prodList Cs p.1 p.2
    rw [← hprod]
    exact hcurve p hp
  · intro Ci hCi
    obtain ⟨hpri, hpos⟩ := hvalid Ci hCi
    refine ⟨hpri, hpos, ?_⟩
    apply nonpersistent_curve_card_le x D hD d A B M hAB hB Ci hpri hpos equation hdegree
      (fun z hz => hrefined Ci hCi (equation z) (List.mem_map.mpr ⟨z, hz, rfl⟩))
      (pts.filter (fun p => decide (Ci.eval2 p.1 p.2 = zero))) (nodup_filter _ pts hnd)
      α β P
      (fun p hp q hq => hinj p (List.mem_filter.mp hp).1 q (List.mem_filter.mp hq).1)
      (fun _ hp => of_decide_eq_true (List.mem_filter.mp hp).2)
      (fun p hp => hdeg p (List.mem_filter.mp hp).1)
      (fun p hp => haccept p (List.mem_filter.mp hp).1)
      (fun p hp => hnonpers p (List.mem_filter.mp hp).1)
      (fun p hp => hmatch p (List.mem_filter.mp hp).1)

#verify_constructive incidence_mul_le curve_incidence_card_le nonpersistent_curve_card_le nonpersistent_curve_cover
namespace Tests
private def coordEquation (z : Goldilocks) : Poly2 Goldilocks := C (ofList [neg z, one])
private def twoPts : List (Goldilocks × Goldilocks) := [(zero, zero), (one, zero)]
private def twoCoords : List Goldilocks := [zero, one]
private theorem primitive_X : IsPrimY (X : Poly2 Goldilocks) :=
  BivariateGaussTests.isPrimY_monic_deg1 zero

/-- A sharp two-point instance of the curve count: `Z=0` meets `Y=0` and `Y=1`,
with one incident coordinate per point and no shared incident coordinate. -/
theorem inhabited_curve_incidence :
    ∃ (C : Poly2 Goldilocks) (D : List Goldilocks) (equation : Goldilocks → Poly2 Goldilocks)
      (pts : List (Goldilocks × Goldilocks)) (M A B : Nat),
      IsPrimY C ∧ 1 ≤ C.natDeg ∧ D.Nodup ∧ B < A ∧
      (∀ z ∈ D, tdeg (equation z) ≤ M) ∧
      (∀ z ∈ D, (∃ Q, equation z = mul C Q) ∨ CoprimeZ C (equation z)) ∧
      pts.Nodup ∧ (∀ p ∈ pts, C.eval2 p.1 p.2 = zero) ∧
      (∀ p ∈ pts, A ≤ (D.filter (fun z => decide ((equation z).eval2 p.1 p.2 = zero))).length) ∧
      (∀ p ∈ pts, ∀ q ∈ pts, p ≠ q →
        (D.filter (fun z => decide ((equation z).eval2 p.1 p.2 = zero) &&
          decide ((equation z).eval2 q.1 q.2 = zero))).length ≤ B) ∧
      pts.length = 2 ∧ pts.length = Nat.max 1 ((D.length * (tdeg C * M * C.natDeg)) / (A-B)) := by
  refine ⟨X, twoCoords, coordEquation, twoPts, 1, 1, 0, primitive_X,
    by decide +kernel, by decide +kernel, by decide, by decide +kernel, ?_,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    rfl, by decide +kernel⟩
  intro z hz
  right
  refine ⟨zero, one, ofList [neg z, one], ?_, ?_⟩
  · have hz' : z = zero ∨ z = one := by
      simpa only [twoCoords, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using hz
    rcases hz' with rfl | rfl <;> decide +kernel
  · rw [LawfulCommRing.zero_mul, LawfulCommRing.one_mul, LawfulCommRing.zero_add]
    rfl

/-- At `A=B`, every coordinate may contain the whole curve. The nonzero denominator
hypothesis cannot be removed, even with a primitive curve and a valid refinement. -/
theorem tooth_curve_incidence_needs_gap :
    ∃ (C : Poly2 Goldilocks) (D : List Goldilocks) (equation : Goldilocks → Poly2 Goldilocks)
      (pts : List (Goldilocks × Goldilocks)) (M A B : Nat),
      IsPrimY C ∧ 1 ≤ C.natDeg ∧ D.Nodup ∧
      (∀ z ∈ D, tdeg (equation z) ≤ M) ∧
      (∀ z ∈ D, (∃ Q, equation z = mul C Q) ∨ CoprimeZ C (equation z)) ∧
      pts.Nodup ∧ (∀ p ∈ pts, C.eval2 p.1 p.2 = zero) ∧
      (∀ p ∈ pts, A ≤ (D.filter (fun z => decide ((equation z).eval2 p.1 p.2 = zero))).length) ∧
      (∀ p ∈ pts, ∀ q ∈ pts, p ≠ q →
        (D.filter (fun z => decide ((equation z).eval2 p.1 p.2 = zero) &&
          decide ((equation z).eval2 q.1 q.2 = zero))).length ≤ B) ∧
      ¬ pts.length ≤ Nat.max 1 ((D.length * (tdeg C * M * C.natDeg)) / (A-B)) := by
  refine ⟨X, [zero], (fun _ => zero), twoPts, 0, 1, 1, primitive_X,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (fun _ _ => .inl ⟨zero, (LawfulCommRing.mul_zero _).symm⟩),
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

private def mixedWords : (Goldilocks → Goldilocks) × (Goldilocks → Goldilocks) :=
  (fun _ => zero, fun z => if z = zero ∨ z = one then zero else one)
private def fourCoords : List Goldilocks :=
  [zero, one, Goldilocks.ofNat 2, Goldilocks.ofNat 3]

/-- An actually accepted nonpersistent candidate: the zero challenge and zero polynomial
agree everywhere, but a constant numerator cannot explain three coordinates when `g` is
zero on two positions and one on two positions. -/
theorem inhabited_nonpersistent_candidate :
    ∃ (x : (Goldilocks → Goldilocks) × (Goldilocks → Goldilocks)) (D : List Goldilocks)
      (d A B : Nat) (α β : Goldilocks) (P : UPoly Goldilocks),
      D.Nodup ∧ d + 1 ≤ B ∧ B < A ∧ P.natDeg ≤ d ∧
      A ≤ (D.filter (foldAgreePt x α β P)).length ∧ ¬ IsPersistent x D d B α β P := by
  refine ⟨mixedWords, fourCoords, 0, 4, 3, zero, zero, zero,
    by decide +kernel, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  rintro ⟨H, L, _, _, hdeg, hsize⟩
  let c := coeffAt H.coeffs 0
  have hH : H = C c := by
    apply ext_coeffAt
    intro k
    cases k with
    | zero => rw [coeffAt_C_zero]
    | succ k => rw [coeffAt_C_succ, H.coeffAt_eq_zero_of_natDeg_lt (by omega)]
  have heval : ∀ z, H.eval z = c := fun z => by rw [hH, eval_C]
  let good := fourCoords.filter (fun z => decide (L.eval z ≠ zero) &&
    foldAgreePt mixedWords zero zero zero z && decide (H.eval z = mul (mixedWords.2 z) (L.eval z)))
  have hnd : good.Nodup := nodup_filter _ fourCoords (by decide +kernel)
  have hbound : good.length ≤ 2 := by
    if hc : c = zero then
      have hsub : ∀ z ∈ good, z ∈ fourCoords.filter (fun z => decide (mixedWords.2 z = zero)) := by
        intro z hz
        obtain ⟨hzD, hgood⟩ := List.mem_filter.mp hz
        obtain ⟨hleft, hHL⟩ := Bool.and_eq_true_iff.mp hgood
        obtain ⟨hL, _⟩ := Bool.and_eq_true_iff.mp hleft
        have hmul := (of_decide_eq_true hHL).symm
        rw [heval z, hc] at hmul
        have hg := (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hmul).resolve_right
          (of_decide_eq_true hL)
        exact List.mem_filter.mpr ⟨hzD, decide_eq_true hg⟩
      have hb := nodup_length_le_of_subset hnd hsub
      have hn : (fourCoords.filter (fun z => decide (mixedWords.2 z = zero))).length = 2 :=
        by decide +kernel
      omega
    else
      have hsub : ∀ z ∈ good, z ∈ fourCoords.filter (fun z => decide (mixedWords.2 z ≠ zero)) := by
        intro z hz
        obtain ⟨hzD, hgood⟩ := List.mem_filter.mp hz
        have hHL := of_decide_eq_true (Bool.and_eq_true_iff.mp hgood).2
        have hg : mixedWords.2 z ≠ zero := fun hg => hc (by
          rw [heval z, hg, LawfulCommRing.zero_mul] at hHL
          exact hHL)
        exact List.mem_filter.mpr ⟨hzD, decide_eq_true hg⟩
      have hb := nodup_length_le_of_subset hnd hsub
      have hn : (fourCoords.filter (fun z => decide (mixedWords.2 z ≠ zero))).length = 2 :=
        by decide +kernel
      omega
  change 3 ≤ good.length at hsize
  omega

#verify_constructive inhabited_nonpersistent_candidate
#verify_constructive inhabited_curve_incidence tooth_curve_incidence_needs_gap
#verify_inhabited curve_incidence_card_le inhabited_curve_incidence
#tooth_pair curve_incidence_card_le vs tooth_curve_incidence_needs_gap
end Tests
end NonpersistentIncidence
end Qsag
end
