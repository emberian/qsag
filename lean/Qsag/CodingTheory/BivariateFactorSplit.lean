module
/-
# Qsag.CodingTheory.BivariateFactorSplit — `Y`-Primitive D5 Splitting & Variable Swap

Constructive bivariate polynomial factor splitting over any field `E`
(`[LawfulField E] [DecidableEq E]`, `0 Classical.choice`, `0` irreducible factorization):
* `Poly2.liftFY`, `Poly2.clear_uPoly_ratFunc`, `Poly2.primY_dvd_of_dvd_FY`: Gauss divisibility
  descent from `E(Y)[Z]` to `E[Y][Z]`.
* `Poly2.d5_split_prim` & `Poly2.splitAgainstList`: dynamic Euclidean splitting lifted to
  `Y`-primitive factors in `Poly2 E` preserving total-degree sum `∑ tdeg Pᵢ = tdeg P`.
* `Poly2.swapVZ`, `Poly2.vCoeff`, `Poly2.coprimeZ_const_of_vCoeff`: variable swap `(V, Z) ↔ (Z, V)`
  and `CoprimeZ` certificate for `Z`-only polynomials from a single `V`-coefficient.
-/

public import Qsag.CodingTheory.BivariateGauss
import all Qsag.CodingTheory.PolyMv3
import all Qsag.CodingTheory.SylvesterResultant
import all Qsag.CodingTheory.DynamicGcdSplit
import all Qsag.CodingTheory.BivariateGauss
import all Qsag.AffineProximityGaps
import all Qsag.Goldilocks

public section
namespace Qsag

set_option autoImplicit false

open CommRingOps RoundPoly

namespace Poly2
section Field
variable {E : Type} [LawfulField E] [DecidableEq E]
open UPoly

local instance : NoZeroDivisors E := LawfulField.toNoZeroDivisors E

private theorem uPoly_natDeg_C {R : Type} [LawfulCommRing R] [DecidableEq R] (c : R) :
    (C c : UPoly R).natDeg = 0 :=
  Nat.le_zero.mp (natDeg_le_of_coeffAt _ 0 (fun k hk => by
    cases k with
    | zero => omega
    | succ k => exact coeffAt_C_succ c k))

/-! ## Clearing `E(Y)`-denominators and `Y`-primitive D5 splitting -/

abbrev liftFY : RingHom (Poly2 E) (UPoly (RatFunc E)) := UPoly.mapHom (Frac.of (D := UPoly E))

private theorem of_inj_uPoly (x : UPoly E) (h : (Frac.of (D := UPoly E)).toFun x = zero) :
    x = zero :=
  Frac.of_injective (h.trans (Frac.of (D := UPoly E)).map_zero.symm)

theorem liftFY_inj (P : Poly2 E) (h : liftFY.toFun P = zero) : P = zero :=
  UPoly.mapHom_inj _ of_inj_uPoly P h

private theorem clear_frac_list :
    ∀ cs : List (RatFunc E),
      ∃ (d : UPoly E) (ns : List (UPoly E)),
        d ≠ zero ∧ ns.length = cs.length ∧
        ∀ k, mul ((Frac.of (D := UPoly E)).toFun d) (coeffAt cs k) =
          (Frac.of (D := UPoly E)).toFun (coeffAt ns k)
  | [] =>
    ⟨one, [], NontrivialRing.one_ne_zero, rfl, fun k => by
      rw [coeffAt_nil, coeffAt_nil, RingHom.map_zero, LawfulCommRing.mul_zero]⟩
  | c :: tl => by
    obtain ⟨dTl, nsTl, hdTl, hlenTl, hspecTl⟩ := clear_frac_list tl
    have hcEx : ∃ (n0 d0 : UPoly E), d0 ≠ zero ∧
        mul ((Frac.of (D := UPoly E)).toFun d0) c = (Frac.of (D := UPoly E)).toFun n0 := by
      induction c using Frac.ind₁ with | h a =>
      refine ⟨a.num, a.den, a.den_ne, Frac.sound ?_⟩
      show mul (mul a.den a.num) one = mul a.num (mul one a.den)
      constructive_ring
    obtain ⟨n0, d0, hd0, hc0⟩ := hcEx
    refine ⟨mul d0 dTl, mul n0 dTl :: nsTl.map (mul d0), mul_ne_zero' hd0 hdTl,
      by simp [hlenTl], fun k => ?_⟩
    cases k with
    | zero =>
      change mul ((Frac.of (D := UPoly E)).toFun (mul d0 dTl)) c =
        (Frac.of (D := UPoly E)).toFun (mul n0 dTl)
      rw [RingHom.map_mul, RingHom.map_mul]
      have : mul (mul ((Frac.of (D := UPoly E)).toFun d0)
          ((Frac.of (D := UPoly E)).toFun dTl)) c =
          mul (mul ((Frac.of (D := UPoly E)).toFun d0) c)
            ((Frac.of (D := UPoly E)).toFun dTl) := by constructive_ring
      rw [this, hc0]
    | succ k =>
      show mul _ (coeffAt tl k) = (Frac.of (D := UPoly E)).toFun (coeffAt (nsTl.map (mul d0)) k)
      rw [coeffAt_map_mul_left, RingHom.map_mul, RingHom.map_mul, LawfulCommRing.mul_assoc,
        hspecTl k]

theorem clear_uPoly_ratFunc (f : UPoly (RatFunc E)) :
    ∃ (d : UPoly E) (P : Poly2 E), d ≠ zero ∧
      mul (C ((Frac.of (D := UPoly E)).toFun d)) f = liftFY.toFun P := by
  obtain ⟨d, ns, hd, _, hspec⟩ := clear_frac_list f.coeffs
  refine ⟨d, ofList ns, hd, ext_coeffAt fun k => ?_⟩
  rw [coeffAt_C_mul, coeffAt_mapHom, coeffAt_ofList]
  exact hspec k

/-- Two `Y`-primitive polynomials differing by an `E[Y]` scalar factor differ by `e ∈ E \ {0}`. -/
private theorem primY_assoc_of_scalar_eq {A B : Poly2 E} (hA : IsPrimY A) (hB : IsPrimY B)
    {c d : UPoly E} (hc : c ≠ zero) (hd : d ≠ zero)
    (hEq : mul (C c) A = mul (C d) B) :
    ∃ e : E, e ≠ zero ∧ A = mul (C (C e)) B ∧ mul c (C e) = d := by
  obtain ⟨hbez, ⟨c', hc'⟩, ⟨d', hd'⟩⟩ := xgcd_spec c d
  generalize (UPoly.xgcd c d).1 = g at hbez hc' hd'
  generalize (UPoly.xgcd c d).2.1 = u0 at hbez
  generalize (UPoly.xgcd c d).2.2 = v0 at hbez
  have hgNe : g ≠ zero := fun e => hc (by rw [hc', e, LawfulCommRing.zero_mul])
  have hc'Ne : c' ≠ zero := fun e => hc (by rw [hc', e, LawfulCommRing.mul_zero])
  have hd'Ne : d' ≠ zero := fun e => hd (by rw [hd', e, LawfulCommRing.mul_zero])
  have huv1 : add (mul u0 c') (mul v0 d') = one := by
    apply mul_right_cancel' hgNe
    rw [LawfulCommRing.one_mul]
    have : mul (add (mul u0 c') (mul v0 d')) g = add (mul u0 (mul g c')) (mul v0 (mul g d')) := by
      constructive_ring
    rw [this, ← hc', ← hd', hbez]
  have hEq' : mul (C c') A = mul (C d') B := by
    apply mul_right_cancel' (Poly2.C_ne_zero hgNe)
    have hL : mul (mul (C c') A) (C g) = mul (C c) A := by
      rw [hc', ← C_mul_eq]; constructive_ring
    have hR : mul (mul (C d') B) (C g) = mul (C d) B := by
      rw [hd', ← C_mul_eq]; constructive_ring
    rw [hL, hR, hEq]
  have hc'Deg0 : c'.natDeg = 0 := hB.2 c' (fun k => by
    refine ⟨add (mul u0 (coeffAt B.coeffs k)) (mul v0 (coeffAt A.coeffs k)), ?_⟩
    have hk := congrArg (fun P : Poly2 E => coeffAt P.coeffs k) hEq'
    rw [coeffAt_C_mul, coeffAt_C_mul] at hk
    have h1 : coeffAt B.coeffs k = mul (add (mul u0 c') (mul v0 d')) (coeffAt B.coeffs k) := by
      rw [huv1, LawfulCommRing.one_mul]
    conv => lhs; rw [h1]
    have h2 : mul (add (mul u0 c') (mul v0 d')) (coeffAt B.coeffs k) =
        add (mul (mul c' u0) (coeffAt B.coeffs k)) (mul v0 (mul d' (coeffAt B.coeffs k))) := by
      constructive_ring
    rw [h2, ← hk]; constructive_ring)
  have hd'Deg0 : d'.natDeg = 0 := hA.2 d' (fun k => by
    refine ⟨add (mul u0 (coeffAt B.coeffs k)) (mul v0 (coeffAt A.coeffs k)), ?_⟩
    have hk := congrArg (fun P : Poly2 E => coeffAt P.coeffs k) hEq'
    rw [coeffAt_C_mul, coeffAt_C_mul] at hk
    have h1 : coeffAt A.coeffs k = mul (add (mul u0 c') (mul v0 d')) (coeffAt A.coeffs k) := by
      rw [huv1, LawfulCommRing.one_mul]
    conv => lhs; rw [h1]
    have h2 : mul (add (mul u0 c') (mul v0 d')) (coeffAt A.coeffs k) =
        add (mul u0 (mul c' (coeffAt A.coeffs k))) (mul (mul d' v0) (coeffAt A.coeffs k)) := by
      constructive_ring
    rw [h2, hk]; constructive_ring)
  let e1 := c'.lead
  let e2 := d'.lead
  have he1 : e1 ≠ zero := lead_ne_zero hc'Ne
  have he2 : e2 ≠ zero := lead_ne_zero hd'Ne
  let e := mul e2 (LawfulField.inv e1)
  have heNe : e ≠ zero := mul_ne_zero' he2 (fun h0 =>
    LawfulField.one_ne_zero (by have := LawfulField.mul_inv_cancel he1; rw [h0, LawfulCommRing.mul_zero] at this; exact this.symm))
  have hc'd' : mul c' (C e) = d' := by
    conv => lhs; rw [eq_C_lead_of_natDeg_zero hc'Deg0]
    conv => rhs; rw [eq_C_lead_of_natDeg_zero hd'Deg0]
    rw [C_mul_eq]
    congr 1
    dsimp [e, e1, e2]
    rw [LawfulCommRing.mul_comm c'.lead, LawfulCommRing.mul_assoc,
      LawfulCommRing.mul_comm (LawfulField.inv c'.lead), LawfulField.mul_inv_cancel he1,
      LawfulCommRing.mul_one]
  refine ⟨e, heNe, ?_, by rw [hc', hd', LawfulCommRing.mul_assoc, hc'd']⟩
  apply mul_right_cancel' (Poly2.C_ne_zero hc'Ne)
  have hL : mul A (C c') = mul (C c') A := LawfulCommRing.mul_comm _ _
  have hR : mul (mul (C (C e)) B) (C c') = mul (C (mul c' (C e))) B := by
    rw [← C_mul_eq c' (C e)]; constructive_ring
  rw [hL, hR, hc'd', hEq']

/-- **Gauss divisibility descent (`primY_dvd_of_dvd_FY`)**: if `P` is `Y`-primitive and divides
    `G` in `E(Y)[Z]`, then `P` divides `G` in `E[Y][Z]`. -/
theorem primY_dvd_of_dvd_FY {P G : Poly2 E} (hP : IsPrimY P)
    (hDvd : ∃ t : UPoly (RatFunc E), liftFY.toFun G = mul (liftFY.toFun P) t) :
    ∃ Q : Poly2 E, G = mul P Q := by
  if hG : G = zero then
    exact ⟨zero, by rw [hG, LawfulCommRing.mul_zero]⟩
  else
    obtain ⟨t, ht⟩ := hDvd
    obtain ⟨d, T0, hd, hT0⟩ := clear_uPoly_ratFunc t
    have hEqFY : liftFY.toFun (mul (C d) G) = liftFY.toFun (mul P T0) := by
      rw [RingHom.map_mul, RingHom.map_mul, mapHom_C, ht]
      have : mul (C ((Frac.of (D := UPoly E)).toFun d)) (mul (liftFY.toFun P) t) =
          mul (liftFY.toFun P) (mul (C ((Frac.of (D := UPoly E)).toFun d)) t) := by constructive_ring
      rw [this, hT0]
    have hEqP : mul (C d) G = mul P T0 :=
      LawfulCommRing.sub_eq_zero_iff.mp (liftFY_inj _ (by rw [RingHom.map_sub, hEqFY, LawfulCommRing.sub_self]))
    have hT0Ne : T0 ≠ zero := fun e => by
      rw [e, LawfulCommRing.mul_zero] at hEqP
      exact mul_ne_zero' (Poly2.C_ne_zero hd) hG hEqP
    obtain ⟨hcG, hGp, hGdecomp, _, _⟩ := contY_mul_primY hG
    obtain ⟨hcT, hTp, hTdecomp, _, _⟩ := contY_mul_primY hT0Ne
    have hScalar : mul (C (mul d (contY G))) (primY G) =
        mul (C (contY T0)) (mul P (primY T0)) := by
      have h1 : mul (C (mul d (contY G))) (primY G) = mul (C d) (mul (C (contY G)) (primY G)) := by
        rw [← C_mul_eq d (contY G), LawfulCommRing.mul_assoc]
      have h2 : mul P (mul (C (contY T0)) (primY T0)) = mul (C (contY T0)) (mul P (primY T0)) := by
        constructive_ring
      rw [h1, ← hGdecomp, hEqP]
      conv => lhs; rw [hTdecomp]
      exact h2
    obtain ⟨e, _, heEq, _⟩ := primY_assoc_of_scalar_eq hGp (isPrimY_mul hP hTp)
      (mul_ne_zero' hd hcG) hcT hScalar
    refine ⟨mul (C (contY G)) (mul (C (C e)) (primY T0)), ?_⟩
    conv => lhs; rw [hGdecomp]
    rw [heEq]; constructive_ring

/-- **Primitive D5 splitting step (`d5_split_prim`)**: testing `G : Poly2 E` against a `Y`-primitive
    modulus `P : Poly2 E` either finds `Q` with `G = mul P Q`, certifies `CoprimeZ P G`, or splits
    `P = mul P₁ P₂` into two `Y`-primitive positive-`Z`-degree factors with `G = mul P₁ Q`. -/
theorem d5_split_prim (P G : Poly2 E) (hP : IsPrimY P) :
    (∃ Q : Poly2 E, G = mul P Q) ∨ CoprimeZ P G ∨
      ∃ P₁ P₂ : Poly2 E, IsPrimY P₁ ∧ IsPrimY P₂ ∧ 1 ≤ P₁.natDeg ∧ 1 ≤ P₂.natDeg ∧
        P = mul P₁ P₂ ∧ tdeg P₁ + tdeg P₂ = tdeg P ∧ (∃ Q : Poly2 E, G = mul P₁ Q) := by
  have hPFY : liftFY.toFun P ≠ zero := fun e => hP.1 (liftFY_inj P e)
  rcases UPoly.d5_split (liftFY.toFun P) (liftFY.toFun G) hPFY with
    ⟨u, v, hbez⟩ | ⟨t, ht⟩ | ⟨g, q, hsplit, hgPos, hqPos, _, t, ht⟩
  · obtain ⟨du, U0, hdu, hU0⟩ := clear_uPoly_ratFunc u
    obtain ⟨dv, V0, hdv, hV0⟩ := clear_uPoly_ratFunc v
    refine .inr (.inl ⟨mul (C dv) U0, mul (C du) V0, mul du dv, mul_ne_zero' hdu hdv, ?_⟩)
    apply LawfulCommRing.sub_eq_zero_iff.mp
    apply liftFY_inj _
    rw [RingHom.map_sub, RingHom.map_add, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul,
      RingHom.map_mul, mapHom_C, mapHom_C, mapHom_C, RingHom.map_mul, ← hU0, ← hV0]
    have hId : sub (add (mul (mul (C ((Frac.of (D := UPoly E)).toFun dv))
          (mul (C ((Frac.of (D := UPoly E)).toFun du)) u)) (liftFY.toFun P))
        (mul (mul (C ((Frac.of (D := UPoly E)).toFun du))
          (mul (C ((Frac.of (D := UPoly E)).toFun dv)) v)) (liftFY.toFun G)))
        (C (mul ((Frac.of (D := UPoly E)).toFun du) ((Frac.of (D := UPoly E)).toFun dv))) =
      sub (mul (mul (C ((Frac.of (D := UPoly E)).toFun du))
          (C ((Frac.of (D := UPoly E)).toFun dv)))
          (add (mul u (liftFY.toFun P)) (mul v (liftFY.toFun G))))
        (C (mul ((Frac.of (D := UPoly E)).toFun du) ((Frac.of (D := UPoly E)).toFun dv))) := by
      constructive_ring
    rw [hId, hbez, LawfulCommRing.mul_one, C_mul_eq, LawfulCommRing.sub_self]
  · exact .inl (primY_dvd_of_dvd_FY hP ⟨t, ht⟩)
  · obtain ⟨dg, G0, hdg, hG0⟩ := clear_uPoly_ratFunc g
    obtain ⟨dq, Q0, hdq, hQ0⟩ := clear_uPoly_ratFunc q
    have hCdg : (C ((Frac.of (D := UPoly E)).toFun dg) : UPoly (RatFunc E)) ≠ zero := fun e => by
      have := congrArg (fun X : UPoly (RatFunc E) => coeffAt X.coeffs 0) e
      simp only [coeffAt_C_zero, coeffs_zero, coeffAt_nil] at this
      exact hdg (of_inj_uPoly dg this)
    have hCdq : (C ((Frac.of (D := UPoly E)).toFun dq) : UPoly (RatFunc E)) ≠ zero := fun e => by
      have := congrArg (fun X : UPoly (RatFunc E) => coeffAt X.coeffs 0) e
      simp only [coeffAt_C_zero, coeffs_zero, coeffAt_nil] at this
      exact hdq (of_inj_uPoly dq this)
    have hG0Ne : G0 ≠ zero := fun e => by
      rw [e, RingHom.map_zero] at hG0
      have hg0 : g = zero := mul_right_cancel' hCdg (by
        rw [LawfulCommRing.zero_mul, LawfulCommRing.mul_comm]; exact hG0)
      rw [hg0] at hgPos; exact Nat.not_succ_le_zero 0 hgPos
    have hQ0Ne : Q0 ≠ zero := fun e => by
      rw [e, RingHom.map_zero] at hQ0
      have hq0 : q = zero := mul_right_cancel' hCdq (by
        rw [LawfulCommRing.zero_mul, LawfulCommRing.mul_comm]; exact hQ0)
      rw [hq0] at hqPos; exact Nat.not_succ_le_zero 0 hqPos
    obtain ⟨hcG0, hG0p, hG0d, hG0deg, _⟩ := contY_mul_primY hG0Ne
    obtain ⟨hcQ0, hQ0p, hQ0d, hQ0deg, _⟩ := contY_mul_primY hQ0Ne
    have hEqFY : liftFY.toFun (mul (C (mul dg dq)) P) = liftFY.toFun (mul G0 Q0) := by
      rw [RingHom.map_mul, RingHom.map_mul, mapHom_C, RingHom.map_mul, hsplit, ← hG0, ← hQ0,
        ← C_mul_eq]
      constructive_ring
    have hEqP : mul (C (mul dg dq)) P = mul G0 Q0 :=
      LawfulCommRing.sub_eq_zero_iff.mp (liftFY_inj _ (by rw [RingHom.map_sub, hEqFY, LawfulCommRing.sub_self]))
    have hScalar : mul (C (mul dg dq)) P =
        mul (C (mul (contY G0) (contY Q0))) (mul (primY G0) (primY Q0)) := by
      rw [hEqP]
      conv => lhs; rw [hG0d]; rw [hQ0d]
      rw [← C_mul_eq (contY G0) (contY Q0)]; constructive_ring
    obtain ⟨e, heNe, heEq, _⟩ := primY_assoc_of_scalar_eq hP (isPrimY_mul hG0p hQ0p)
      (mul_ne_zero' hdg hdq) (mul_ne_zero' hcG0 hcQ0) hScalar
    let P₁ := mul (C (C e)) (primY G0)
    let P₂ := primY Q0
    have hCeNe : (C e : UPoly E) ≠ zero := fun e0 => heNe (by
      have := congrArg (fun X : UPoly E => coeffAt X.coeffs 0) e0
      simpa only [coeffAt_C_zero, coeffs_zero, coeffAt_nil] using this)
    have hP₁Ne : P₁ ≠ zero := mul_ne_zero' (Poly2.C_ne_zero hCeNe) hG0p.1
    have hP₁Prim : IsPrimY P₁ := ⟨hP₁Ne, fun f hf => hG0p.2 f (fun k => by
      obtain ⟨qf, hqf⟩ := hf k
      dsimp [P₁] at hqf
      rw [coeffAt_C_mul] at hqf
      refine ⟨mul (C (LawfulField.inv e)) qf, ?_⟩
      have h1 : mul (C (LawfulField.inv e)) (mul (C e) (coeffAt (primY G0).coeffs k)) =
          mul (C (LawfulField.inv e)) (mul f qf) := congrArg (mul (C (LawfulField.inv e))) hqf
      rw [← LawfulCommRing.mul_assoc, C_mul_eq, LawfulCommRing.mul_comm (LawfulField.inv e) e,
        LawfulField.mul_inv_cancel heNe, ← one_eq_C, LawfulCommRing.one_mul] at h1
      rw [h1]; constructive_ring)⟩
    have hP₁deg : 1 ≤ P₁.natDeg := by
      have hd1 := UPoly.natDeg_mul (Poly2.C_ne_zero hCeNe) hG0p.1
      change P₁.natDeg = _ at hd1
      rw [Poly2.natDeg_C, Nat.zero_add, hG0deg] at hd1
      have hd2 := UPoly.natDeg_mapHom (Frac.of (D := UPoly E)) of_inj_uPoly G0
      change (liftFY.toFun G0).natDeg = G0.natDeg at hd2
      rw [← hG0, UPoly.natDeg_mul hCdg
        (fun e0 => by rw [e0] at hgPos; exact Nat.not_succ_le_zero 0 hgPos),
        uPoly_natDeg_C, Nat.zero_add] at hd2
      omega
    have hP₂deg : 1 ≤ P₂.natDeg := by
      dsimp [P₂]; rw [hQ0deg]
      have hd2 := UPoly.natDeg_mapHom (Frac.of (D := UPoly E)) of_inj_uPoly Q0
      change (liftFY.toFun Q0).natDeg = Q0.natDeg at hd2
      rw [← hQ0, UPoly.natDeg_mul hCdq
        (fun e0 => by rw [e0] at hqPos; exact Nat.not_succ_le_zero 0 hqPos),
        uPoly_natDeg_C, Nat.zero_add] at hd2
      omega
    have hPMul : P = mul P₁ P₂ := by
      rw [heEq]; dsimp [P₁, P₂]; exact (LawfulCommRing.mul_assoc _ _ _).symm
    have hP₁DvdG : ∃ Q : Poly2 E, G = mul P₁ Q := by
      apply primY_dvd_of_dvd_FY hP₁Prim
      let sd : RatFunc E := (Frac.of (D := UPoly E)).toFun dg
      let s0 : RatFunc E := (Frac.of (D := UPoly E)).toFun (contY G0)
      let se : RatFunc E := (Frac.of (D := UPoly E)).toFun (C e)
      have hsdNe : sd ≠ zero := fun h0 => hdg (of_inj_uPoly dg h0)
      have hseNe : se ≠ zero := fun h0 => hCeNe (of_inj_uPoly (C e) h0)
      refine ⟨mul (C (mul (LawfulField.inv sd) (mul s0 (LawfulField.inv se)))) t, ?_⟩
      have hP₁FY : liftFY.toFun P₁ = mul (C se) (liftFY.toFun (primY G0)) := by
        dsimp [P₁, se]; rw [RingHom.map_mul, mapHom_C]
      have hG0FY : mul (C sd) g = mul (C s0) (liftFY.toFun (primY G0)) := by
        change mul (C ((Frac.of (D := UPoly E)).toFun dg)) g = _
        rw [hG0]
        conv => lhs; rw [hG0d]
        rw [RingHom.map_mul, mapHom_C]
      have hgRel : g = mul (liftFY.toFun P₁) (C (mul (LawfulField.inv sd) (mul s0 (LawfulField.inv se)))) := by
        apply mul_right_cancel' hCdg
        have hL : mul g (C sd) = mul (C sd) g := LawfulCommRing.mul_comm _ _
        change mul g (C sd) = mul (mul (liftFY.toFun P₁) _) (C sd)
        rw [hL, hG0FY, hP₁FY]
        have hSc : mul se (mul (mul (LawfulField.inv sd) (mul s0 (LawfulField.inv se))) sd) = s0 := by
          have : mul se (mul (mul (LawfulField.inv sd) (mul s0 (LawfulField.inv se))) sd) =
              mul (mul se (LawfulField.inv se)) (mul (mul sd (LawfulField.inv sd)) s0) := by
            constructive_ring
          rw [this, LawfulField.mul_inv_cancel hseNe, LawfulField.mul_inv_cancel hsdNe,
            LawfulCommRing.one_mul, LawfulCommRing.one_mul]
        have hAssoc : mul (mul (mul (C se) (liftFY.toFun (primY G0)))
            (C (mul (LawfulField.inv sd) (mul s0 (LawfulField.inv se))))) (C sd) =
            mul (C (mul se (mul (mul (LawfulField.inv sd) (mul s0 (LawfulField.inv se))) sd)))
              (liftFY.toFun (primY G0)) := by
          rw [LawfulCommRing.mul_assoc,
            C_mul_eq (mul (LawfulField.inv sd) (mul s0 (LawfulField.inv se))) sd,
            ← C_mul_eq se]
          constructive_ring
        rw [hAssoc, hSc]
      rw [ht, hgRel, LawfulCommRing.mul_assoc]
    exact .inr (.inr ⟨P₁, P₂, hP₁Prim, hQ0p, hP₁deg, hP₂deg, hPMul,
      (tdeg_mul hP₁Ne hQ0p.1).symm.trans (congrArg tdeg hPMul.symm), hP₁DvdG⟩)

/-! ## Iterated factor refinement against a list of test polynomials -/

private theorem nat_sum_append : ∀ xs ys : List Nat, (xs ++ ys).sum = xs.sum + ys.sum
  | [], ys => by show ys.sum = 0 + ys.sum; rw [Nat.zero_add]
  | x :: tl, ys => by
    show x + (tl ++ ys).sum = (x + tl.sum) + ys.sum
    rw [nat_sum_append tl ys, Nat.add_assoc]

private theorem mem_append_or {α : Type} {x : α} :
    ∀ {xs ys : List α}, x ∈ xs ++ ys → x ∈ xs ∨ x ∈ ys
  | [], _, h => .inr h
  | _ :: _, _, .head _ => .inl (.head _)
  | _ :: tl, _, .tail _ h => (mem_append_or h).elim (fun hx => .inl (.tail _ hx)) .inr

private theorem dvd_prodList_of_mem {F : Poly2 E} :
    ∀ Fs : List (Poly2 E), F ∈ Fs → ∃ R, UPoly.prodList Fs = mul F R
  | [], hm => nomatch hm
  | _ :: Xtl, .head _ => ⟨UPoly.prodList Xtl, rfl⟩
  | X :: Xtl, .tail _ hmtl => by
    obtain ⟨R, hR⟩ := dvd_prodList_of_mem Xtl hmtl
    exact ⟨mul X R, by show mul X (UPoly.prodList Xtl) = _; rw [hR]; constructive_ring⟩

private theorem prodList_append :
    ∀ xs ys : List (Poly2 E),
      UPoly.prodList (xs ++ ys) = mul (UPoly.prodList xs) (UPoly.prodList ys)
  | [], ys => by show UPoly.prodList ys = mul one (UPoly.prodList ys); rw [LawfulCommRing.one_mul]
  | x :: xtl, ys => by
    show mul x (UPoly.prodList (xtl ++ ys)) = mul (mul x (UPoly.prodList xtl)) (UPoly.prodList ys)
    rw [prodList_append xtl ys, LawfulCommRing.mul_assoc]

private theorem split_single_against_list :
    ∀ (fuel : Nat) (Gs0 : List (Poly2 E)) (P : Poly2 E),
      P.natDeg ≤ fuel → IsPrimY P → 1 ≤ P.natDeg →
      ∃ Ps : List (Poly2 E),
        P = UPoly.prodList Ps ∧
        (Ps.map tdeg).sum = tdeg P ∧
        (∀ F ∈ Ps, IsPrimY F ∧ 1 ≤ F.natDeg) ∧
        (∀ F ∈ Ps, ∀ G ∈ Gs0, (∃ Q, G = mul F Q) ∨ CoprimeZ F G) := by
  intro fuel
  induction fuel with
  | zero =>
    intro _ P hFuel _ hDeg
    exact absurd (Nat.le_trans hDeg hFuel) (Nat.not_succ_le_zero 0)
  | succ fuel ihFuel =>
    intro Gs0 P hFuel hP hDeg
    induction Gs0 with
    | nil =>
      exact ⟨[P], (LawfulCommRing.mul_one P).symm, Nat.add_zero (tdeg P),
        (fun (F : Poly2 E) (hF : F ∈ [P]) => by
          have hEq : F = P := List.mem_singleton.mp hF
          rw [hEq]; exact ⟨hP, hDeg⟩),
        fun _ _ _ hG => False.elim (List.not_mem_nil hG)⟩
    | cons G tl ihTl =>
      rcases d5_split_prim P G hP with ⟨Q, hQ⟩ | hCop |
        ⟨P₁, P₂, hP₁, hP₂, hDeg₁, hDeg₂, hMul, hTdeg, _⟩
      · obtain ⟨Ps, hProd, hSum, hValid, hTl⟩ := ihTl
        refine ⟨Ps, hProd, hSum, hValid, fun F hF G' hG' => ?_⟩
        rcases List.mem_cons.mp hG' with hEq | hGtl
        · obtain ⟨R, hR⟩ := dvd_prodList_of_mem Ps hF
          exact .inl ⟨mul R Q, by rw [hEq, hQ, hProd, hR, LawfulCommRing.mul_assoc]⟩
        · exact hTl F hF G' hGtl
      · obtain ⟨Ps, hProd, hSum, hValid, hTl⟩ := ihTl
        refine ⟨Ps, hProd, hSum, hValid, fun F hF G' hG' => ?_⟩
        rcases List.mem_cons.mp hG' with hEq | hGtl
        · obtain ⟨u0, v0, c, hc, hbez⟩ := hCop
          obtain ⟨R, hR⟩ := dvd_prodList_of_mem Ps hF
          exact .inr ⟨mul u0 R, v0, c, hc, by rw [hEq, ← hbez, hProd, hR]; constructive_ring⟩
        · exact hTl F hF G' hGtl
      · have hDegSum : P.natDeg = P₁.natDeg + P₂.natDeg := by
          rw [hMul]; exact UPoly.natDeg_mul hP₁.1 hP₂.1
        have hLe₁ : P₁.natDeg ≤ fuel :=
          Nat.le_of_succ_le_succ
            (Nat.le_trans (Nat.add_le_add_left hDeg₂ P₁.natDeg) (hDegSum ▸ hFuel))
        have hLe₂ : P₂.natDeg ≤ fuel :=
          Nat.le_of_succ_le_succ
            (Nat.le_trans (Nat.add_comm 1 P₂.natDeg ▸ Nat.add_le_add_right hDeg₁ P₂.natDeg)
              (hDegSum ▸ hFuel))
        obtain ⟨Ps₁, hProd₁, hSum₁, hValid₁, hAll₁⟩ := ihFuel (G :: tl) P₁ hLe₁ hP₁ hDeg₁
        obtain ⟨Ps₂, hProd₂, hSum₂, hValid₂, hAll₂⟩ := ihFuel (G :: tl) P₂ hLe₂ hP₂ hDeg₂
        refine ⟨Ps₁ ++ Ps₂, by rw [hMul, hProd₁, hProd₂, ← prodList_append],
          by rw [List.map_append, nat_sum_append, hSum₁, hSum₂, hTdeg],
          fun F hF => (mem_append_or hF).elim (hValid₁ F) (hValid₂ F),
          fun F hF => (mem_append_or hF).elim (hAll₁ F) (hAll₂ F)⟩

/-- **Iterated `Y`-primitive factor refinement (`splitAgainstList`)**. -/
theorem splitAgainstList (P : Poly2 E) (Gs : List (Poly2 E)) (hP : IsPrimY P) (hDeg : 1 ≤ P.natDeg) :
    ∃ Ps : List (Poly2 E),
      P = UPoly.prodList Ps ∧
      (Ps.map tdeg).sum = tdeg P ∧
      (∀ F ∈ Ps, IsPrimY F ∧ 1 ≤ F.natDeg) ∧
      (∀ F ∈ Ps, ∀ G ∈ Gs, (∃ Q, G = mul F Q) ∨ CoprimeZ F G) :=
  split_single_against_list P.natDeg Gs P (Nat.le_refl _) hP hDeg

/-! ## Variable swap `(V, Z) ↔ (Z, V)` and coprimality from one `V`-coefficient -/

/-- Ring automorphism of `Poly2 E` swapping the inner and outer variables:
    `A(V, Z) ∈ (E[V])[Z] ↦ A(V_out, Z_in) ∈ (E[Z])[V]`. -/
def swapVZ : RingHom (Poly2 E) (Poly2 E) :=
  eval₂Hom innerHom (C X)

/-- The `V^k`-coefficient of `A(V, Z) ∈ (E[V])[Z]`, as a polynomial in `E[Z]`. -/
@[expose] def vCoeff (A : Poly2 E) (k : Nat) : UPoly E :=
  coeffAt (swapVZ.toFun A).coeffs k

theorem c2_swapVZ (A : Poly2 E) (j k : Nat) :
    coeffAt (vCoeff A k).coeffs j = coeffAt (coeffAt A.coeffs j).coeffs k := by
  unfold vCoeff swapVZ
  have h := fun qs : List (UPoly E) => show
      ∀ (j k : Nat),
        c2 (evalCoeffs (qs.map (innerHom (E := E)).toFun) (C X)) j k =
          coeffAt (coeffAt qs j).coeffs k from by
    induction qs with
    | nil =>
      intro j k
      show c2 (zero : Poly2 E) j k = _
      rw [c2_zero, coeffAt_nil, coeffs_zero, coeffAt_nil]
    | cons q tl ih =>
      intro j k
      show c2 (add (innerHom.toFun q) (mul (C X) (evalCoeffs _ (C X)))) j k = _
      have hq : c2 (innerHom.toFun q) j k = if j = 0 then coeffAt q.coeffs k else zero :=
        c2_innerHom_eval q.coeffs j k
      rw [c2_add, hq]
      cases j with
      | zero =>
        rw [c2_CX_mul_zero, LawfulCommRing.add_zero]
        rfl
      | succ j =>
        rw [c2_CX_mul_succ, ih j k]
        simp only [Nat.succ_ne_zero, ↓reduceIte, LawfulCommRing.zero_add, coeffAt_cons_succ]
  exact h A.coeffs j k

private theorem swapVZ_constZ (p : UPoly E) :
    swapVZ.toFun ((UPoly.mapHom CHom).toFun p) = C p := by
  have h : ∀ cs : List E,
      swapVZ.toFun (ofList (cs.map (CHom (R := E)).toFun)) = C (ofList cs) := by
    intro cs; induction cs with
    | nil =>
      show swapVZ.toFun zero = C zero
      rw [RingHom.map_zero, C_zero_eq]
    | cons c tl ih =>
      rw [List.map_cons, ofList_cons, ofList_cons, RingHom.map_add, RingHom.map_mul, ih]
      have hX : swapVZ.toFun (X : Poly2 E) = C X := eval₂_X innerHom (C X)
      have hC : swapVZ.toFun (C (C c) : Poly2 E) = C (C c) := by
        show eval₂ innerHom (C X) (C (C c)) = C (C c)
        rw [eval₂_C]
        exact eval₂_C (CHom.comp CHom) X c
      change add (swapVZ.toFun (C (C c))) (mul (swapVZ.toFun X) (C (ofList tl))) = _
      rw [hC, hX, C_mul_eq]
      exact (CHom.map_add (C c) (mul X (ofList tl))).symm
  rw [mapHom_apply, h, ofList_coeffs]

/-- If `p ∈ E[Z]` (`1 ≤ p.natDeg`) is coprime in `E[Z]` to at least one `V`-coefficient `vCoeff A k₀`
    of `A(V, Z) ∈ (E[V])[Z]`, then `mapHom CHom p` is `CoprimeZ` to `A` in `Poly2 E`. -/
theorem coprimeZ_const_of_vCoeff (p : UPoly E) (A : Poly2 E) (hpDeg : 1 ≤ p.natDeg)
    (k₀ : Nat) (u0 v0 : UPoly E) (hbez : add (mul u0 p) (mul v0 (vCoeff A k₀)) = one) :
    CoprimeZ ((UPoly.mapHom CHom).toFun p) A := by
  let P := (UPoly.mapHom (CHom (R := E))).toFun p
  have hpNe : p ≠ zero := fun e => by rw [e] at hpDeg; exact Nat.not_succ_le_zero 0 hpDeg
  have hCHomInj : ∀ x : E, (CHom (R := E)).toFun x = zero → x = zero := fun x hx => by
    have := congrArg (fun q : UPoly E => coeffAt q.coeffs 0) hx
    simpa only [CHom_apply, coeffAt_C_zero, coeffs_zero, coeffAt_nil] using this
  have hPNe : P ≠ zero := fun e => hpNe (UPoly.mapHom_inj CHom hCHomInj p e)
  have hPDeg : P.natDeg = p.natDeg := UPoly.natDeg_mapHom CHom hCHomInj p
  have hPPrim : IsPrimY P := ⟨hPNe, fun g hg => by
    obtain ⟨q, hq⟩ := hg p.natDeg
    dsimp [P] at hq
    rw [coeffAt_mapHom, CHom_apply] at hq
    let ld := coeffAt p.coeffs p.natDeg
    change C ld = mul g q at hq
    have hldNe : ld ≠ zero := lead_ne_zero hpNe
    have hClNe : (C ld : UPoly E) ≠ zero := fun e => hldNe (hCHomInj ld e)
    have hg0 : g ≠ zero := fun e => hClNe (by rw [hq, e, LawfulCommRing.zero_mul])
    have hq0 : q ≠ zero := fun e => hClNe (by rw [hq, e, LawfulCommRing.mul_zero])
    have hd := UPoly.natDeg_mul hg0 hq0
    rw [← hq, uPoly_natDeg_C] at hd; omega⟩
  have hNoCommonConstFactor : ∀ g1 : UPoly E, 1 ≤ g1.natDeg →
      (∃ q1, p = mul g1 q1) → (∃ Q : Poly2 E, A = mul ((UPoly.mapHom CHom).toFun g1) Q) → False := by
    rintro g1 hg1Deg ⟨q1, hq1⟩ ⟨Q, hQ⟩
    have hvk : vCoeff A k₀ = mul g1 (vCoeff Q k₀) := by
      unfold vCoeff
      rw [hQ, RingHom.map_mul, swapVZ_constZ, coeffAt_C_mul]
    have hUnit : mul g1 (add (mul u0 q1) (mul v0 (vCoeff Q k₀))) = one := by
      have : mul g1 (add (mul u0 q1) (mul v0 (vCoeff Q k₀))) =
          add (mul u0 (mul g1 q1)) (mul v0 (mul g1 (vCoeff Q k₀))) := by constructive_ring
      rw [this, ← hq1, ← hvk, hbez]
    have hg1Ne : g1 ≠ zero := fun e => NontrivialRing.one_ne_zero (by rw [← hUnit, e, LawfulCommRing.zero_mul])
    have hwNe : add (mul u0 q1) (mul v0 (vCoeff Q k₀)) ≠ zero := fun e =>
      NontrivialRing.one_ne_zero (by rw [← hUnit, e, LawfulCommRing.mul_zero])
    have hd := UPoly.natDeg_mul hg1Ne hwNe
    rw [hUnit, natDeg_one] at hd; omega
  rcases d5_split_prim P A hPPrim with ⟨Q, hQ⟩ | hCop |
    ⟨P₁, P₂, _, _, hDeg₁, _, hMul, _, hP₁DvdA⟩
  · exact absurd ⟨Q, hQ⟩ (hNoCommonConstFactor p hpDeg ⟨one, (LawfulCommRing.mul_one p).symm⟩)
  · exact hCop
  · exfalso
    have hSwapEq : (C p : Poly2 E) = mul (swapVZ.toFun P₁) (swapVZ.toFun P₂) := by
      have := congrArg swapVZ.toFun hMul
      rwa [swapVZ_constZ p, RingHom.map_mul] at this
    have hCpNe : (C p : Poly2 E) ≠ zero := Poly2.C_ne_zero hpNe
    have hS₁Ne : swapVZ.toFun P₁ ≠ zero := fun e =>
      hCpNe (by rw [hSwapEq, e, LawfulCommRing.zero_mul])
    have hS₂Ne : swapVZ.toFun P₂ ≠ zero := fun e =>
      hCpNe (by rw [hSwapEq, e, LawfulCommRing.mul_zero])
    have hSwapDeg : (swapVZ.toFun P₁).natDeg = 0 := by
      have hd := UPoly.natDeg_mul hS₁Ne hS₂Ne
      rw [← hSwapEq, Poly2.natDeg_C] at hd
      omega
    let g1 := vCoeff P₁ 0
    have hS₁C : swapVZ.toFun P₁ = C g1 := ext_coeffAt fun k => by
      cases k with
      | zero => rw [coeffAt_C_zero]; rfl
      | succ k => rw [coeffAt_C_succ]; exact (swapVZ.toFun P₁).coeffAt_eq_zero_of_natDeg_lt (by omega)
    let g2 := vCoeff P₂ 0
    have hS₂Deg : (swapVZ.toFun P₂).natDeg = 0 := by
      have hd := UPoly.natDeg_mul hS₁Ne hS₂Ne
      rw [← hSwapEq, Poly2.natDeg_C] at hd
      omega
    have hS₂C : swapVZ.toFun P₂ = C g2 := ext_coeffAt fun k => by
      cases k with
      | zero => rw [coeffAt_C_zero]; rfl
      | succ k => rw [coeffAt_C_succ]; exact (swapVZ.toFun P₂).coeffAt_eq_zero_of_natDeg_lt (by omega)
    have hpFact : p = mul g1 g2 := by
      rw [hS₁C, hS₂C, C_mul_eq] at hSwapEq
      have := congrArg (fun X : Poly2 E => coeffAt X.coeffs 0) hSwapEq
      simpa only [coeffAt_C_zero] using this
    have hP₁Eq : P₁ = (UPoly.mapHom CHom).toFun g1 := ext_coeffAt fun j => by
      rw [coeffAt_mapHom, CHom_apply]
      apply ext_coeffAt; intro k
      rw [← c2_swapVZ P₁ j k]
      cases k with
      | zero => rw [coeffAt_C_zero]
      | succ k =>
        have hvk0 : vCoeff P₁ (k + 1) = zero := by
          unfold vCoeff; rw [hS₁C, coeffAt_C_succ]
        rw [hvk0, coeffs_zero, coeffAt_nil, coeffAt_C_succ]
    have hg1Deg : 1 ≤ g1.natDeg := by
      have hd := UPoly.natDeg_mapHom CHom hCHomInj g1
      rw [← hP₁Eq] at hd; omega
    exact hNoCommonConstFactor g1 hg1Deg ⟨g2, hpFact⟩ (hP₁Eq ▸ hP₁DvdA)

end Field
end Poly2

/-! ## Assurance Witnesses -/

namespace BivariateFactorSplitTests
open UPoly Poly2

/-- Witness that `coprimeZ_const_of_vCoeff` is inhabited: `p(Z) = Z` and `A(V, Z) = V + Z`
    have `vCoeff A 1 = 1`, certifying `CoprimeZ (mapHom CHom X) (C X + X)`. -/
theorem inhabited_coprimeZ_const_of_vCoeff :
    ∃ (p : UPoly Goldilocks) (A : Poly2 Goldilocks) (k₀ : Nat) (u0 v0 : UPoly Goldilocks),
      1 ≤ p.natDeg ∧
      add (mul u0 p) (mul v0 (vCoeff A k₀)) = one ∧
      CoprimeZ ((UPoly.mapHom CHom).toFun p) A := by
  let p : UPoly Goldilocks := X
  let A : Poly2 Goldilocks := add (C X) X
  have hp : 1 ≤ p.natDeg := by decide +kernel
  have hv1 : vCoeff A 1 = one := by decide +kernel
  have hbez : add (mul zero p) (mul one (vCoeff A 1)) = one := by
    rw [hv1, LawfulCommRing.zero_mul, LawfulCommRing.zero_add, LawfulCommRing.mul_one]
  exact ⟨p, A, 1, zero, one, hp, hbez, coprimeZ_const_of_vCoeff p A hp 1 zero one hbez⟩

/-- `#tooth`: without a coprime `V`-coefficient, `coprimeZ_const_of_vCoeff`'s conclusion fails:
    for `p(Z) = Z` and `A(V, Z) = V · Z` (`vCoeff A 1 = Z`, sharing root `0` with `p`),
    `CoprimeZ (mapHom CHom p) A` is false because `(0, 0)` is a common zero at `c(0) = 0`?
    Even stronger: in `RatFunc Goldilocks[Z]`, `Z` divides both `Z` and `V · Z`! -/
theorem tooth_coprimeZ_needs_coprime_vCoeff :
    ∃ (p : UPoly Goldilocks) (A : Poly2 Goldilocks),
      1 ≤ p.natDeg ∧ vCoeff A 1 ≠ zero ∧ ¬ CoprimeZ ((UPoly.mapHom CHom).toFun p) A := by
  let p : UPoly Goldilocks := X
  let A : Poly2 Goldilocks := mul (C X) X
  refine ⟨p, A, by decide +kernel, by decide +kernel, ?_⟩
  rintro ⟨U, V, c, hc, hbez⟩
  have hPZ : (UPoly.mapHom CHom).toFun p = (X : Poly2 Goldilocks) := by decide +kernel
  rw [hPZ] at hbez
  have h0 := congrArg (fun Q : Poly2 Goldilocks => coeffAt Q.coeffs 0) hbez
  have hUX : coeffAt (mul U X).coeffs 0 = zero := by
    rw [LawfulCommRing.mul_comm, coeffAt_X_mul_zero]
  have hVA : coeffAt (mul V A).coeffs 0 = zero := by
    dsimp [A]
    have : mul V (mul (C X) X) = mul X (mul V (C X)) := by constructive_ring
    rw [this, coeffAt_X_mul_zero]
  rw [coeffAt_add, hUX, hVA, LawfulCommRing.add_zero, coeffAt_C_zero] at h0
  exact hc h0.symm

#verify_constructive Poly2.primY_dvd_of_dvd_FY Poly2.d5_split_prim
#verify_constructive Poly2.splitAgainstList Poly2.coprimeZ_const_of_vCoeff
#verify_constructive inhabited_coprimeZ_const_of_vCoeff tooth_coprimeZ_needs_coprime_vCoeff
#tooth_pair Poly2.coprimeZ_const_of_vCoeff vs tooth_coprimeZ_needs_coprime_vCoeff
#verify_inhabited Poly2.coprimeZ_const_of_vCoeff inhabited_coprimeZ_const_of_vCoeff

end BivariateFactorSplitTests

end Qsag
end
