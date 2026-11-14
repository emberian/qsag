module
/-
# Qsag.CodingTheory.PolyMv3 — constructive trivariate polynomials `F[X][Y][Z]`

`UPoly R` is the ring of canonical (trimmed) coefficient lists over any lawful commutative
ring with decidable equality. It is again such a ring, so towers are free:
`Poly3 F := UPoly (UPoly (UPoly F))` is `F[X][Y][Z]` with `Z` outermost.

Contents:
* `UPoly R` with `LawfulCommRing`, `NoZeroDivisors` (over a domain) and exact product length.
* Ring homomorphisms, `eval₂`, coefficient maps, and the Horner decomposition.
* Weighted degrees `wdeg w s` (a degree function on `R` lifts to `UPoly R`), giving
  `degZ`, `degYZ` and the `(1, 1, d)`-weighted `deg11d`.
* `evalAffineLine Q α β P = Q(X, α + βX, P(X))`, multiplicative, with
  `deg_evalAffineLine_le`.
* Taylor shift `p(b + W)`: a ring homomorphism (the Leibniz rule in generating-function
  form) whose coefficients are the Hasse derivatives `gsUniHasse`.
-/

public import Qsag.AffineProximityGaps
import all Qsag.AffineProximityGaps
public import Qsag.Tactic.ConstructiveRing

public section
namespace Qsag

set_option autoImplicit false

open CommRingOps RoundPoly

/-- Canonical univariate polynomials over `R`: coefficient lists without trailing zeros. -/
structure UPoly (R : Type) [CommRingOps R] [DecidableEq R] where
  coeffs : List R
  trimmed : trimPoly coeffs = coeffs

namespace UPoly

section Ring
variable {R : Type} [LawfulCommRing R] [DecidableEq R]

theorem ext {a b : UPoly R} (h : a.coeffs = b.coeffs) : a = b := by
  cases a; cases b; cases h; rfl

instance : DecidableEq (UPoly R) := fun a b =>
  if h : a.coeffs = b.coeffs then .isTrue (ext h) else .isFalse (fun e => h (e ▸ rfl))

/-- Canonicalize a coefficient list. -/
def ofList (l : List R) : UPoly R := ⟨trimPoly l, trimPoly_idem l⟩

theorem coeffs_ofList (l : List R) : (ofList l).coeffs = trimPoly l := by rfl

theorem pAdd_trimmed (a b : List R) : trimPoly (pAdd a b) = pAdd a b := trimPoly_idem _
theorem pMul_trimmed (a b : List R) : trimPoly (pMul a b) = pMul a b := trimPoly_idem _
theorem pNeg_trimmed (a : List R) : trimPoly (pNeg a) = pNeg a := trimPoly_idem _
theorem pSub_trimmed (a b : List R) : trimPoly (pSub a b) = pSub a b := trimPoly_idem _

instance instLawfulCommRing : LawfulCommRing (UPoly R) where
  zero := ofList []
  one := ofList [one]
  add a b := ⟨pAdd a.coeffs b.coeffs, pAdd_trimmed _ _⟩
  mul a b := ⟨pMul a.coeffs b.coeffs, pMul_trimmed _ _⟩
  neg a := ⟨pNeg a.coeffs, pNeg_trimmed _⟩
  sub a b := ⟨pSub a.coeffs b.coeffs, pSub_trimmed _ _⟩
  add_assoc a b c := ext (pAdd_assoc a.coeffs b.coeffs c.coeffs)
  add_comm a b := ext (pAdd_comm a.coeffs b.coeffs)
  zero_add a := by
    apply ext
    show pAdd [] a.coeffs = a.coeffs
    rw [pAdd_nil_left, a.trimmed]
  add_zero a := by
    apply ext
    show pAdd a.coeffs [] = a.coeffs
    rw [pAdd_nil_right, a.trimmed]
  add_left_neg a := by
    apply ext
    show trimPoly (rawAddCoeffs (pNeg a.coeffs) a.coeffs) = trimPoly []
    rw [trimPoly_eq_iff_coeffAt]
    intro k
    rw [coeffAt_addCoeffs, coeffAt_pNeg, LawfulCommRing.add_left_neg, coeffAt_nil]
  sub_eq_add_neg a b := ext (pSub_eq_pAdd_pNeg a.coeffs b.coeffs)
  mul_assoc a b c := ext (pMul_assoc a.coeffs b.coeffs c.coeffs)
  mul_comm a b := ext (pMul_comm a.coeffs b.coeffs)
  one_mul a := by
    apply ext
    show pMul (trimPoly [one]) a.coeffs = a.coeffs
    rw [pMul_trimPoly_left, pMul_comm, pMul_one_right, a.trimmed]
  mul_one a := by
    apply ext
    show pMul a.coeffs (trimPoly [one]) = a.coeffs
    rw [pMul_trimPoly_right, pMul_one_right, a.trimmed]
  left_distrib a b c := ext (pMul_pAdd_right a.coeffs b.coeffs c.coeffs)
  right_distrib a b c := ext (pMul_pAdd_left a.coeffs b.coeffs c.coeffs)

theorem coeffs_zero : (zero : UPoly R).coeffs = [] := by rfl
theorem coeffs_add (a b : UPoly R) : (add a b).coeffs = pAdd a.coeffs b.coeffs := by rfl
theorem coeffs_mul (a b : UPoly R) : (mul a b).coeffs = pMul a.coeffs b.coeffs := by rfl
theorem coeffs_neg (a : UPoly R) : (neg a).coeffs = pNeg a.coeffs := by rfl
theorem coeffs_sub (a b : UPoly R) : (sub a b).coeffs = pSub a.coeffs b.coeffs := by rfl

theorem eq_zero_iff (a : UPoly R) : a = zero ↔ a.coeffs = [] :=
  ⟨fun h => h ▸ rfl, fun h => ext h⟩

/-- Coefficientwise extensionality. -/
theorem ext_coeffAt {a b : UPoly R} (h : ∀ k, coeffAt a.coeffs k = coeffAt b.coeffs k) :
    a = b := by
  apply ext
  rw [← a.trimmed, ← b.trimmed]
  exact (trimPoly_eq_iff_coeffAt _ _).mpr h

theorem coeffAt_add (a b : UPoly R) (k : Nat) :
    coeffAt (add a b).coeffs k = add (coeffAt a.coeffs k) (coeffAt b.coeffs k) :=
  coeffAt_pAdd _ _ k

theorem coeffAt_neg (a : UPoly R) (k : Nat) :
    coeffAt (neg a).coeffs k = neg (coeffAt a.coeffs k) := coeffAt_pNeg _ k

theorem coeffAt_sub (a b : UPoly R) (k : Nat) :
    coeffAt (sub a b).coeffs k = sub (coeffAt a.coeffs k) (coeffAt b.coeffs k) :=
  coeffAt_pSub _ _ k

theorem coeffAt_ofList (l : List R) (k : Nat) : coeffAt (ofList l).coeffs k = coeffAt l k :=
  coeffAt_trimPoly l k

/-- The degree, with `natDeg 0 = 0`. -/
def natDeg (p : UPoly R) : Nat := p.coeffs.length - 1

/-- The leading coefficient (`zero` for the zero polynomial). -/
def lead (p : UPoly R) : R := coeffAt p.coeffs p.natDeg

theorem lead_ne_zero {p : UPoly R} (h : p ≠ zero) : p.lead ≠ zero := by
  have hne : trimPoly p.coeffs ≠ [] := by
    rw [p.trimmed]; exact fun e => h ((eq_zero_iff p).mpr e)
  have := leadCoeff_ne_zero_of_trimPoly_ne_nil p.coeffs hne
  rwa [p.trimmed] at this

theorem coeffAt_eq_zero_of_natDeg_lt (p : UPoly R) {k : Nat} (h : p.natDeg < k) :
    coeffAt p.coeffs k = zero :=
  coeffAt_eq_zero_of_ge p.coeffs k (by unfold natDeg at h; omega)

theorem natDeg_le_of_coeffAt (p : UPoly R) (B : Nat)
    (h : ∀ k, B < k → coeffAt p.coeffs k = zero) : p.natDeg ≤ B := by
  have := length_trimPoly_le_of_coeffAt_zero p.coeffs (B + 1) (fun k hk => h k (by omega))
  rw [p.trimmed] at this
  unfold natDeg; omega

/-- Coefficients of a product above the sum of the degrees vanish, and the top one is the
    product of the leading coefficients. -/
theorem coeffAt_mul_top (a b : UPoly R) :
    (∀ k, a.natDeg + b.natDeg < k → coeffAt (mul a b).coeffs k = zero) ∧
    coeffAt (mul a b).coeffs (a.natDeg + b.natDeg) = mul a.lead b.lead := by
  have h := coeffAt_rawMul_high b.coeffs b.natDeg
    (fun j hj => b.coeffAt_eq_zero_of_natDeg_lt hj) a.natDeg a.coeffs
    (fun i hi => a.coeffAt_eq_zero_of_natDeg_lt hi)
  refine ⟨fun k hk => ?_, ?_⟩
  · show coeffAt (trimPoly (rawMul a.coeffs b.coeffs)) k = zero
    rw [coeffAt_trimPoly]; exact h.1 k hk
  · show coeffAt (trimPoly (rawMul a.coeffs b.coeffs)) _ = _
    rw [coeffAt_trimPoly]; exact h.2

theorem natDeg_mul_le (a b : UPoly R) : (mul a b).natDeg ≤ a.natDeg + b.natDeg :=
  natDeg_le_of_coeffAt _ _ (coeffAt_mul_top a b).1

theorem natDeg_add_le (a b : UPoly R) : (add a b).natDeg ≤ max a.natDeg b.natDeg := by
  apply natDeg_le_of_coeffAt
  intro k hk
  have hk' : a.natDeg < k ∧ b.natDeg < k := by
    have := Nat.le_max_left a.natDeg b.natDeg
    have := Nat.le_max_right a.natDeg b.natDeg
    omega
  rw [coeffAt_add, a.coeffAt_eq_zero_of_natDeg_lt hk'.1, b.coeffAt_eq_zero_of_natDeg_lt hk'.2,
    LawfulCommRing.add_zero]

instance [NoZeroDivisors R] : NoZeroDivisors (UPoly R) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b h
    if ha : a = zero then exact .inl ha
    else if hb : b = zero then exact .inr hb
    else
      exfalso
      have htop := (coeffAt_mul_top a b).2
      rw [show (CommRingOps.mul a b) = zero from h, coeffs_zero, coeffAt_nil] at htop
      rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero htop.symm with h1 | h1
      · exact lead_ne_zero ha h1
      · exact lead_ne_zero hb h1

/-- Over a domain the degree of a product of nonzero polynomials is the sum of degrees. -/
theorem natDeg_mul [NoZeroDivisors R] {a b : UPoly R} (ha : a ≠ zero) (hb : b ≠ zero) :
    (mul a b).natDeg = a.natDeg + b.natDeg := by
  apply Nat.le_antisymm (natDeg_mul_le a b)
  apply Decidable.byContradiction
  intro hlt
  have hz := (mul a b).coeffAt_eq_zero_of_natDeg_lt (Nat.lt_of_not_le hlt)
  rw [(coeffAt_mul_top a b).2] at hz
  rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hz with h1 | h1
  · exact lead_ne_zero ha h1
  · exact lead_ne_zero hb h1

end Ring

end UPoly

end Qsag
end
