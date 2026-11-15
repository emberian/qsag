module
/-
# Qsag.Coding.BivariateGauss — Total-Degree Additivity & Constructive Gauss's Lemma

Constructive bivariate polynomial content and primitivity over any field `E`
(`[LawfulField E] [DecidableEq E]`, `0 Classical.choice`, `0` irreducible factorization):
* `Poly2.tdeg_mul`: additivity of total degree `tdeg (mul A B) = tdeg A + tdeg B` via the
  homogenization homomorphism `P(Y, Z) ↦ P(T, X · T)`.
* `Poly2.IsPrimY`, `Poly2.contY`, `Poly2.primY`, `Poly2.contY_mul_primY`: `Y`-content extraction
  and `Y`-primitive decomposition `A = C (contY A) * primY A`.
* `Poly2.isPrimY_mul`: constructive Gauss's Lemma via `UPoly.d5_split` dynamic Euclidean
  refinement against minimal non-divisible `Z`-coefficients.
-/

public import Qsag.Coding.DynamicGcdSplit
import all Qsag.Coding.PolyMv3
import all Qsag.Coding.SylvesterResultant
import all Qsag.Coding.DynamicGcdSplit
import all Qsag.Coding.AffineProximityGaps
import all Qsag.Math.Goldilocks

public section
namespace Qsag

set_option autoImplicit false

open CommRingOps RoundPoly

namespace Poly2
section Field
variable {E : Type} [LawfulField E] [DecidableEq E]
open UPoly

local instance : NoZeroDivisors E := LawfulField.toNoZeroDivisors E

theorem C_mul_eq {R : Type} [LawfulCommRing R] [DecidableEq R] (a b : R) :
    mul (C a) (C b) = (C (mul a b) : UPoly R) :=
  (CHom.map_mul a b).symm

theorem C_zero_eq {R : Type} [LawfulCommRing R] [DecidableEq R] :
    (C (zero : R) : UPoly R) = zero :=
  CHom.map_zero

/-! ## Total-degree additivity via homogenization `P(Y, Z) ↦ P(T, X·T)` -/

abbrev c2 (P : Poly2 E) (i d : Nat) : E :=
  coeffAt (coeffAt P.coeffs d).coeffs i

theorem c2_zero (i d : Nat) : c2 (zero : Poly2 E) i d = zero := by
  show coeffAt (coeffAt ([] : List (UPoly E)) d).coeffs i = zero
  rw [coeffAt_nil, coeffs_zero, coeffAt_nil]

theorem c2_add (A B : Poly2 E) (i d : Nat) :
    c2 (add A B) i d = add (c2 A i d) (c2 B i d) := by
  show coeffAt (coeffAt (add A B).coeffs d).coeffs i = _
  rw [coeffAt_add, coeffAt_add]

def innerHom : RingHom (UPoly E) (Poly2 E) :=
  eval₂Hom (CHom.comp CHom) X

private def homogHom : RingHom (Poly2 E) (Poly2 E) :=
  eval₂Hom innerHom (mul (C X) X)

theorem c2_X_mul_zero (H : Poly2 E) (i : Nat) : c2 (mul X H) i 0 = zero := by
  show coeffAt (coeffAt (mul X H).coeffs 0).coeffs i = zero
  rw [coeffAt_X_mul_zero, coeffs_zero, coeffAt_nil]

theorem c2_X_mul_succ (H : Poly2 E) (i d : Nat) :
    c2 (mul X H) i (d + 1) = c2 H i d := by
  show coeffAt (coeffAt (mul X H).coeffs (d + 1)).coeffs i = _
  rw [coeffAt_X_mul_succ]

theorem c2_CX_mul_zero (H : Poly2 E) (d : Nat) : c2 (mul (C X) H) 0 d = zero := by
  show coeffAt (coeffAt (mul (C X) H).coeffs d).coeffs 0 = zero
  rw [coeffAt_C_mul, coeffAt_X_mul_zero]

theorem c2_CX_mul_succ (H : Poly2 E) (j d : Nat) :
    c2 (mul (C X) H) (j + 1) d = c2 H j d := by
  show coeffAt (coeffAt (mul (C X) H).coeffs d).coeffs (j + 1) = _
  rw [coeffAt_C_mul, coeffAt_X_mul_succ]

theorem c2_innerHom_eval :
    ∀ (cs : List E) (j d : Nat),
      c2 (evalCoeffs (cs.map (CHom.comp (CHom (R := E))).toFun) X) j d =
        if j = 0 then coeffAt cs d else zero
  | [], j, d => by
    show c2 (zero : Poly2 E) j d = _
    rw [c2_zero]
    split
    · exact (coeffAt_nil d).symm
    · rfl
  | c :: tl, j, d => by
    show c2 (add (C (C c)) (mul X (evalCoeffs _ X))) j d = _
    rw [c2_add]
    cases d with
    | zero =>
      rw [c2_X_mul_zero, LawfulCommRing.add_zero]
      show coeffAt (coeffAt (C (C c)).coeffs 0).coeffs j = _
      rw [coeffAt_C_zero]
      cases j with
      | zero => rw [coeffAt_C_zero]; rfl
      | succ j => rw [coeffAt_C_succ]; rfl
    | succ d =>
      have hCC0 : c2 (C (C c) : Poly2 E) j (d + 1) = zero := by
        show coeffAt (coeffAt (C (C c)).coeffs (d + 1)).coeffs j = zero
        rw [coeffAt_C_succ, coeffs_zero, coeffAt_nil]
      rw [hCC0, LawfulCommRing.zero_add, c2_X_mul_succ, c2_innerHom_eval tl j d]
      cases j <;> rfl

private theorem c2_homog_eval :
    ∀ (qs : List (UPoly E)) (j d : Nat),
      c2 (evalCoeffs (qs.map (innerHom (E := E)).toFun) (mul (C X) X)) j d =
        if j ≤ d then coeffAt (coeffAt qs j).coeffs (d - j) else zero
  | [], j, d => by
    show c2 (zero : Poly2 E) j d = _
    rw [c2_zero]
    split
    · rw [coeffAt_nil, coeffs_zero, coeffAt_nil]
    · rfl
  | q :: tl, j, d => by
    show c2 (add (innerHom.toFun q) (mul (mul (C X) X) (evalCoeffs _ _))) j d = _
    rw [c2_add, LawfulCommRing.mul_assoc]
    have hq : c2 (innerHom.toFun q) j d = if j = 0 then coeffAt q.coeffs d else zero :=
      c2_innerHom_eval q.coeffs j d
    rw [hq]
    cases j with
    | zero =>
      rw [c2_CX_mul_zero, LawfulCommRing.add_zero]
      rfl
    | succ j =>
      rw [c2_CX_mul_succ]
      cases d with
      | zero =>
        rw [c2_X_mul_zero]
        simp [LawfulCommRing.add_zero]
      | succ d =>
        rw [c2_X_mul_succ, c2_homog_eval tl j d]
        simp only [Nat.succ_ne_zero, ↓reduceIte, LawfulCommRing.zero_add, Nat.succ_le_succ_iff,
          Nat.succ_sub_succ_eq_sub, coeffAt_cons_succ]

private theorem c2_homogHom (P : Poly2 E) (j d : Nat) :
    c2 (homogHom.toFun P) j d = if j ≤ d then c2 P (d - j) j else zero :=
  c2_homog_eval P.coeffs j d

private theorem homogHom_ne_zero {P : Poly2 E} (hP : P ≠ zero) : homogHom.toFun P ≠ zero := by
  intro h0
  apply hP
  apply ext_coeffAt; intro j
  rw [coeffs_zero, coeffAt_nil]
  apply ext_coeffAt; intro i
  rw [coeffs_zero, coeffAt_nil]
  have h := c2_homogHom P j (i + j)
  rw [h0, c2_zero] at h
  have hle : j ≤ i + j := Nat.le_add_left j i
  simp only [hle, ↓reduceIte, show i + j - j = i by omega] at h
  exact h.symm

private theorem natDeg_homogHom (P : Poly2 E) : (homogHom.toFun P).natDeg = tdeg P := by
  apply Nat.le_antisymm
  · refine natDeg_le_of_coeffAt _ (tdeg P) (fun d hd => ext_coeffAt fun j => ?_)
    rw [coeffs_zero, coeffAt_nil]
    have h := c2_homogHom P j d
    show c2 (homogHom.toFun P) j d = zero
    rw [h]
    split
    · next hjd =>
      if hcj : coeffAt P.coeffs j = zero then
        show coeffAt (coeffAt P.coeffs j).coeffs (d - j) = zero
        rw [hcj, coeffs_zero, coeffAt_nil]
      else
        have hw : (coeffAt P.coeffs j).natDeg + 1 * j ≤ tdeg P := le_wdeg UPoly.natDeg 1 P j hcj
        exact (coeffAt P.coeffs j).coeffAt_eq_zero_of_natDeg_lt (by omega)
    · rfl
  · if hP : P = zero then
      rw [hP, RingHom.map_zero]
      have ht0 : tdeg (zero : Poly2 E) = 0 :=
        Nat.le_zero.mp (wdeg_le _ _ _ 0 (fun _ hk => absurd (by rw [coeffs_zero, coeffAt_nil]) hk))
      rw [ht0]; exact Nat.zero_le _
    else
      apply Decidable.byContradiction
      intro hlt
      have hlt' : (homogHom.toFun P).natDeg < tdeg P := Nat.lt_of_not_le hlt
      apply Nat.lt_irrefl (tdeg P)
      refine Nat.lt_of_le_of_lt (wdeg_le UPoly.natDeg 1 P ((homogHom.toFun P).natDeg) ?_) hlt'
      intro j hcj
      have hlead := lead_ne_zero hcj
      let i := (coeffAt P.coeffs j).natDeg
      show i + 1 * j ≤ (homogHom.toFun P).natDeg
      apply Decidable.byContradiction
      intro hij
      have hdgt : (homogHom.toFun P).natDeg < i + j := by omega
      have hz : coeffAt (homogHom.toFun P).coeffs (i + j) = zero :=
        (homogHom.toFun P).coeffAt_eq_zero_of_natDeg_lt hdgt
      have hz2 : c2 (homogHom.toFun P) j (i + j) = zero := by
        show coeffAt (coeffAt (homogHom.toFun P).coeffs (i + j)).coeffs j = zero
        rw [hz, coeffs_zero, coeffAt_nil]
      have hle : j ≤ i + j := Nat.le_add_left j i
      rw [c2_homogHom] at hz2
      simp only [hle, ↓reduceIte, show i + j - j = i by omega] at hz2
      exact hlead hz2

/-- **Total-degree additivity (`tdeg_mul`)**: over a field, `tdeg (mul A B) = tdeg A + tdeg B`
    for nonzero bivariate polynomials `A, B`. -/
theorem tdeg_mul {A B : Poly2 E} (hA : A ≠ zero) (hB : B ≠ zero) :
    tdeg (mul A B) = tdeg A + tdeg B := by
  rw [← natDeg_homogHom (mul A B), RingHom.map_mul,
    UPoly.natDeg_mul (homogHom_ne_zero hA) (homogHom_ne_zero hB),
    natDeg_homogHom A, natDeg_homogHom B]

theorem tdeg_C (c : UPoly E) : tdeg (C c : Poly2 E) = c.natDeg := by
  if hc : c = zero then
    subst hc
    rw [C_zero_eq]
    have hc0 : (zero : UPoly E).natDeg = 0 := rfl
    rw [hc0]
    exact Nat.le_zero.mp (wdeg_le _ _ _ 0 (fun _ hk => absurd (by rw [coeffs_zero, coeffAt_nil]) hk))
  else
    apply Nat.le_antisymm
    · refine wdeg_le UPoly.natDeg 1 (C c) c.natDeg (fun k hk => ?_)
      cases k with
      | zero => rw [coeffAt_C_zero]; omega
      | succ k => exact absurd (coeffAt_C_succ c k) hk
    · have h0 : coeffAt (C c : Poly2 E).coeffs 0 ≠ zero := by rw [coeffAt_C_zero]; exact hc
      have hw : (coeffAt (C c : Poly2 E).coeffs 0).natDeg + 1 * 0 ≤ tdeg (C c) :=
        le_wdeg UPoly.natDeg 1 (C c) 0 h0
      rw [coeffAt_C_zero] at hw; omega

/-! ## `Y`-content, `Y`-primitive polynomials, and constructive Gauss's Lemma -/

/-- `A ∈ E[Y][Z]` is `Y`-primitive if it is nonzero and every common divisor in `E[Y]` of its
    `Z`-coefficients has `Y`-degree `0`. -/
@[expose] def IsPrimY (A : Poly2 E) : Prop :=
  A ≠ zero ∧ ∀ g : UPoly E, (∀ k, ∃ q, coeffAt A.coeffs k = mul g q) → g.natDeg = 0

private def gcdList : List (UPoly E) → UPoly E
  | [] => zero
  | a :: as => (UPoly.xgcd a (gcdList as)).1

/-- The `Y`-content of `A`. -/
def contY (A : Poly2 E) : UPoly E := gcdList A.coeffs

/-- The `Y`-primitive part of `A`, obtained by dividing every `Z`-coefficient by `contY A`. -/
def primY (A : Poly2 E) : Poly2 E :=
  ofList (A.coeffs.map fun c => (UPoly.divMod c (contY A)).1)

theorem xgcd_spec (a b : UPoly E) :
    add (mul (UPoly.xgcd a b).2.1 a) (mul (UPoly.xgcd a b).2.2 b) = (UPoly.xgcd a b).1 ∧
      (∃ s, a = mul (UPoly.xgcd a b).1 s) ∧ (∃ t, b = mul (UPoly.xgcd a b).1 t) :=
  UPoly.xgcdAux_spec b.coeffs.length a b (Nat.le_refl _)

private theorem gcdList_dvd_and_bezout :
    ∀ cs : List (UPoly E),
      (∀ k, ∃ q, coeffAt cs k = mul (gcdList cs) q) ∧
      (∀ g : UPoly E, (∀ k, ∃ q, coeffAt cs k = mul g q) → ∃ t, gcdList cs = mul g t)
  | [] => ⟨fun k => ⟨zero, by rw [coeffAt_nil]; exact (LawfulCommRing.mul_zero _).symm⟩,
      fun g _ => ⟨zero, (LawfulCommRing.mul_zero g).symm⟩⟩
  | a :: tl => by
    obtain ⟨hdvdTl, hbezTl⟩ := gcdList_dvd_and_bezout tl
    obtain ⟨hbez, ⟨sa, hsa⟩, ⟨sb, hsb⟩⟩ := xgcd_spec a (gcdList tl)
    refine ⟨fun k => ?_, fun g hg => ?_⟩
    · cases k with
      | zero => exact ⟨sa, hsa⟩
      | succ k =>
        obtain ⟨q, hq⟩ := hdvdTl k
        refine ⟨mul sb q, ?_⟩
        show coeffAt tl k = mul (UPoly.xgcd a (gcdList tl)).1 (mul sb q)
        conv => lhs; rw [hq, hsb, LawfulCommRing.mul_assoc]
    · obtain ⟨qa, hqa⟩ := hg 0
      obtain ⟨qb, hqb⟩ := hbezTl g (fun k => hg (k + 1))
      refine ⟨add (mul (UPoly.xgcd a (gcdList tl)).2.1 qa)
        (mul (UPoly.xgcd a (gcdList tl)).2.2 qb), ?_⟩
      show (UPoly.xgcd a (gcdList tl)).1 = _
      rw [← hbez, show a = mul g qa from hqa, hqb]
      constructive_ring

theorem eq_C_lead_of_natDeg_zero {u : UPoly E} (hd : u.natDeg = 0) : u = C u.lead :=
  ext_coeffAt fun k => by
    cases k with
    | zero => rw [coeffAt_C_zero]; show _ = coeffAt u.coeffs u.natDeg; rw [hd]
    | succ k => rw [coeffAt_C_succ]; exact u.coeffAt_eq_zero_of_natDeg_lt (by omega)

private theorem divMod_exact_of_mul (g q : UPoly E) (hg : g ≠ zero) :
    (UPoly.divMod (mul g q) g).1 = q := by
  obtain ⟨hdiv, hlen⟩ := UPoly.divMod_spec (mul g q) g hg
  generalize (UPoly.divMod (mul g q) g).1 = q' at hdiv
  generalize (UPoly.divMod (mul g q) g).2 = r at hdiv hlen
  have hrEq : r = mul g (sub q q') := by
    apply LawfulCommRing.add_left_cancel (a := mul q' g)
    rw [← hdiv]; constructive_ring
  if hsub : sub q q' = zero then
    exact (LawfulCommRing.sub_eq_zero_iff.mp hsub).symm
  else
    exfalso
    have hr0 : r ≠ zero := fun e => mul_ne_zero' hg hsub (hrEq.symm.trans e)
    have hdeg := UPoly.natDeg_mul hg hsub
    rw [← hrEq] at hdeg
    have hgPos : 1 ≤ g.coeffs.length := by
      cases hc : g.coeffs with
      | nil => exact absurd (UPoly.ext hc) hg
      | cons _ _ => exact Nat.succ_pos _
    have hrPos : 1 ≤ r.coeffs.length := by
      cases hc : r.coeffs with
      | nil => exact absurd (UPoly.ext hc) hr0
      | cons _ _ => exact Nat.succ_pos _
    unfold UPoly.natDeg at hdeg
    omega

theorem coeffAt_map_zero_fn {α β : Type} [CommRingOps α] [CommRingOps β]
    (f : α → β) (hf0 : f zero = zero) :
    ∀ (l : List α) (k : Nat), coeffAt (l.map f) k = f (coeffAt l k)
  | [], k => by rw [List.map_nil, coeffAt_nil, coeffAt_nil, hf0]
  | _ :: _, 0 => rfl
  | _ :: tl, k + 1 => coeffAt_map_zero_fn f hf0 tl k

theorem coeffAt_map_mul_left (c : UPoly E) :
    ∀ (bs : List (UPoly E)) (k : Nat), coeffAt (bs.map (mul c)) k = mul c (coeffAt bs k) :=
  coeffAt_map_zero_fn (mul c) (LawfulCommRing.mul_zero c)

/-- Decomposition `A = C(contY A) * primY A` for any `A ≠ zero`. -/
theorem contY_mul_primY {A : Poly2 E} (hA : A ≠ zero) :
    contY A ≠ zero ∧ IsPrimY (primY A) ∧ A = mul (C (contY A)) (primY A) ∧
      (primY A).natDeg = A.natDeg ∧ (contY A).natDeg + tdeg (primY A) = tdeg A := by
  obtain ⟨hdvd, hbez⟩ := gcdList_dvd_and_bezout A.coeffs
  change (∀ k, ∃ q, coeffAt A.coeffs k = mul (contY A) q) at hdvd
  change (∀ g : UPoly E, (∀ k, ∃ q, coeffAt A.coeffs k = mul g q) → ∃ t, contY A = mul g t) at hbez
  have hcNe : contY A ≠ zero := fun hc0 => by
    apply hA; apply ext_coeffAt; intro k
    obtain ⟨q, hq⟩ := hdvd k
    rw [coeffs_zero, coeffAt_nil, hq, hc0, LawfulCommRing.zero_mul]
  have hCoeff : ∀ k, coeffAt A.coeffs k = mul (contY A) (coeffAt (primY A).coeffs k) := by
    intro k
    obtain ⟨q, hq⟩ := hdvd k
    unfold primY
    have hf0 : (UPoly.divMod zero (contY A)).1 = zero := by
      have h0 : (zero : UPoly E) = mul (contY A) zero := (LawfulCommRing.mul_zero _).symm
      conv => lhs; rw [h0]
      exact divMod_exact_of_mul (contY A) zero hcNe
    rw [coeffAt_ofList, coeffAt_map_zero_fn _ hf0, hq, divMod_exact_of_mul (contY A) q hcNe]
  have hEq : A = mul (C (contY A)) (primY A) := ext_coeffAt fun k => by
    rw [coeffAt_C_mul]; exact hCoeff k
  have hpNe : primY A ≠ zero := fun hp0 => hA (by rw [hEq, hp0, LawfulCommRing.mul_zero])
  have hPrim : IsPrimY (primY A) := ⟨hpNe, fun g hg => by
    have hAll : ∀ k, ∃ q, coeffAt A.coeffs k = mul (mul (contY A) g) q := fun k => by
      obtain ⟨q, hq⟩ := hg k
      exact ⟨q, by rw [hCoeff k, hq, LawfulCommRing.mul_assoc]⟩
    obtain ⟨t, ht⟩ := hbez (mul (contY A) g) hAll
    have ht1 : mul one (contY A) = mul (mul g t) (contY A) := by
      rw [LawfulCommRing.one_mul]
      have : mul (mul g t) (contY A) = mul (mul (contY A) g) t := by constructive_ring
      rw [this, ← ht]
    have hgt : one = mul g t := mul_right_cancel' hcNe ht1
    have hg0 : g ≠ zero := fun e => NontrivialRing.one_ne_zero (by rw [hgt, e, LawfulCommRing.zero_mul])
    have ht0 : t ≠ zero := fun e => NontrivialRing.one_ne_zero (by rw [hgt, e, LawfulCommRing.mul_zero])
    have hdeg := UPoly.natDeg_mul hg0 ht0
    rw [← hgt, natDeg_one] at hdeg; omega⟩
  have hDegZ : (primY A).natDeg = A.natDeg := by
    have := UPoly.natDeg_mul (Poly2.C_ne_zero hcNe) hpNe
    rw [← hEq, Poly2.natDeg_C, Nat.zero_add] at this
    exact this.symm
  have hTdeg : (contY A).natDeg + tdeg (primY A) = tdeg A := by
    have := tdeg_mul (Poly2.C_ne_zero hcNe) hpNe
    rw [← hEq, tdeg_C] at this
    exact this.symm
  exact ⟨hcNe, hPrim, hEq, hDegZ, hTdeg⟩

/-! ### Constructive Gauss's Lemma (via `UPoly.d5_split`, zero irreducible factorization) -/

private def DvdU (g x : UPoly E) : Prop := ∃ q, x = mul g q

private theorem dvdU_zero (g : UPoly E) : DvdU g zero :=
  ⟨zero, (LawfulCommRing.mul_zero g).symm⟩

private theorem dvdU_add {g x y : UPoly E} (hx : DvdU g x) (hy : DvdU g y) : DvdU g (add x y) := by
  obtain ⟨qx, rfl⟩ := hx; obtain ⟨qy, rfl⟩ := hy
  exact ⟨add qx qy, (LawfulCommRing.left_distrib g qx qy).symm⟩

private theorem dvdU_mul_right {g x : UPoly E} (hx : DvdU g x) (y : UPoly E) : DvdU g (mul x y) := by
  obtain ⟨q, rfl⟩ := hx; exact ⟨mul q y, LawfulCommRing.mul_assoc g q y⟩

private theorem dvdU_trans {g' g x : UPoly E} (hg : DvdU g' g) (hx : DvdU g x) : DvdU g' x := by
  obtain ⟨t, rfl⟩ := hg; obtain ⟨q, rfl⟩ := hx
  exact ⟨mul t q, LawfulCommRing.mul_assoc g' t q⟩

private theorem coeffAt_rawAddCoeffs (as bs : List (UPoly E)) (k : Nat) :
    coeffAt (rawAddCoeffs as bs) k = add (coeffAt as k) (coeffAt bs k) := by
  induction as generalizing bs k with
  | nil => cases bs <;> simp [rawAddCoeffs, coeffAt_nil, LawfulCommRing.zero_add]
  | cons a tl ih =>
    cases bs with
    | nil => cases k <;> simp [rawAddCoeffs, coeffAt_nil, LawfulCommRing.add_zero]
    | cons _ btl =>
      cases k with
      | zero => rfl
      | succ k => exact ih btl k

private theorem dvdU_rawMul_lt (g : UPoly E) (bs : List (UPoly E)) (k : Nat)
    (hbs : ∀ j, j < k → DvdU g (coeffAt bs j)) :
    ∀ (as : List (UPoly E)) (m : Nat), m < k → DvdU g (coeffAt (rawMul as bs) m)
  | [], m, _ => by show DvdU g (coeffAt [] m); rw [coeffAt_nil]; exact dvdU_zero g
  | a :: tl, m, hm => by
    show DvdU g (coeffAt (rawAddCoeffs (bs.map (mul a)) (zero :: rawMul tl bs)) m)
    rw [coeffAt_rawAddCoeffs, coeffAt_map_mul_left]
    refine dvdU_add ?_ ?_
    · obtain ⟨q, hq⟩ := hbs m hm
      exact ⟨mul a q, by rw [hq]; constructive_ring⟩
    · cases m with
      | zero => exact dvdU_zero g
      | succ m' => exact dvdU_rawMul_lt g bs k hbs tl m' (by omega)

private theorem rawMul_pivot_congr (g : UPoly E) (bs : List (UPoly E)) (j₀ : Nat)
    (hbs : ∀ j, j < j₀ → DvdU g (coeffAt bs j)) :
    ∀ (i₀ : Nat) (as : List (UPoly E)),
      (∀ i, i < i₀ → DvdU g (coeffAt as i)) →
      ∃ q, coeffAt (rawMul as bs) (i₀ + j₀) =
        add (mul (coeffAt as i₀) (coeffAt bs j₀)) (mul g q)
  | 0, [], _ =>
    ⟨zero, by
      show zero = add (mul zero (coeffAt bs j₀)) (mul g zero)
      rw [LawfulCommRing.zero_mul, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]⟩
  | 0, a :: tl, _ => by
    rw [Nat.zero_add]
    show ∃ q, coeffAt (rawAddCoeffs (bs.map (mul a)) (zero :: rawMul tl bs)) j₀ =
      add (mul a (coeffAt bs j₀)) (mul g q)
    rw [coeffAt_rawAddCoeffs, coeffAt_map_mul_left]
    cases j₀ with
    | zero => exact ⟨zero, by show add _ zero = _; rw [LawfulCommRing.mul_zero]⟩
    | succ j' =>
      obtain ⟨q, hq⟩ := dvdU_rawMul_lt g bs (j' + 1) hbs tl j' (Nat.lt_succ_self j')
      exact ⟨q, by show add _ (coeffAt (rawMul tl bs) j') = _; rw [hq]⟩
  | i' + 1, [], _ =>
    ⟨zero, by
      show zero = add (mul zero (coeffAt bs j₀)) (mul g zero)
      rw [LawfulCommRing.zero_mul, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]⟩
  | i' + 1, a :: tl, has => by
    rw [Nat.succ_add]
    show ∃ q, coeffAt (rawAddCoeffs (bs.map (mul a)) (zero :: rawMul tl bs)) (i' + j₀ + 1) =
      add (mul (coeffAt tl i') (coeffAt bs j₀)) (mul g q)
    rw [coeffAt_rawAddCoeffs, coeffAt_map_mul_left]
    have ha0 : DvdU g a := has 0 (Nat.zero_lt_succ i')
    obtain ⟨qa, hqa⟩ := dvdU_mul_right ha0 (coeffAt bs (i' + j₀ + 1))
    obtain ⟨qtl, hqtl⟩ := rawMul_pivot_congr g bs j₀ hbs i' tl
      (fun i hi => has (i + 1) (Nat.succ_lt_succ hi))
    refine ⟨add qa qtl, ?_⟩
    show add (mul a (coeffAt bs (i' + j₀ + 1))) (coeffAt (rawMul tl bs) (i' + j₀)) = _
    rw [hqa, hqtl]; constructive_ring

private theorem refine_against_list :
    ∀ (cs : List (UPoly E)) (g : UPoly E), 1 ≤ g.natDeg →
      ∃ g' : UPoly E, 1 ≤ g'.natDeg ∧ DvdU g' g ∧
        ∀ c ∈ cs, DvdU g' c ∨ ∃ u v, add (mul u g') (mul v c) = one
  | [], g, hg => ⟨g, hg, ⟨one, (LawfulCommRing.mul_one g).symm⟩, fun _ hc => nomatch hc⟩
  | c :: tl, g, hg => by
    have hgNe : g ≠ zero := fun e => by rw [e] at hg; exact Nat.not_succ_le_zero 0 hg
    rcases UPoly.d5_split g c hgNe with ⟨u, v, hbez⟩ | ⟨t, ht⟩ | ⟨g₁, q₁, hsplit, hg₁pos, _, _, t, ht⟩
    · obtain ⟨g', hg'deg, hg'dvd, htl⟩ := refine_against_list tl g hg
      refine ⟨g', hg'deg, hg'dvd, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hxtl
      · obtain ⟨s, rfl⟩ := hg'dvd
        exact .inr ⟨mul u s, v, by rw [← hbez]; constructive_ring⟩
      · exact htl x hxtl
    · obtain ⟨g', hg'deg, hg'dvd, htl⟩ := refine_against_list tl g hg
      refine ⟨g', hg'deg, hg'dvd, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hxtl
      · exact .inl (dvdU_trans hg'dvd ⟨t, ht⟩)
      · exact htl x hxtl
    · obtain ⟨g', hg'deg, hg'dvd, htl⟩ := refine_against_list tl g₁ hg₁pos
      have hg'g : DvdU g' g := dvdU_trans hg'dvd ⟨q₁, hsplit⟩
      refine ⟨g', hg'deg, hg'g, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hxtl
      · exact .inl (dvdU_trans hg'dvd ⟨t, ht⟩)
      · exact htl x hxtl

private theorem coeffAt_mem_or_zero :
    ∀ (cs : List (UPoly E)) (k : Nat), coeffAt cs k ∈ cs ∨ coeffAt cs k = zero
  | [], k => .inr (coeffAt_nil k)
  | _ :: _, 0 => .inl (.head _)
  | _ :: tl, k + 1 => (coeffAt_mem_or_zero tl k).elim (fun h => .inl (.tail _ h)) .inr

private theorem find_min_non_dvd (g : UPoly E) (A : Poly2 E) (hPrim : IsPrimY A)
    (hg : 1 ≤ g.natDeg)
    (hDich : ∀ c ∈ A.coeffs, DvdU g c ∨ ∃ u v, add (mul u g) (mul v c) = one) :
    ∃ i₀, (∀ i < i₀, DvdU g (coeffAt A.coeffs i)) ∧
      ∃ u v, add (mul u g) (mul v (coeffAt A.coeffs i₀)) = one := by
  have hDec : ∀ k, DvdU g (coeffAt A.coeffs k) ∨
      ∃ u v, add (mul u g) (mul v (coeffAt A.coeffs k)) = one := fun k => by
    rcases coeffAt_mem_or_zero A.coeffs k with hm | hz
    · exact hDich _ hm
    · rw [hz]; exact .inl (dvdU_zero g)
  have hNotAll : ¬ ∀ k, k ≤ A.coeffs.length → DvdU g (coeffAt A.coeffs k) := fun hall => by
    have hAllK : ∀ k, DvdU g (coeffAt A.coeffs k) := fun k =>
      if hk : k ≤ A.coeffs.length then hall k hk
      else by rw [coeffAt_eq_zero_of_ge A.coeffs k (by omega)]; exact dvdU_zero g
    have hd0 := hPrim.2 g hAllK
    omega
  have hStep : ∀ N : Nat,
      (∀ k ≤ N, DvdU g (coeffAt A.coeffs k)) ∨
      ∃ i₀ ≤ N, (∀ i < i₀, DvdU g (coeffAt A.coeffs i)) ∧
        ∃ u v, add (mul u g) (mul v (coeffAt A.coeffs i₀)) = one := by
    intro N; induction N with
    | zero =>
      rcases hDec 0 with hd0 | hb0
      · exact .inl (fun k hk => by
          have hk0 : k = 0 := Nat.le_zero.mp hk
          rw [hk0]; exact hd0)
      · exact .inr ⟨0, Nat.le_refl 0, fun _ hi => absurd hi (Nat.not_lt_zero _), hb0⟩
    | succ n ih =>
      rcases ih with hall | ⟨i₀, hi₀, hlt, hb⟩
      · rcases hDec (n + 1) with hdn | hbn
        · exact .inl (fun k hk =>
            if hkn : k ≤ n then hall k hkn
            else by
              have hkeq : k = n + 1 := by omega
              rw [hkeq]; exact hdn)
        · exact .inr ⟨n + 1, Nat.le_refl _, fun i hi => hall i (by omega), hbn⟩
      · exact .inr ⟨i₀, Nat.le_succ_of_le hi₀, hlt, hb⟩
  rcases hStep A.coeffs.length with hall | ⟨i₀, _, hlt, hb⟩
  · exact absurd hall hNotAll
  · exact ⟨i₀, hlt, hb⟩

/-- **Constructive Gauss's Lemma (`isPrimY_mul`)**: the product of two `Y`-primitive bivariate
    polynomials is `Y`-primitive. -/
theorem isPrimY_mul {A B : Poly2 E} (hA : IsPrimY A) (hB : IsPrimY B) :
    IsPrimY (mul A B) := by
  refine ⟨mul_ne_zero' hA.1 hB.1, fun g hg => ?_⟩
  apply Decidable.byContradiction
  intro hPos
  have hgPos : 1 ≤ g.natDeg := by omega
  obtain ⟨g₁, hg₁Pos, hg₁g, hDichA⟩ := refine_against_list A.coeffs g hgPos
  obtain ⟨i₀, hi₀lt, uA, vA, hbezA⟩ := find_min_non_dvd g₁ A hA hg₁Pos hDichA
  obtain ⟨g₂, hg₂Pos, hg₂g₁, hDichB⟩ := refine_against_list B.coeffs g₁ hg₁Pos
  obtain ⟨j₀, hj₀lt, uB, vB, hbezB⟩ := find_min_non_dvd g₂ B hB hg₂Pos hDichB
  have hi₀g₂ : ∀ i < i₀, DvdU g₂ (coeffAt A.coeffs i) :=
    fun i hi => dvdU_trans hg₂g₁ (hi₀lt i hi)
  have ⟨t₁, ht₁⟩ := hg₂g₁
  have hbezA₂ : add (mul (mul uA t₁) g₂) (mul vA (coeffAt A.coeffs i₀)) = one := by
    rw [← hbezA, ht₁]; constructive_ring
  obtain ⟨qConv, hConv⟩ := rawMul_pivot_congr g₂ B.coeffs j₀ hj₀lt i₀ A.coeffs hi₀g₂
  have hMulCoeff : coeffAt (mul A B).coeffs (i₀ + j₀) =
      coeffAt (rawMul A.coeffs B.coeffs) (i₀ + j₀) := coeffAt_trimPoly _ _
  obtain ⟨qAB, hqAB⟩ := dvdU_trans (dvdU_trans hg₂g₁ hg₁g) (hg (i₀ + j₀))
  rw [hMulCoeff, hConv] at hqAB
  have habDvd : mul (coeffAt A.coeffs i₀) (coeffAt B.coeffs j₀) = mul g₂ (sub qAB qConv) := by
    apply LawfulCommRing.add_left_cancel (a := mul g₂ qConv)
    rw [LawfulCommRing.add_comm (mul g₂ qConv), hqAB]; constructive_ring
  let w := add (mul (mul uA t₁) (add (mul uB g₂) (mul vB (coeffAt B.coeffs j₀))))
      (add (mul (mul vA (coeffAt A.coeffs i₀)) uB) (mul (mul vA vB) (sub qAB qConv)))
  have hUnit : mul g₂ w = one := by
    have hProd : mul (add (mul (mul uA t₁) g₂) (mul vA (coeffAt A.coeffs i₀)))
        (add (mul uB g₂) (mul vB (coeffAt B.coeffs j₀))) = one := by
      rw [hbezA₂, hbezB, LawfulCommRing.mul_one]
    have hExp : mul g₂ w =
        add (mul (add (mul (mul uA t₁) g₂) (mul vA (coeffAt A.coeffs i₀)))
          (add (mul uB g₂) (mul vB (coeffAt B.coeffs j₀))))
          (mul (mul vA vB) (sub (mul g₂ (sub qAB qConv))
            (mul (coeffAt A.coeffs i₀) (coeffAt B.coeffs j₀)))) := by
      dsimp [w]; constructive_ring
    rw [hExp, ← habDvd, LawfulCommRing.sub_self, LawfulCommRing.mul_zero,
      LawfulCommRing.add_zero, hProd]
  have hg₂Ne : g₂ ≠ zero := fun e => NontrivialRing.one_ne_zero (by rw [← hUnit, e, LawfulCommRing.zero_mul])
  have hwNe : w ≠ zero := fun e => NontrivialRing.one_ne_zero (by rw [← hUnit, e, LawfulCommRing.mul_zero])
  have hdeg := UPoly.natDeg_mul hg₂Ne hwNe
  rw [hUnit, natDeg_one] at hdeg
  omega

end Field
end Poly2

/-! ## Assurance Witnesses -/

namespace BivariateGaussTests
open UPoly Poly2

private theorem isPrimY_monic_deg1 (c : UPoly Goldilocks) :
    IsPrimY (ofList [c, one] : Poly2 Goldilocks) := by
  have hc1 : coeffAt (ofList [c, one] : Poly2 Goldilocks).coeffs 1 = one := by
    rw [coeffAt_ofList]; rfl
  refine ⟨fun e => NontrivialRing.one_ne_zero (by
    rw [← hc1, e, coeffs_zero, coeffAt_nil]), fun g hg => ?_⟩
  obtain ⟨q, hq⟩ := hg 1
  rw [hc1] at hq
  have hg0 : g ≠ zero := fun e => NontrivialRing.one_ne_zero (by rw [hq, e, LawfulCommRing.zero_mul])
  have hq0 : q ≠ zero := fun e => NontrivialRing.one_ne_zero (by rw [hq, e, LawfulCommRing.mul_zero])
  have hd := UPoly.natDeg_mul hg0 hq0
  rw [← hq, natDeg_one] at hd; omega

/-- Witness that `isPrimY_mul` and `tdeg_mul` are inhabited: `Z + Y` and `Z - Y` are `Y`-primitive
    and their product `Z² - Y²` is `Y`-primitive of total degree `2`. -/
theorem inhabited_isPrimY_mul :
    ∃ A B : Poly2 Goldilocks,
      IsPrimY A ∧ IsPrimY B ∧ IsPrimY (mul A B) ∧ tdeg (mul A B) = 2 := by
  let A : Poly2 Goldilocks := ofList [X, one]
  let B : Poly2 Goldilocks := ofList [neg X, one]
  have hA : IsPrimY A := isPrimY_monic_deg1 X
  have hB : IsPrimY B := isPrimY_monic_deg1 (neg X)
  exact ⟨A, B, hA, hB, isPrimY_mul hA hB, by decide +kernel⟩

/-- `#tooth`: dropping `IsPrimY A` invalidates `isPrimY_mul`: `A = Y · 1` (`C X`) and `B = Z` (`X`)
    satisfy `A ≠ 0 ∧ IsPrimY B`, yet `mul A B = Y · Z` is divisible by `Y` (`natDeg = 1 ≠ 0`). -/
theorem tooth_isPrimY_needs_prim :
    ∃ A B : Poly2 Goldilocks,
      A ≠ zero ∧ IsPrimY B ∧ ¬ IsPrimY (mul A B) := by
  let A : Poly2 Goldilocks := C X
  let B : Poly2 Goldilocks := ofList [zero, one]
  refine ⟨A, B, by decide +kernel, isPrimY_monic_deg1 zero, fun hPrim => ?_⟩
  have hAll : ∀ k, ∃ q : UPoly Goldilocks, coeffAt (mul A B).coeffs k = mul X q := fun k => by
    dsimp [A]
    rw [coeffAt_C_mul]
    exact ⟨coeffAt B.coeffs k, rfl⟩
  have hd0 := hPrim.2 X hAll
  have hd1 : (X : UPoly Goldilocks).natDeg = 1 := by decide +kernel
  omega

#verify_constructive Poly2.tdeg_mul Poly2.tdeg_C Poly2.contY_mul_primY Poly2.isPrimY_mul
#verify_constructive inhabited_isPrimY_mul tooth_isPrimY_needs_prim
#tooth_pair Poly2.isPrimY_mul vs tooth_isPrimY_needs_prim
#verify_inhabited Poly2.isPrimY_mul inhabited_isPrimY_mul

end BivariateGaussTests

end Qsag
end
