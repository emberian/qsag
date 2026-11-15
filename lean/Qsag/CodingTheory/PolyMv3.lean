module
/-
# Qsag.CodingTheory.PolyMv3 — constructive trivariate polynomials `F[X][Y][Z]`

`UPoly R` is the ring of trimmed coefficient lists over a lawful commutative ring with
decidable equality; it is again such a ring, so `Poly3 F := UPoly (UPoly (UPoly F))` is
`F[X][Y][Z]` with `Z` outermost. The file provides the ring and integral-domain structure,
ring homomorphisms and `eval₂`, weighted degrees (`degZ`, `degYZ`, `deg11d`), the affine-line
specialization `Q(X, α + βX, P(X))` with its degree bound, and the Taylor shift with Hasse
derivatives (multiplicativity of the shift is the Leibniz rule).
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
@[expose] def natDeg (p : UPoly R) : Nat := p.coeffs.length - 1

/-- The leading coefficient (`zero` for the zero polynomial). -/
@[expose] def lead (p : UPoly R) : R := coeffAt p.coeffs p.natDeg

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
  have ha : a.natDeg < k := by omega
  have hb : b.natDeg < k := by omega
  rw [coeffAt_add, a.coeffAt_eq_zero_of_natDeg_lt ha, b.coeffAt_eq_zero_of_natDeg_lt hb,
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

/-! ## Ring homomorphisms and evaluation -/

/-- Ring homomorphisms between the project's ring structures. -/
structure RingHom (R S : Type) [CommRingOps R] [CommRingOps S] where
  toFun : R → S
  map_zero : toFun zero = zero
  map_one : toFun one = one
  map_add : ∀ a b, toFun (add a b) = add (toFun a) (toFun b)
  map_mul : ∀ a b, toFun (mul a b) = mul (toFun a) (toFun b)

namespace RingHom
variable {R S T : Type} [LawfulCommRing R] [LawfulCommRing S] [LawfulCommRing T]

theorem map_neg (φ : RingHom R S) (a : R) : φ.toFun (neg a) = neg (φ.toFun a) := by
  apply LawfulCommRing.add_left_cancel (a := φ.toFun a)
  rw [← φ.map_add, LawfulCommRing.add_right_neg, LawfulCommRing.add_right_neg, φ.map_zero]

theorem map_sub (φ : RingHom R S) (a b : R) :
    φ.toFun (sub a b) = sub (φ.toFun a) (φ.toFun b) := by
  rw [LawfulCommRing.sub_eq_add_neg, φ.map_add, φ.map_neg, ← LawfulCommRing.sub_eq_add_neg]

/-- The identity homomorphism. -/
def id (R : Type) [CommRingOps R] : RingHom R R :=
  ⟨fun a => a, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem id_apply (a : R) : (RingHom.id R).toFun a = a := by rfl

/-- Composition `ψ ∘ φ`. -/
def comp (ψ : RingHom S T) (φ : RingHom R S) : RingHom R T where
  toFun a := ψ.toFun (φ.toFun a)
  map_zero := by rw [φ.map_zero, ψ.map_zero]
  map_one := by rw [φ.map_one, ψ.map_one]
  map_add a b := by rw [φ.map_add, ψ.map_add]
  map_mul a b := by rw [φ.map_mul, ψ.map_mul]

theorem comp_apply (ψ : RingHom S T) (φ : RingHom R S) (a : R) :
    (ψ.comp φ).toFun a = ψ.toFun (φ.toFun a) := by rfl

theorem coeffAt_map (φ : RingHom R S) :
    ∀ (l : List R) (k : Nat), coeffAt (l.map φ.toFun) k = φ.toFun (coeffAt l k)
  | [], k => by rw [List.map_nil, coeffAt_nil, coeffAt_nil, φ.map_zero]
  | _ :: _, 0 => by rfl
  | _ :: cs, k + 1 => by
    rw [List.map_cons, coeffAt_cons_succ, coeffAt_cons_succ, coeffAt_map φ cs k]

theorem map_rawAdd (φ : RingHom R S) :
    ∀ a b : List R, (rawAddCoeffs a b).map φ.toFun =
      rawAddCoeffs (a.map φ.toFun) (b.map φ.toFun)
  | [], b => by simp [rawAddCoeffs]
  | c :: cs, [] => by simp [rawAddCoeffs]
  | c :: cs, d :: ds => by simp [rawAddCoeffs, φ.map_add, map_rawAdd φ cs ds]

theorem map_rawMul (φ : RingHom R S) :
    ∀ a b : List R, (rawMul a b).map φ.toFun = rawMul (a.map φ.toFun) (b.map φ.toFun)
  | [], _ => by rfl
  | c :: cs, b => by
    show (rawAddCoeffs (b.map (mul c)) (zero :: rawMul cs b)).map φ.toFun =
      rawAddCoeffs ((b.map φ.toFun).map (mul (φ.toFun c)))
        (zero :: rawMul (cs.map φ.toFun) (b.map φ.toFun))
    rw [map_rawAdd, List.map_cons, φ.map_zero, map_rawMul φ cs b, List.map_map, List.map_map]
    exact congrArg (rawAddCoeffs · _) (List.map_congr_left fun x _ => φ.map_mul c x)

theorem map_evalCoeffs (φ : RingHom R S) (x : R) :
    ∀ l : List R, φ.toFun (evalCoeffs l x) = evalCoeffs (l.map φ.toFun) (φ.toFun x)
  | [] => φ.map_zero
  | c :: cs => by
    show φ.toFun (add c (mul x (evalCoeffs cs x))) =
      add (φ.toFun c) (mul (φ.toFun x) (evalCoeffs (cs.map φ.toFun) (φ.toFun x)))
    rw [φ.map_add, φ.map_mul, map_evalCoeffs φ x cs]

end RingHom

namespace UPoly
section Eval
variable {R S T : Type} [LawfulCommRing R] [DecidableEq R] [LawfulCommRing S] [LawfulCommRing T]

theorem evalCoeffs_map_trimPoly (φ : RingHom R S) (s : S) :
    ∀ l : List R, evalCoeffs ((trimPoly l).map φ.toFun) s = evalCoeffs (l.map φ.toFun) s
  | [] => by rfl
  | c :: cs => by
    have ih := evalCoeffs_map_trimPoly φ s cs
    simp only [trimPoly]
    split
    · next h =>
      rw [h.1] at ih
      show zero = add (φ.toFun c) (mul s (evalCoeffs (cs.map φ.toFun) s))
      rw [← ih, h.2, φ.map_zero]
      show zero = add zero (mul s zero)
      rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    · show add (φ.toFun c) (mul s (evalCoeffs ((trimPoly cs).map φ.toFun) s)) =
        add (φ.toFun c) (mul s (evalCoeffs (cs.map φ.toFun) s))
      rw [ih]

/-- Evaluate at `s : S` after pushing coefficients through `φ`. -/
@[expose] def eval₂ (φ : RingHom R S) (s : S) (p : UPoly R) : S := evalCoeffs (p.coeffs.map φ.toFun) s

theorem eval₂_ofList (φ : RingHom R S) (s : S) (l : List R) :
    eval₂ φ s (ofList l) = evalCoeffs (l.map φ.toFun) s := evalCoeffs_map_trimPoly φ s l

theorem eval₂_zero (φ : RingHom R S) (s : S) : eval₂ φ s zero = zero := by rfl
theorem eval₂_add (φ : RingHom R S) (s : S) (a b : UPoly R) :
    eval₂ φ s (add a b) = add (eval₂ φ s a) (eval₂ φ s b) := by
  show evalCoeffs ((trimPoly (rawAddCoeffs a.coeffs b.coeffs)).map φ.toFun) s = _
  rw [evalCoeffs_map_trimPoly, RingHom.map_rawAdd, evalCoeffs_rawAdd]; rfl

theorem eval₂_mul (φ : RingHom R S) (s : S) (a b : UPoly R) :
    eval₂ φ s (mul a b) = mul (eval₂ φ s a) (eval₂ φ s b) := by
  show evalCoeffs ((trimPoly (rawMul a.coeffs b.coeffs)).map φ.toFun) s = _
  rw [evalCoeffs_map_trimPoly, RingHom.map_rawMul, evalCoeffs_rawMul]; rfl

/-- Constant polynomials. -/
@[expose] def C (c : R) : UPoly R := ofList [c]

/-- The variable. -/
@[expose] def X : UPoly R := ofList [zero, one]

theorem eval₂_C (φ : RingHom R S) (s : S) (c : R) : eval₂ φ s (C c) = φ.toFun c := by
  show eval₂ φ s (ofList [c]) = _; rw [eval₂_ofList]
  show add (φ.toFun c) (mul s zero) = _; rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

theorem eval₂_X (φ : RingHom R S) (s : S) : eval₂ φ s (X : UPoly R) = s := by
  show eval₂ φ s (ofList [zero, one]) = _; rw [eval₂_ofList]
  show add (φ.toFun zero) (mul s (add (φ.toFun one) (mul s zero))) = s
  rw [φ.map_zero, φ.map_one, LawfulCommRing.mul_zero, LawfulCommRing.add_zero,
    LawfulCommRing.mul_one, LawfulCommRing.zero_add]

theorem one_eq_C : (one : UPoly R) = C one := by rfl

/-- `eval₂ φ s` as a ring homomorphism. -/
def eval₂Hom (φ : RingHom R S) (s : S) : RingHom (UPoly R) S where
  toFun := eval₂ φ s
  map_zero := eval₂_zero φ s
  map_one := by rw [one_eq_C, eval₂_C, φ.map_one]
  map_add := eval₂_add φ s
  map_mul := eval₂_mul φ s

theorem eval₂Hom_apply (φ : RingHom R S) (s : S) (p : UPoly R) :
    (eval₂Hom φ s).toFun p = eval₂ φ s p := by rfl

/-- Homomorphisms commute with `eval₂`. -/
theorem hom_eval₂ (ψ : RingHom S T) (φ : RingHom R S) (s : S) (p : UPoly R) :
    ψ.toFun (eval₂ φ s p) = eval₂ (ψ.comp φ) (ψ.toFun s) p := by
  show ψ.toFun (evalCoeffs (p.coeffs.map φ.toFun) s) = _
  rw [RingHom.map_evalCoeffs, List.map_map]; rfl

/-- Plain evaluation at a point of the coefficient ring. -/
@[expose] def eval (p : UPoly R) (x : R) : R := eval₂ (RingHom.id R) x p

theorem eval_eq (p : UPoly R) (x : R) : p.eval x = evalCoeffs p.coeffs x := by
  show evalCoeffs (p.coeffs.map (fun a => a)) x = _; rw [List.map_id']

/-- Evaluation at `x` as a ring homomorphism. -/
def evalHom (x : R) : RingHom (UPoly R) R := eval₂Hom (RingHom.id R) x

theorem evalHom_apply (x : R) (p : UPoly R) : (evalHom x).toFun p = p.eval x := by rfl
theorem eval_C (c x : R) : (C c).eval x = c := eval₂_C _ _ _
theorem eval_X (x : R) : (X : UPoly R).eval x = x := eval₂_X _ _
theorem coeffAt_C_zero (c : R) : coeffAt (C c).coeffs 0 = c := by
  show coeffAt (ofList [c]).coeffs 0 = _; rw [coeffAt_ofList]; rfl
theorem coeffAt_C_succ (c : R) (k : Nat) : coeffAt (C c).coeffs (k + 1) = zero := by
  show coeffAt (ofList [c]).coeffs (k + 1) = _
  rw [coeffAt_ofList, coeffAt_cons_succ, coeffAt_nil]

omit [DecidableEq R] in
private theorem coeffAt_zero_cons_nil (l : List R) : ∀ k : Nat,
    coeffAt (zero :: rawMul ([] : List R) l) k = zero
  | 0 => rfl
  | k + 1 => by rw [coeffAt_cons_succ]; exact coeffAt_nil k

theorem coeffAt_C_mul (c : R) (q : UPoly R) (k : Nat) :
    coeffAt (mul (C c) q).coeffs k = mul c (coeffAt q.coeffs k) := by
  show coeffAt (pMul (trimPoly [c]) q.coeffs) k = _
  rw [pMul_trimPoly_left]
  show coeffAt (trimPoly (rawAddCoeffs (q.coeffs.map (mul c)) (zero :: rawMul [] q.coeffs))) k = _
  rw [coeffAt_trimPoly, coeffAt_addCoeffs, coeffAt_map_mul, coeffAt_zero_cons_nil,
    LawfulCommRing.add_zero]

theorem coeffAt_X_mul_zero (q : UPoly R) : coeffAt (mul X q).coeffs 0 = zero := by
  show coeffAt (pMul (trimPoly [zero, one]) q.coeffs) 0 = _
  rw [pMul_trimPoly_left]
  show coeffAt (trimPoly (rawAddCoeffs (q.coeffs.map (mul zero))
    (zero :: rawMul [one] q.coeffs))) 0 = _
  rw [coeffAt_trimPoly, coeffAt_addCoeffs, coeffAt_map_mul, LawfulCommRing.zero_mul,
    coeffAt_cons_zero, LawfulCommRing.add_zero]

theorem coeffAt_X_mul_succ (q : UPoly R) (k : Nat) :
    coeffAt (mul X q).coeffs (k + 1) = coeffAt q.coeffs k := by
  show coeffAt (pMul (trimPoly [zero, one]) q.coeffs) (k + 1) = _
  rw [pMul_trimPoly_left]
  show coeffAt (trimPoly (rawAddCoeffs (q.coeffs.map (mul zero))
    (zero :: rawAddCoeffs (q.coeffs.map (mul one)) (zero :: rawMul [] q.coeffs)))) (k + 1) = _
  rw [coeffAt_trimPoly, coeffAt_addCoeffs, coeffAt_map_mul, LawfulCommRing.zero_mul,
    coeffAt_cons_succ, coeffAt_addCoeffs, coeffAt_map_mul, LawfulCommRing.one_mul,
    LawfulCommRing.zero_add, coeffAt_zero_cons_nil, LawfulCommRing.add_zero]

/-- Horner decomposition of a coefficient list. -/
theorem ofList_cons (c : R) (l : List R) :
    ofList (c :: l) = add (C c) (mul X (ofList l)) := by
  apply ext_coeffAt; intro k
  rw [coeffAt_ofList, coeffAt_add]
  cases k with
  | zero => rw [coeffAt_X_mul_zero, coeffAt_C_zero, coeffAt_cons_zero, LawfulCommRing.add_zero]
  | succ k =>
    rw [coeffAt_X_mul_succ, coeffAt_C_succ, coeffAt_cons_succ, coeffAt_ofList,
      LawfulCommRing.zero_add]

theorem ofList_coeffs (p : UPoly R) : ofList p.coeffs = p := ext p.trimmed

/-- `C` as a ring homomorphism. -/
def CHom : RingHom R (UPoly R) where
  toFun := C
  map_zero := ext_coeffAt fun k => by
    rw [coeffs_zero, coeffAt_nil]
    cases k <;> first | exact coeffAt_C_zero _ | exact coeffAt_C_succ _ _
  map_one := by rfl
  map_add a b := ext_coeffAt fun k => by
    rw [coeffAt_add]
    cases k with
    | zero => rw [coeffAt_C_zero, coeffAt_C_zero, coeffAt_C_zero]
    | succ k => rw [coeffAt_C_succ, coeffAt_C_succ, coeffAt_C_succ, LawfulCommRing.add_zero]
  map_mul a b := ext_coeffAt fun k => by
    rw [coeffAt_C_mul]
    cases k with
    | zero => rw [coeffAt_C_zero, coeffAt_C_zero]
    | succ k => rw [coeffAt_C_succ, coeffAt_C_succ, LawfulCommRing.mul_zero]

theorem CHom_apply (c : R) : (CHom (R := R)).toFun c = C c := by rfl

end Eval
end UPoly

/-! ## Weighted degrees -/

section Degree
variable {R S : Type} [LawfulCommRing R] [DecidableEq R] [LawfulCommRing S] [DecidableEq S]

omit [DecidableEq R] in
/-- The filtration lemma for products: if the coefficients of `a` and `b` lie in families
    `M` and `N` with `M i · N j ⊆ L (i + j)`, the coefficients of `a * b` lie in `L`. -/
theorem coeffAt_rawMul_graded (N : Nat → R → Prop) (b : List R) (hN : ∀ j, N j (coeffAt b j)) :
    ∀ (a : List R) (L M : Nat → R → Prop), (∀ k, L k zero) →
      (∀ k x y, L k x → L k y → L k (add x y)) →
      (∀ i j x y, M i x → N j y → L (i + j) (mul x y)) →
      (∀ i, M i (coeffAt a i)) → ∀ k, L k (coeffAt (rawMul a b) k)
  | [], L, _, hz, _, _, _, k => by
    show L k (coeffAt [] k); rw [coeffAt_nil]; exact hz k
  | c :: cs, L, M, hz, hadd, hmul, hM, k => by
    show L k (coeffAt (rawAddCoeffs (b.map (mul c)) (zero :: rawMul cs b)) k)
    rw [coeffAt_addCoeffs, coeffAt_map_mul]
    apply hadd
    · have := hmul 0 k c _ (hM 0) (hN k)
      rwa [Nat.zero_add] at this
    · cases k with
      | zero => exact hz 0
      | succ k =>
        rw [coeffAt_cons_succ]
        exact coeffAt_rawMul_graded N b hN cs (fun k => L (k + 1)) (fun i => M (i + 1))
          (fun k => hz _) (fun k => hadd _)
          (fun i j x y hx hy => by
            have := hmul (i + 1) j x y hx hy
            rwa [Nat.add_right_comm] at this)
          (fun i => hM (i + 1)) k

/-- A degree-like function: zero at zero, ultrametric on sums, subadditive on products. -/
structure DegFn (w : R → Nat) : Prop where
  zero : w zero = 0
  add_le : ∀ x y, w (add x y) ≤ max (w x) (w y)
  mul_le : ∀ x y, w (mul x y) ≤ w x + w y
  neg_le : ∀ x, w (neg x) ≤ w x

namespace UPoly

/-- `max` of `w c + s * k` over the nonzero coefficients `c` at index `k`, from offset `o`. -/
def wdegFrom (w : R → Nat) (s : Nat) : Nat → List R → Nat
  | _, [] => 0
  | o, c :: cs => max (if c = zero then 0 else w c + s * o) (wdegFrom w s (o + 1) cs)

/-- Weighted degree: coefficients are measured by `w`, the variable has weight `s`. -/
@[expose] def wdeg (w : R → Nat) (s : Nat) (p : UPoly R) : Nat := wdegFrom w s 0 p.coeffs

theorem le_wdegFrom (w : R → Nat) (s : Nat) : ∀ (o : Nat) (l : List R) (k : Nat),
    coeffAt l k ≠ zero → w (coeffAt l k) + s * (o + k) ≤ wdegFrom w s o l
  | _, [], k, h => absurd (coeffAt_nil k) h
  | o, c :: cs, 0, h => by
    rw [coeffAt_cons_zero] at h ⊢
    unfold wdegFrom
    simp only [h, ↓reduceIte, Nat.add_zero]
    exact Nat.le_max_left _ _
  | o, c :: cs, k + 1, h => by
    rw [coeffAt_cons_succ] at h ⊢
    have ih := le_wdegFrom w s (o + 1) cs k h
    unfold wdegFrom
    have e : o + (k + 1) = o + 1 + k := by omega
    rw [e]
    exact Nat.le_trans ih (Nat.le_max_right _ _)

theorem wdegFrom_le (w : R → Nat) (s : Nat) : ∀ (o : Nat) (l : List R) (B : Nat),
    (∀ k, coeffAt l k ≠ zero → w (coeffAt l k) + s * (o + k) ≤ B) → wdegFrom w s o l ≤ B
  | _, [], _, _ => Nat.zero_le _
  | o, c :: cs, B, h => by
    unfold wdegFrom
    apply Nat.max_le.mpr
    constructor
    · split
      · exact Nat.zero_le _
      · next hc => exact h 0 hc
    · apply wdegFrom_le w s (o + 1) cs B
      intro k hk
      have := h (k + 1) hk
      rw [coeffAt_cons_succ] at this
      have e : o + (k + 1) = o + 1 + k := by omega
      rwa [e] at this

theorem le_wdeg (w : R → Nat) (s : Nat) (p : UPoly R) (k : Nat)
    (h : coeffAt p.coeffs k ≠ zero) : w (coeffAt p.coeffs k) + s * k ≤ p.wdeg w s := by
  have := le_wdegFrom w s 0 p.coeffs k h
  rwa [Nat.zero_add] at this

theorem wdeg_le (w : R → Nat) (s : Nat) (p : UPoly R) (B : Nat)
    (h : ∀ k, coeffAt p.coeffs k ≠ zero → w (coeffAt p.coeffs k) + s * k ≤ B) :
    p.wdeg w s ≤ B :=
  wdegFrom_le w s 0 p.coeffs B (fun k hk => by rw [Nat.zero_add]; exact h k hk)

theorem bnd_add {w : R → Nat} (hw : DegFn w) {c : Nat} {B : Nat} {x y : R}
    (hx : x ≠ zero → w x + c ≤ B) (hy : y ≠ zero → w y + c ≤ B) (h : add x y ≠ zero) :
    w (add x y) + c ≤ B := by
  if hx0 : x = zero then
    subst hx0; rw [LawfulCommRing.zero_add] at h ⊢; exact hy h
  else if hy0 : y = zero then
    subst hy0; rw [LawfulCommRing.add_zero] at h ⊢; exact hx h
  else
    have := hw.add_le x y; have := hx hx0; have := hy hy0; omega

/-- A degree function on `R` lifts to the weighted degree on `UPoly R`. -/
theorem degFn_wdeg {w : R → Nat} (hw : DegFn w) (s : Nat) :
    DegFn (fun p : UPoly R => p.wdeg w s) where
  zero := by rfl
  add_le a b := by
    apply wdeg_le
    intro k hk
    rw [coeffAt_add] at hk ⊢
    have ha := le_wdeg w s a k
    have hb := le_wdeg w s b k
    exact bnd_add hw (B := max (a.wdeg w s) (b.wdeg w s)) (fun h => by have := ha h; omega)
      (fun h => by have := hb h; omega) hk
  neg_le a := by
    apply wdeg_le
    intro k hk
    rw [coeffAt_neg] at hk ⊢
    have hne : coeffAt a.coeffs k ≠ zero := fun e => hk (by rw [e, LawfulCommRing.neg_zero])
    have := le_wdeg w s a k hne; have := hw.neg_le (coeffAt a.coeffs k); omega
  mul_le a b := by
    apply wdeg_le
    intro k
    have e : coeffAt (mul a b).coeffs k = coeffAt (rawMul a.coeffs b.coeffs) k :=
      coeffAt_trimPoly _ k
    rw [e]
    exact coeffAt_rawMul_graded (fun j y => y ≠ zero → w y + s * j ≤ b.wdeg w s) b.coeffs
      (le_wdeg w s b) a.coeffs (fun k x => x ≠ zero → w x + s * k ≤ a.wdeg w s + b.wdeg w s)
      (fun i x => x ≠ zero → w x + s * i ≤ a.wdeg w s) (fun _ h => absurd rfl h)
      (fun _ _ _ hx hy h => bnd_add hw hx hy h)
      (fun i j x y hx hy h => by
        have hx0 : x ≠ zero := fun e => h (by rw [e, LawfulCommRing.zero_mul])
        have hy0 : y ≠ zero := fun e => h (by rw [e, LawfulCommRing.mul_zero])
        have := hx hx0; have := hy hy0; have := hw.mul_le x y
        rw [Nat.mul_add]; omega)
      (le_wdeg w s a) k

theorem degFn_natDeg : DegFn (natDeg : UPoly R → Nat) where
  zero := by rfl
  add_le := natDeg_add_le
  mul_le := natDeg_mul_le
  neg_le a := natDeg_le_of_coeffAt _ _ (fun k hk => by
    rw [coeffAt_neg, a.coeffAt_eq_zero_of_natDeg_lt hk, LawfulCommRing.neg_zero])

omit [DecidableEq S] in
theorem evalCoeffs_eq_zero_of_coeffAt (s : S) : ∀ l : List S,
    (∀ k, coeffAt l k = zero) → evalCoeffs l s = zero
  | [], _ => rfl
  | c :: cs, h => by
    show add c (mul s (evalCoeffs cs s)) = zero
    rw [evalCoeffs_eq_zero_of_coeffAt s cs (fun k => h (k + 1)), show c = zero from h 0,
      LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

/-- Horner degree bound: evaluating at a point of degree at most `t`. -/
theorem degFn_evalCoeffs_le {δ : S → Nat} (hδ : DegFn δ) (s : S) (t : Nat) (hs : δ s ≤ t) :
    ∀ (l : List S) (B : Nat), (∀ k, coeffAt l k ≠ zero → δ (coeffAt l k) + t * k ≤ B) →
      δ (evalCoeffs l s) ≤ B
  | [], _, _ => by show δ zero ≤ _; rw [hδ.zero]; exact Nat.zero_le _
  | c :: cs, B, h => by
    show δ (add c (mul s (evalCoeffs cs s))) ≤ B
    have hc : δ c ≤ B := by
      if hc0 : c = zero then rw [hc0, hδ.zero]; exact Nat.zero_le _
      else have := h 0 hc0; rw [coeffAt_cons_zero] at this; omega
    have hrest : δ (mul s (evalCoeffs cs s)) ≤ B := by
      if htB : t ≤ B then
        have ih := degFn_evalCoeffs_le hδ s t hs cs (B - t) (fun k hk => by
          have := h (k + 1) hk
          rw [coeffAt_cons_succ, Nat.mul_succ] at this; omega)
        have := hδ.mul_le s (evalCoeffs cs s); omega
      else
        have hall : ∀ k, coeffAt cs k = zero := fun k => Decidable.byContradiction fun hk => by
          have := h (k + 1) hk
          rw [coeffAt_cons_succ, Nat.mul_succ] at this; omega
        rw [evalCoeffs_eq_zero_of_coeffAt s cs hall, LawfulCommRing.mul_zero, hδ.zero]
        exact Nat.zero_le _
    have := hδ.add_le c (mul s (evalCoeffs cs s)); omega

/-- Degree of `eval₂ φ s p` against the weighted degree of `p`. -/
theorem degFn_eval₂_le {δ : S → Nat} (hδ : DegFn δ) (φ : RingHom R S) (w : R → Nat)
    (hw : ∀ c, δ (φ.toFun c) ≤ w c) (s : S) (t : Nat) (hs : δ s ≤ t) (p : UPoly R) :
    δ (eval₂ φ s p) ≤ p.wdeg w t := by
  apply degFn_evalCoeffs_le hδ s t hs
  intro k hk
  rw [RingHom.coeffAt_map] at hk ⊢
  have hne : coeffAt p.coeffs k ≠ zero := fun e => hk (by rw [e, φ.map_zero])
  have := le_wdeg w t p k hne; have := hw (coeffAt p.coeffs k); omega

end UPoly
end Degree

/-! ## Taylor shift and Hasse derivatives -/

namespace RingHom
variable {S T : Type} [LawfulCommRing S] [LawfulCommRing T]

/-- The Horner–Hasse recursion commutes with ring homomorphisms. -/
theorem map_gsUniHasse (ψ : RingHom S T) : ∀ (l : List S) (k : Nat) (s : S),
    ψ.toFun (gsUniHasse l k s) = gsUniHasse (l.map ψ.toFun) k (ψ.toFun s)
  | [], _, _ => ψ.map_zero
  | c :: cs, 0, s => by
    show ψ.toFun (add c (mul s (gsUniHasse cs 0 s))) = add (ψ.toFun c)
      (mul (ψ.toFun s) (gsUniHasse (cs.map ψ.toFun) 0 (ψ.toFun s)))
    rw [ψ.map_add, ψ.map_mul, map_gsUniHasse ψ cs 0 s]
  | c :: cs, k + 1, s => by
    show ψ.toFun (add (gsUniHasse cs k s) (mul s (gsUniHasse cs (k + 1) s))) =
      add (gsUniHasse (cs.map ψ.toFun) k (ψ.toFun s))
        (mul (ψ.toFun s) (gsUniHasse (cs.map ψ.toFun) (k + 1) (ψ.toFun s)))
    rw [ψ.map_add, ψ.map_mul, map_gsUniHasse ψ cs k s, map_gsUniHasse ψ cs (k + 1) s]

end RingHom

namespace UPoly
section Taylor
variable {R : Type} [LawfulCommRing R] [DecidableEq R]

/-- The Taylor shift `p ↦ p(b + W)`. It is a ring homomorphism: multiplicativity is the
    Leibniz rule for Hasse derivatives in generating-function form. -/
def taylorShift (b : R) : RingHom (UPoly R) (UPoly R) := eval₂Hom CHom (add (C b) X)

/-- The `k`-th Hasse derivative as a polynomial: the Horner–Hasse recursion `gsUniHasse`
    run at the generic point `X` of `R[X]`. -/
@[expose] def hasse (k : Nat) (p : UPoly R) : UPoly R := gsUniHasse (p.coeffs.map C) k X

private theorem map_eval_C (x : R) : ∀ l : List R, l.map (fun c => (C c).eval x) = l
  | [] => rfl
  | c :: cs => by rw [List.map_cons, map_eval_C x cs, eval_C]

/-- Evaluating the Hasse derivative recovers the pointwise recursion; by
    `gsUniHasse_eq_dotVec` this is the binomial formula `Σ C(i, k) pᵢ b^(i-k)`. -/
theorem eval_hasse (k : Nat) (p : UPoly R) (b : R) :
    (hasse k p).eval b = gsUniHasse p.coeffs k b := by
  show (evalHom b).toFun (gsUniHasse (p.coeffs.map C) k X) = _
  rw [RingHom.map_gsUniHasse, List.map_map]
  show gsUniHasse (p.coeffs.map (fun c => (C c).eval b)) k (X.eval b) = _
  rw [map_eval_C, eval_X]

/-- Shift rule: `(taylorShift b p)(w) = p(b + w)`. -/
theorem eval_taylorShift (b w : R) (p : UPoly R) :
    ((taylorShift b).toFun p).eval w = p.eval (add b w) := by
  show (evalHom w).toFun (eval₂ CHom (add (C b) X) p) = _
  rw [hom_eval₂, (evalHom w).map_add]
  show evalCoeffs (p.coeffs.map (fun c => (C c).eval w)) (add ((C b).eval w) (X.eval w)) = _
  rw [map_eval_C, eval_C, eval_X, eval_eq]

private theorem coeffAt_shift_list (b : R) : ∀ (l : List R) (k : Nat),
    coeffAt (evalCoeffs (l.map C) (add (C b) X)).coeffs k = gsUniHasse l k b
  | [], k => by show coeffAt (zero : UPoly R).coeffs k = zero; rw [coeffs_zero, coeffAt_nil]
  | c :: cs, k => by
    show coeffAt (add (C c) (mul (add (C b) X) (evalCoeffs (cs.map C) (add (C b) X)))).coeffs k
      = _
    rw [coeffAt_add, LawfulCommRing.right_distrib, coeffAt_add, coeffAt_C_mul]
    cases k with
    | zero =>
      rw [coeffAt_X_mul_zero, coeffAt_C_zero, coeffAt_shift_list b cs 0,
        LawfulCommRing.add_zero]; rfl
    | succ k =>
      rw [coeffAt_X_mul_succ, coeffAt_C_succ, coeffAt_shift_list b cs (k + 1),
        coeffAt_shift_list b cs k]
      show add zero (add (mul b (gsUniHasse cs (k + 1) b)) (gsUniHasse cs k b)) =
        add (gsUniHasse cs k b) (mul b (gsUniHasse cs (k + 1) b))
      rw [LawfulCommRing.zero_add, LawfulCommRing.add_comm]

/-- Taylor's formula: the coefficient of `W^k` in `p(b + W)` is the `k`-th Hasse derivative
    of `p` at `b`. -/
theorem coeffAt_taylorShift (b : R) (p : UPoly R) (k : Nat) :
    coeffAt ((taylorShift b).toFun p).coeffs k = (hasse k p).eval b :=
  (coeffAt_shift_list b p.coeffs k).trans (eval_hasse k p b).symm

end Taylor
end UPoly

/-! ## Trivariate polynomials -/

/-- `F[X][Y][Z]`, with `Z` the outermost variable. -/
abbrev Poly3 (F : Type) [LawfulCommRing F] [DecidableEq F] := UPoly (UPoly (UPoly F))

namespace Poly3
variable {F : Type} [LawfulCommRing F] [DecidableEq F]

/-- Degree in `Z`. -/
@[expose] def degZ (Q : Poly3 F) : Nat := Q.natDeg

/-- Total degree in `(Y, Z)`. -/
@[expose] def degYZ (Q : Poly3 F) : Nat := Q.wdeg UPoly.natDeg 1

/-- The `(1, 1, d)`-weighted degree in `(X, Y, Z)`. -/
@[expose] def deg11d (d : Nat) (Q : Poly3 F) : Nat := Q.wdeg (fun q => q.wdeg UPoly.natDeg 1) d

/-- The line `α + βX`. -/
@[expose] def line (α β : F) : UPoly F := UPoly.ofList [α, β]

theorem natDeg_line_le (α β : F) : (line α β).natDeg ≤ 1 := by
  have := trimPoly_length_le [α, β]
  show (trimPoly [α, β]).length - 1 ≤ 1
  simp only [List.length_cons, List.length_nil] at this; omega

/-- Specialization to the affine line: `Q(X, α + βX, P(X))`, as a ring homomorphism. -/
def affineLineHom (α β : F) (P : UPoly F) : RingHom (Poly3 F) (UPoly F) :=
  UPoly.eval₂Hom (UPoly.evalHom (line α β)) P

/-- `Q(X, α + βX, P(X))`. -/
def evalAffineLine (Q : Poly3 F) (α β : F) (P : UPoly F) : UPoly F :=
  (affineLineHom α β P).toFun Q

theorem evalAffineLine_mul (Q₁ Q₂ : Poly3 F) (α β : F) (P : UPoly F) :
    evalAffineLine (mul Q₁ Q₂) α β P = mul (evalAffineLine Q₁ α β P) (evalAffineLine Q₂ α β P) :=
  (affineLineHom α β P).map_mul Q₁ Q₂

theorem evalAffineLine_add (Q₁ Q₂ : Poly3 F) (α β : F) (P : UPoly F) :
    evalAffineLine (add Q₁ Q₂) α β P = add (evalAffineLine Q₁ α β P) (evalAffineLine Q₂ α β P) :=
  (affineLineHom α β P).map_add Q₁ Q₂

/-- A polynomial constant in `Z` is evaluated on the line alone. -/
theorem evalAffineLine_C (G : UPoly (UPoly F)) (α β : F) (P : UPoly F) :
    evalAffineLine (UPoly.C G) α β P = G.eval (line α β) := UPoly.eval₂_C _ _ _

/-- Substituting a line for `Y` and a polynomial of degree at most `d` for `Z` produces a
    polynomial of degree at most the `(1, 1, d)`-weighted degree. -/
theorem deg_evalAffineLine_le (Q : Poly3 F) (α β : F) (P : UPoly F) (d : Nat)
    (hP : P.natDeg ≤ d) : (evalAffineLine Q α β P).natDeg ≤ Q.deg11d d :=
  UPoly.degFn_eval₂_le UPoly.degFn_natDeg _ _
    (fun q => UPoly.degFn_eval₂_le UPoly.degFn_natDeg (RingHom.id _) UPoly.natDeg
      (fun _ => Nat.le_refl _) (line α β) 1 (natDeg_line_le α β) q) P d hP Q

/-- Formal derivative in `Z`, of Hasse order `s`. -/
def hasseZ (s : Nat) (Q : Poly3 F) : Poly3 F := UPoly.hasse s Q

/-- Mixed Hasse derivative `∂_X^(r) ∂_Z^(s)`: differentiate the innermost coefficients in
    `X`, then the outer polynomial in `Z`. -/
def hasseXZ (r s : Nat) (Q : Poly3 F) : Poly3 F :=
  UPoly.hasse s (UPoly.ofList (Q.coeffs.map fun q => UPoly.ofList (q.coeffs.map (UPoly.hasse r))))

end Poly3

/-! ## Witnesses -/

namespace Poly3.Tests
open UPoly

def g (n : Nat) : Goldilocks := Goldilocks.ofNat n

/-- `Q = Z` in `Goldilocks[X][Y][Z]`, and `P = X²`. -/
def qZ : Poly3 Goldilocks := X
def pSq : UPoly Goldilocks := ofList [g 0, g 0, g 1]

/-- The hypothesis of `deg_evalAffineLine_le` is satisfiable with the bound attained:
    `Q = Z`, `P = X²` gives degree exactly `2 = deg11d 2 Q`. -/
theorem inhabited_deg_evalAffineLine :
    ∃ (Q : Poly3 Goldilocks) (P : UPoly Goldilocks) (d : Nat), P.natDeg ≤ d ∧
      (Q.evalAffineLine (g 3) (g 5) P).natDeg = 2 ∧ Q.deg11d d = 2 :=
  ⟨qZ, pSq, 2, by decide, by decide, by decide⟩

/-- The `Z`-weight cannot be lowered below `deg P`: with weight `1` the bound fails. -/
theorem tooth_deg_evalAffineLine_weight :
    ∃ (Q : Poly3 Goldilocks) (P : UPoly Goldilocks), P.natDeg ≤ 2 ∧
      ¬ (Q.evalAffineLine (g 3) (g 5) P).natDeg ≤ Q.deg11d 1 :=
  ⟨qZ, pSq, by decide, by decide⟩

/-- Taylor's formula on a concrete cubic: `p = 1 + 2X + 3X² + 4X³` at `b = 5` has first
    Hasse derivative `2 + 6·5 + 12·25 = 332`. -/
theorem taylor_cubic_example :
    coeffAt ((taylorShift (g 5)).toFun (ofList [g 1, g 2, g 3, g 4])).coeffs 1 = g 332 ∧
      (hasse 1 (ofList [g 1, g 2, g 3, g 4])).coeffs = [g 2, g 6, g 12] := by
  decide

#verify_constructive deg_evalAffineLine_le UPoly.coeffAt_taylorShift UPoly.eval_taylorShift
#verify_constructive UPoly.degFn_wdeg UPoly.natDeg_mul UPoly.eval_hasse taylor_cubic_example
#tooth_pair deg_evalAffineLine_le vs tooth_deg_evalAffineLine_weight
#verify_inhabited deg_evalAffineLine_le inhabited_deg_evalAffineLine

end Poly3.Tests

end Qsag
end
