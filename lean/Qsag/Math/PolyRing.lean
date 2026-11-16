module
public import Qsag.Math.CoeffPoly

/-!
# Qsag.Math.PolyRing

Polynomial rings as rings, and the linear algebra over them.

* `UPoly R` (trimmed coefficient lists) as a `LawfulCommRing`, degrees and leading coefficients,
  ring homomorphisms `RingHom`, evaluation `eval₂` / `eval`, weighted degrees `wdeg`, Taylor shift
  and Hasse derivatives, and the trivariate ring `Poly3`;
* matrices `Mat`: finite sums `rangeSum`, the Laplace determinant, multilinearity, alternation,
  `det_matMul`, and weighted-degree bounds on determinants;
* ring and field isomorphisms (`RingIso`, `FieldIso`);
* fraction fields `Frac D` of a domain, base change `UPoly.mapHom`, and dynamic gcd splitting
  over a field;
* bivariate polynomials `Poly2`, Sylvester-elimination helper identities (`SylElim`), and
  variable-length coefficient arithmetic (`polyAddVar`, `shiftPoly`, …).
-/

public section
-- Avoid the choice-based LawfulBEq derived from the Fin order package.
attribute [-instance] Fin.instLinearOrderPackage
namespace Qsag
set_option autoImplicit false
open CommRingOps RoundPoly

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
@[expose] def id (R : Type) [CommRingOps R] : RingHom R R :=
  ⟨fun a => a, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem id_apply (a : R) : (RingHom.id R).toFun a = a := by rfl

/-- Composition `ψ ∘ φ`. -/
@[expose] def comp (ψ : RingHom S T) (φ : RingHom R S) : RingHom R T where
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
  show evalCoeffs ((add a b).coeffs.map φ.toFun) s = _
  rw [coeffs_add, pAdd_eq]
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
@[expose] def eval₂Hom (φ : RingHom R S) (s : S) : RingHom (UPoly R) S where
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
@[expose] def evalHom (x : R) : RingHom (UPoly R) R := eval₂Hom (RingHom.id R) x

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


theorem ofList_coeffs (p : UPoly R) : ofList p.coeffs = p := by apply ext; rw [coeffs_ofList]; exact p.trimmed

/-- `C` as a ring homomorphism. -/
@[expose] def CHom : RingHom R (UPoly R) where
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
end Qsag

namespace Qsag

set_option autoImplicit false
open CommRingOps RoundPoly

namespace Mat
section Ring
variable {R : Type} [LawfulCommRing R]

private theorem ite_pos {α : Type} {p : Prop} [Decidable p] (hp : p) {a b : α} :
    (if p then a else b) = a := by
  split
  · rfl
  · next hn => exact absurd hp hn

private theorem ite_neg {α : Type} {p : Prop} [Decidable p] (hnp : ¬ p) {a b : α} :
    (if p then a else b) = b := by
  split
  · next hp => exact absurd hp hnp
  · rfl

/-! ## Structural finite sums `rangeSum` -/

def rangeSum : Nat → (Nat → R) → R
  | 0, _ => zero
  | n + 1, f => add (rangeSum n f) (f n)

theorem rangeSum_congr {n : Nat} {f g : Nat → R} (h : ∀ i, i < n → f i = g i) :
    rangeSum n f = rangeSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show add (rangeSum n f) (f n) = add (rangeSum n g) (g n)
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

theorem rangeSum_eq_zero {n : Nat} {f : Nat → R} (h : ∀ i, i < n → f i = zero) :
    rangeSum n f = zero := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show add (rangeSum n f) (f n) = zero
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n), LawfulCommRing.add_zero]

theorem rangeSum_add (n : Nat) (f g : Nat → R) :
    rangeSum n (fun i => add (f i) (g i)) = add (rangeSum n f) (rangeSum n g) := by
  induction n with
  | zero => show zero = add zero zero; rw [LawfulCommRing.add_zero]
  | succ n ih =>
    show add (rangeSum n _) (add (f n) (g n)) = add (add (rangeSum n f) (f n)) (add (rangeSum n g) (g n))
    rw [ih]; constructive_ring

theorem rangeSum_mul_left (c : R) (n : Nat) (f : Nat → R) :
    rangeSum n (fun i => mul c (f i)) = mul c (rangeSum n f) := by
  induction n with
  | zero => show zero = mul c zero; rw [LawfulCommRing.mul_zero]
  | succ n ih =>
    show add (rangeSum n _) (mul c (f n)) = mul c (add (rangeSum n f) (f n))
    rw [ih, LawfulCommRing.left_distrib]

theorem rangeSum_mul_right (c : R) (n : Nat) (f : Nat → R) :
    rangeSum n (fun i => mul (f i) c) = mul (rangeSum n f) c := by
  induction n with
  | zero => show zero = mul zero c; rw [LawfulCommRing.zero_mul]
  | succ n ih =>
    show add (rangeSum n _) (mul (f n) c) = mul (add (rangeSum n f) (f n)) c
    rw [ih]; constructive_ring

theorem rangeSum_single {n j₀ : Nat} (hj₀ : j₀ < n) (f : Nat → R)
    (hz : ∀ j, j < n → j ≠ j₀ → f j = zero) :
    rangeSum n f = f j₀ := by
  induction n with
  | zero => exact absurd hj₀ (Nat.not_lt_zero _)
  | succ n ih =>
    show add (rangeSum n f) (f n) = f j₀
    if hEq : j₀ = n then
      subst hEq
      rw [rangeSum_eq_zero (fun j hj => hz j (Nat.lt_succ_of_lt hj) (Nat.ne_of_lt hj)), LawfulCommRing.zero_add]
    else
      rw [ih (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj₀) hEq) (fun j hj => hz j (Nat.lt_succ_of_lt hj)),
        hz n (Nat.lt_succ_self n) (Ne.symm hEq), LawfulCommRing.add_zero]

theorem map_rangeSum {S : Type} [LawfulCommRing S] (φ : RingHom R S) (n : Nat) (f : Nat → R) :
    φ.toFun (rangeSum n f) = rangeSum n (fun i => φ.toFun (f i)) := by
  induction n with
  | zero => exact φ.map_zero
  | succ n ih => show φ.toFun (add _ _) = add _ _; rw [φ.map_add, ih]

private theorem rangeSum_antisym_eq_zero :
    ∀ (n : Nat) (g : Nat → Nat → R),
      (∀ i, i < n → g i i = zero) → (∀ i, i < n → ∀ j, j < n → g i j = neg (g j i)) →
      rangeSum n (fun i => rangeSum n (fun j => g i j)) = zero
  | 0, _, _, _ => rfl
  | n + 1, g, hdiag, hanti => by
    show add (rangeSum n (fun i => add (rangeSum n (fun j => g i j)) (g i n)))
        (add (rangeSum n (fun j => g n j)) (g n n)) = zero
    rw [rangeSum_add, rangeSum_antisym_eq_zero n g
        (fun i hi => hdiag i (Nat.lt_succ_of_lt hi))
        (fun i hi j hj => hanti i (Nat.lt_succ_of_lt hi) j (Nat.lt_succ_of_lt hj)),
      hdiag n (Nat.lt_succ_self n), LawfulCommRing.zero_add, LawfulCommRing.add_zero, ← rangeSum_add]
    exact rangeSum_eq_zero fun i hi => by
      rw [hanti i (Nat.lt_succ_of_lt hi) n (Nat.lt_succ_self n)]
      exact LawfulCommRing.add_left_neg (g n i)

/-! ## Determinant via Laplace expansion along row `0` -/

def skipIdx (r i : Nat) : Nat := if i < r then i else i + 1

theorem skipIdx_lt {r i k : Nat} (hi : i < k) : skipIdx r i < k + 1 := by unfold skipIdx; split <;> omega

def minor (M : Nat → Nat → R) (r c : Nat) : Nat → Nat → R :=
  fun i j => M (skipIdx r i) (skipIdx c j)

def signed (j : Nat) (x : R) : R := if j % 2 = 0 then x else neg x

private theorem signed_zero (j : Nat) : signed j (zero : R) = zero := by
  unfold signed; if h : j % 2 = 0 then rw [ite_pos h] else rw [ite_neg h, LawfulCommRing.neg_zero]

private theorem signed_add (j : Nat) (x y : R) :
    signed j (add x y) = add (signed j x) (signed j y) := by
  unfold signed; split
  · rfl
  · constructive_ring

private theorem signed_mul_left (j : Nat) (c x : R) :
    signed j (mul c x) = mul c (signed j x) := by
  unfold signed; split
  · rfl
  · constructive_ring

private theorem signed_rangeSum (j n : Nat) (f : Nat → R) :
    signed j (rangeSum n f) = rangeSum n (fun i => signed j (f i)) := by
  induction n with
  | zero => exact signed_zero j
  | succ n ih => show signed j (add _ _) = add _ _; rw [signed_add, ih]

private theorem signed_signed (j₁ j₂ : Nat) (x : R) :
    signed j₁ (signed j₂ x) = signed (j₁ + j₂) x := by
  unfold signed
  if h1 : j₁ % 2 = 0 then
    if h2 : j₂ % 2 = 0 then rw [ite_pos h2, ite_pos h1, ite_pos (by omega)]
    else rw [ite_neg h2, ite_pos h1, ite_neg (by omega)]
  else
    if h2 : j₂ % 2 = 0 then rw [ite_pos h2, ite_neg h1, ite_neg (by omega)]
    else rw [ite_neg h2, ite_neg h1, ite_pos (by omega)]; constructive_ring

def det : Nat → (Nat → Nat → R) → R
  | 0, _ => one
  | k + 1, M => rangeSum (k + 1) (fun j => signed j (mul (M 0 j) (det k (minor M 0 j))))

theorem det_congr :
    ∀ (k : Nat) {M N : Nat → Nat → R},
      (∀ i, i < k → ∀ j, j < k → M i j = N i j) → det k M = det k N
  | 0, _, _, _ => rfl
  | k + 1, M, N, h =>
    rangeSum_congr fun j hj => by
      have hm : det k (minor M 0 j) = det k (minor N 0 j) :=
        det_congr k fun i hi c hc => h (i + 1) (Nat.succ_lt_succ hi) (skipIdx j c) (skipIdx_lt hc)
      rw [h 0 (Nat.zero_lt_succ k) j hj, hm]

theorem map_det {S : Type} [LawfulCommRing S] (φ : RingHom R S) :
    ∀ (k : Nat) (M : Nat → Nat → R), φ.toFun (det k M) = det k (fun i j => φ.toFun (M i j))
  | 0, _ => φ.map_one
  | k + 1, M => by
    show φ.toFun (rangeSum (k + 1) _) = rangeSum (k + 1) _
    rw [map_rangeSum]
    refine rangeSum_congr fun j _ => ?_
    unfold signed; split
    · rw [φ.map_mul, map_det φ k (minor M 0 j)]; rfl
    · rw [φ.map_neg, φ.map_mul, map_det φ k (minor M 0 j)]; rfl

/-! ## Triangular, column-0, and identity determinants -/

theorem det_col0_zero :
    ∀ (k : Nat) (M : Nat → Nat → R), (∀ i, i < k + 1 → M i 0 = zero) → det (k + 1) M = zero
  | 0, M, h => by
    show add zero (signed 0 (mul (M 0 0) one)) = zero
    rw [h 0 Nat.zero_lt_one, LawfulCommRing.zero_mul, signed_zero, LawfulCommRing.add_zero]
  | k + 1, M, h =>
    rangeSum_eq_zero fun j _ => by
      cases j with
      | zero => rw [h 0 (Nat.zero_lt_succ _), LawfulCommRing.zero_mul, signed_zero]
      | succ j' =>
        rw [det_col0_zero k (minor M 0 (j' + 1)) (fun i hi => h (i + 1) (Nat.succ_lt_succ hi)),
          LawfulCommRing.mul_zero, signed_zero]

theorem det_col0_unit (k : Nat) (M : Nat → Nat → R) (h : ∀ i, i < k → M (i + 1) 0 = zero) :
    det (k + 1) M = mul (M 0 0) (det k (minor M 0 0)) := by
  show rangeSum (k + 1) _ = _
  rw [rangeSum_single (Nat.zero_lt_succ k) _ fun j hj hne => ?_]
  · rfl
  · cases j with
    | zero => exact absurd rfl hne
    | succ j' =>
      cases k with
      | zero => exfalso; omega
      | succ k' =>
        rw [det_col0_zero k' (minor M 0 (j' + 1)) (fun i hi => h i hi), LawfulCommRing.mul_zero, signed_zero]

theorem det_row0_unit (k : Nat) (M : Nat → Nat → R) (h : ∀ j, j < k → M 0 (j + 1) = zero) :
    det (k + 1) M = mul (M 0 0) (det k (minor M 0 0)) := by
  show rangeSum (k + 1) _ = _
  rw [rangeSum_single (Nat.zero_lt_succ k) _ fun j hj hne => ?_]
  · rfl
  · cases j with
    | zero => exact absurd rfl hne
    | succ j' => rw [h j' (Nat.lt_of_succ_lt_succ hj), LawfulCommRing.zero_mul, signed_zero]

theorem det_lower_tri_const (c : R) :
    ∀ (k : Nat) (M : Nat → Nat → R),
      (∀ i j, i < j → j < k → M i j = zero) → (∀ i, i < k → M i i = c) →
      det k M = CRing.npow c k
  | 0, _, _, _ => rfl
  | k + 1, M, hlt, hdiag => by
    rw [det_row0_unit k M (fun j hj => hlt 0 (j + 1) (Nat.zero_lt_succ j) (Nat.succ_lt_succ hj)),
      hdiag 0 (Nat.zero_lt_succ k),
      det_lower_tri_const c k (minor M 0 0)
        (fun i j hij hjk => hlt (i + 1) (j + 1) (Nat.succ_lt_succ hij) (Nat.succ_lt_succ hjk))
        (fun i hi => hdiag (i + 1) (Nat.succ_lt_succ hi))]
    exact LawfulCommRing.mul_comm c (CRing.npow c k)

private theorem npow_one : ∀ k : Nat, CRing.npow (one : R) k = one
  | 0 => rfl
  | k + 1 => by show mul (CRing.npow one k) one = one; rw [npow_one k, LawfulCommRing.one_mul]

theorem det_lower_tri_one (k : Nat) (M : Nat → Nat → R)
    (hlt : ∀ i j, i < j → j < k → M i j = zero) (hdiag : ∀ i, i < k → M i i = one) :
    det k M = one := by
  rw [det_lower_tri_const one k M hlt hdiag, npow_one]

def idMat (i j : Nat) : R := if i = j then one else zero

theorem det_idMat (k : Nat) : det k (idMat (R := R)) = one :=
  det_lower_tri_one k idMat
    (fun i j hij _ => by unfold idMat; rw [ite_neg (Nat.ne_of_lt hij)])
    (fun i _ => by unfold idMat; rw [ite_pos rfl])

/-! ## Weighted `DegFn` bound on `det k M` -/

def natRangeSum : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => natRangeSum n f + f n

private theorem natRangeSum_shift :
    ∀ (k : Nat) (f : Nat → Nat), f 0 + natRangeSum k (fun i => f (i + 1)) = natRangeSum (k + 1) f
  | 0, f => by show f 0 + 0 = 0 + f 0; omega
  | k + 1, f => by
    show f 0 + (natRangeSum k (fun i => f (i + 1)) + f (k + 1)) = natRangeSum (k + 1) f + f (k + 1)
    rw [← Nat.add_assoc, natRangeSum_shift k f]

private theorem natRangeSum_skipIdx :
    ∀ (k j : Nat) (cWt : Nat → Nat),
      j < k + 1 → cWt j + natRangeSum k (fun c => cWt (skipIdx j c)) = natRangeSum (k + 1) cWt
  | 0, j, cWt, hj => by
    have hj0 : j = 0 := by omega
    subst hj0; show cWt 0 + 0 = 0 + cWt 0; omega
  | k + 1, j, cWt, hj => by
    if hEq : j = k + 1 then
      subst hEq
      have aux : ∀ m, m ≤ k + 1 → natRangeSum m (fun c => cWt (skipIdx (k + 1) c)) = natRangeSum m cWt := by
        intro m; induction m with
        | zero => intro _; rfl
        | succ m ihm =>
          intro hm; show natRangeSum m _ + cWt (skipIdx (k + 1) m) = natRangeSum m cWt + cWt m
          rw [ihm (by omega)]; unfold skipIdx; rw [ite_pos (by omega)]
      show cWt (k + 1) + natRangeSum (k + 1) _ = natRangeSum (k + 1) cWt + cWt (k + 1)
      rw [aux (k + 1) (Nat.le_refl _)]; omega
    else
      have ih := natRangeSum_skipIdx k j cWt (by omega)
      have hsk : skipIdx j k = k + 1 := by unfold skipIdx; rw [ite_neg (by omega)]
      show cWt j + (natRangeSum k (fun c => cWt (skipIdx j c)) + cWt (skipIdx j k)) =
        natRangeSum (k + 1) cWt + cWt (k + 1)
      rw [hsk]; omega

section WeightedDeg
variable [DecidableEq R]

theorem degFn_det_weighted_le {w : R → Nat} (hw : DegFn w) (hw1 : w one = 0) :
    ∀ (k : Nat) (M : Nat → Nat → R) (rowWt colWt : Nat → Nat),
      (∀ i, i < k → ∀ j, j < k → M i j ≠ zero → w (M i j) + colWt j ≤ rowWt i) →
      det k M ≠ zero → w (det k M) + natRangeSum k colWt ≤ natRangeSum k rowWt
  | 0, _, _, _, _, _ => by show w one + 0 ≤ 0; rw [hw1]; exact Nat.zero_le 0
  | k + 1, M, rowWt, colWt, hBnd, hNe => by
    let term (j : Nat) : R := signed j (mul (M 0 j) (det k (minor M 0 j)))
    have hTermBnd : ∀ j, j < k + 1 → term j ≠ zero →
        w (term j) + natRangeSum (k + 1) colWt ≤ natRangeSum (k + 1) rowWt := by
      intro j hj htj
      have hMulNe : mul (M 0 j) (det k (minor M 0 j)) ≠ zero := fun e => by
        dsimp [term] at htj; rw [e, signed_zero] at htj; exact htj rfl
      have hM0Ne : M 0 j ≠ zero := fun e => hMulNe (by rw [e, LawfulCommRing.zero_mul])
      have hMinNe : det k (minor M 0 j) ≠ zero := fun e => hMulNe (by rw [e, LawfulCommRing.mul_zero])
      have h0 := hBnd 0 (Nat.zero_lt_succ k) j hj hM0Ne
      have hih := degFn_det_weighted_le hw hw1 k (minor M 0 j)
        (fun i => rowWt (i + 1)) (fun c => colWt (skipIdx j c))
        (fun i hi c hc => hBnd (i + 1) (Nat.succ_lt_succ hi) (skipIdx j c) (skipIdx_lt hc)) hMinNe
      have hSignW : w (term j) ≤ w (M 0 j) + w (det k (minor M 0 j)) := by
        dsimp [term]; unfold signed; split
        · exact hw.mul_le _ _
        · exact Nat.le_trans (hw.neg_le _) (hw.mul_le _ _)
      have hCol := natRangeSum_skipIdx k j colWt hj
      have hRow := natRangeSum_shift k rowWt
      omega
    have hSumBnd : ∀ m, m ≤ k + 1 → rangeSum m term ≠ zero →
        w (rangeSum m term) + natRangeSum (k + 1) colWt ≤ natRangeSum (k + 1) rowWt := by
      intro m; induction m with
      | zero => intro _ h0; exact absurd rfl h0
      | succ m ihm =>
        intro hm hsum
        exact UPoly.bnd_add hw (ihm (Nat.le_of_succ_le hm)) (hTermBnd m (Nat.lt_of_succ_le hm)) hsum
    exact hSumBnd (k + 1) (Nat.le_refl _) hNe

end WeightedDeg

/-! ## Row multilinearity, alternating rows, and `det_matMul` -/

def updRow (M : Nat → Nat → R) (r : Nat) (v : Nat → R) (i j : Nat) : R :=
  if i = r then v j else M i j

private theorem minor_updRow_zero (M : Nat → Nat → R) (v : Nat → R) (k j : Nat) :
    det k (minor (updRow M 0 v) 0 j) = det k (minor M 0 j) :=
  det_congr k fun _ _ _ _ => rfl

private theorem minor_updRow_succ (M : Nat → Nat → R) (r : Nat) (v : Nat → R) (k j : Nat) :
    det k (minor (updRow M (r + 1) v) 0 j) =
      det k (updRow (minor M 0 j) r (fun c => v (skipIdx j c))) :=
  det_congr k fun i _ c _ => by
    show (if i + 1 = r + 1 then v (skipIdx j c) else M (i + 1) (skipIdx j c)) =
      if i = r then v (skipIdx j c) else M (i + 1) (skipIdx j c)
    if h : i = r then rw [h, ite_pos rfl, ite_pos rfl]
    else rw [ite_neg (fun e => h (Nat.succ.inj e)), ite_neg h]

theorem det_updRow_zero :
    ∀ (k r : Nat) (M : Nat → Nat → R), r < k → det k (updRow M r (fun _ => zero)) = zero
  | 0, _, _, hr => absurd hr (Nat.not_lt_zero _)
  | k + 1, 0, _, _ =>
    rangeSum_eq_zero fun j _ => by show signed j (mul zero _) = zero; rw [LawfulCommRing.zero_mul, signed_zero]
  | k + 1, r + 1, M, hr =>
    rangeSum_eq_zero fun j _ => by
      show signed j (mul (M 0 j) (det k (minor (updRow M (r + 1) _) 0 j))) = zero
      rw [minor_updRow_succ, det_updRow_zero k r (minor M 0 j) (Nat.lt_of_succ_lt_succ hr),
        LawfulCommRing.mul_zero, signed_zero]

theorem det_updRow_add :
    ∀ (k r : Nat) (M : Nat → Nat → R) (u v : Nat → R), r < k →
      det k (updRow M r (fun j => add (u j) (v j))) =
        add (det k (updRow M r u)) (det k (updRow M r v))
  | 0, _, _, _, _, hr => absurd hr (Nat.not_lt_zero _)
  | k + 1, 0, M, u, v, _ => by
    show rangeSum (k + 1) _ = add (rangeSum (k + 1) _) (rangeSum (k + 1) _)
    rw [← rangeSum_add]; refine rangeSum_congr fun j _ => ?_
    show signed j (mul (add (u j) (v j)) (det k (minor (updRow M 0 _) 0 j))) =
      add (signed j (mul (u j) (det k (minor (updRow M 0 u) 0 j))))
        (signed j (mul (v j) (det k (minor (updRow M 0 v) 0 j))))
    rw [minor_updRow_zero, minor_updRow_zero, minor_updRow_zero, ← signed_add]
    congr 1; constructive_ring
  | k + 1, r + 1, M, u, v, hr => by
    show rangeSum (k + 1) _ = add (rangeSum (k + 1) _) (rangeSum (k + 1) _)
    rw [← rangeSum_add]; refine rangeSum_congr fun j _ => ?_
    show signed j (mul (M 0 j) (det k (minor (updRow M (r + 1) _) 0 j))) =
      add (signed j (mul (M 0 j) (det k (minor (updRow M (r + 1) u) 0 j))))
        (signed j (mul (M 0 j) (det k (minor (updRow M (r + 1) v) 0 j))))
    rw [minor_updRow_succ, minor_updRow_succ, minor_updRow_succ,
      det_updRow_add k r (minor M 0 j) _ _ (Nat.lt_of_succ_lt_succ hr),
      LawfulCommRing.left_distrib, signed_add]

theorem det_updRow_smul :
    ∀ (k r : Nat) (M : Nat → Nat → R) (c : R) (u : Nat → R), r < k →
      det k (updRow M r (fun j => mul c (u j))) = mul c (det k (updRow M r u))
  | 0, _, _, _, _, hr => absurd hr (Nat.not_lt_zero _)
  | k + 1, 0, M, c, u, _ => by
    show rangeSum (k + 1) _ = mul c (rangeSum (k + 1) _)
    rw [← rangeSum_mul_left]; refine rangeSum_congr fun j _ => ?_
    show signed j (mul (mul c (u j)) (det k (minor (updRow M 0 _) 0 j))) =
      mul c (signed j (mul (u j) (det k (minor (updRow M 0 u) 0 j))))
    rw [minor_updRow_zero, minor_updRow_zero, LawfulCommRing.mul_assoc, signed_mul_left]
  | k + 1, r + 1, M, c, u, hr => by
    show rangeSum (k + 1) _ = mul c (rangeSum (k + 1) _)
    rw [← rangeSum_mul_left]; refine rangeSum_congr fun j _ => ?_
    show signed j (mul (M 0 j) (det k (minor (updRow M (r + 1) _) 0 j))) =
      mul c (signed j (mul (M 0 j) (det k (minor (updRow M (r + 1) u) 0 j))))
    rw [minor_updRow_succ, minor_updRow_succ,
      det_updRow_smul k r (minor M 0 j) c _ (Nat.lt_of_succ_lt_succ hr), ← signed_mul_left]
    congr 1; constructive_ring

private theorem rangeSum_skipIdx :
    ∀ (n j₁ : Nat) (h : Nat → R),
      j₁ < n + 1 → h j₁ = zero → rangeSum n (fun j₂' => h (skipIdx j₁ j₂')) = rangeSum (n + 1) h
  | 0, j₁, h, hj₁, hz => by
    have hj0 : j₁ = 0 := by omega
    subst hj0; show zero = add zero (h 0); rw [hz, LawfulCommRing.add_zero]
  | n + 1, j₁, h, hj₁, hz => by
    if hEq : j₁ = n + 1 then
      subst hEq
      have hSame : rangeSum (n + 1) (fun j₂' => h (skipIdx (n + 1) j₂')) = rangeSum (n + 1) h :=
        rangeSum_congr fun j₂' hj₂' => by unfold skipIdx; rw [ite_pos hj₂']
      show rangeSum (n + 1) _ = add (rangeSum (n + 1) h) (h (n + 1))
      rw [hSame, hz, LawfulCommRing.add_zero]
    else
      show add (rangeSum n (fun j₂' => h (skipIdx j₁ j₂'))) (h (skipIdx j₁ n)) =
        add (rangeSum (n + 1) h) (h (n + 1))
      rw [rangeSum_skipIdx n j₁ h (by omega) hz]
      have hsk : skipIdx j₁ n = n + 1 := by unfold skipIdx; rw [ite_neg (by omega)]
      rw [hsk]

private theorem skipIdx_comm {j₁ j₂ : Nat} (hlt : j₁ < j₂) (c : Nat) :
    skipIdx j₁ (skipIdx (j₂ - 1) c) = skipIdx j₂ (skipIdx j₁ c) := by
  unfold skipIdx
  if h1 : c < j₂ - 1 then
    rw [ite_pos h1]
    if h2 : c < j₁ then rw [ite_pos h2, ite_pos (by omega)] else rw [ite_neg h2, ite_pos (by omega)]
  else
    rw [ite_neg h1, ite_neg (by omega)]
    if h2 : c < j₁ then exfalso; omega else rw [ite_neg h2, ite_neg (by omega)]

private theorem det_row01_eq_zero (k : Nat) (M : Nat → Nat → R)
    (hEq : ∀ j, j < k + 2 → M 0 j = M 1 j) :
    det (k + 2) M = zero := by
  let min2 (a b : Nat) : Nat → Nat → R := fun i c => M (i + 2) (skipIdx b (skipIdx a c))
  let g (j₁ j₂ : Nat) : R :=
    if j₁ = j₂ then zero
    else if j₂ < j₁ then signed (j₁ + j₂) (mul (mul (M 0 j₁) (M 1 j₂)) (det k (min2 j₂ j₁)))
    else signed (j₁ + j₂ - 1) (mul (mul (M 0 j₁) (M 1 j₂)) (det k (min2 j₁ j₂)))
  have hExpand : det (k + 2) M = rangeSum (k + 2) (fun j₁ => rangeSum (k + 2) (fun j₂ => g j₁ j₂)) := by
    show rangeSum (k + 2) _ = _; refine rangeSum_congr fun j₁ hj₁ => ?_
    show signed j₁ (mul (M 0 j₁) (rangeSum (k + 1) _)) = _
    rw [← rangeSum_mul_left, signed_rangeSum, ← rangeSum_skipIdx (k + 1) j₁ (g j₁) hj₁ (by dsimp [g]; rw [ite_pos rfl])]
    refine rangeSum_congr fun j₂' _ => ?_
    rw [← signed_mul_left, signed_signed, ← LawfulCommRing.mul_assoc]
    have hM1 : minor M 0 j₁ 0 j₂' = M 1 (skipIdx j₁ j₂') := rfl
    rw [hM1]
    if hlt : j₂' < j₁ then
      have hsk : skipIdx j₁ j₂' = j₂' := by unfold skipIdx; rw [ite_pos hlt]
      have hMinEq : det k (minor (minor M 0 j₁) 0 j₂') = det k (min2 j₂' j₁) := det_congr k fun _ _ _ _ => rfl
      dsimp only [g]; rw [hsk, ite_neg (Nat.ne_of_gt hlt), ite_pos hlt, hMinEq]
    else
      have hsk : skipIdx j₁ j₂' = j₂' + 1 := by unfold skipIdx; rw [ite_neg hlt]
      have hgt : j₁ < j₂' + 1 := by omega
      have hMinEq : det k (minor (minor M 0 j₁) 0 j₂') = det k (min2 j₁ (j₂' + 1)) :=
        det_congr k fun i _ c _ => congrArg (M (i + 2)) (skipIdx_comm hgt c)
      dsimp only [g]
      rw [hsk, ite_neg (Nat.ne_of_lt hgt), ite_neg (show ¬ j₂' + 1 < j₁ by omega),
        show j₁ + (j₂' + 1) - 1 = j₁ + j₂' by omega, hMinEq]
  rw [hExpand]
  have hFlip (a b : Nat) (hab : 1 ≤ a + b) (x : R) : signed (a + b) x = neg (signed (a + b - 1) x) := by
    unfold signed
    if hp : (a + b) % 2 = 0 then rw [ite_pos hp, ite_neg (by omega)]; constructive_ring
    else rw [ite_neg hp, ite_pos (by omega)]
  refine rangeSum_antisym_eq_zero (k + 2) g (fun i _ => by dsimp [g]; rw [ite_pos rfl]) (fun i hi j hj => ?_)
  if hij : i = j then
    subst hij; dsimp only [g]; rw [ite_pos rfl, LawfulCommRing.neg_zero]
  else if hji : j < i then
    dsimp only [g]
    rw [ite_neg hij, ite_pos hji, ite_neg (Ne.symm hij), ite_neg (show ¬ i < j by omega),
      show mul (M 0 i) (M 1 j) = mul (M 0 j) (M 1 i) by rw [← hEq i hi, ← hEq j hj, LawfulCommRing.mul_comm],
      Nat.add_comm j i, hFlip i j (by omega)]
  else
    have hijLt : i < j := by omega
    dsimp only [g]
    rw [ite_neg hij, ite_neg hji, ite_neg (Ne.symm hij), ite_pos hijLt,
      show mul (M 0 i) (M 1 j) = mul (M 0 j) (M 1 i) by rw [← hEq i hi, ← hEq j hj, LawfulCommRing.mul_comm],
      Nat.add_comm j i, hFlip i j (by omega), LawfulCommRing.neg_neg]

theorem det_adj_eq_zero :
    ∀ (k r : Nat) (M : Nat → Nat → R), r + 1 < k → (∀ j, j < k → M r j = M (r + 1) j) → det k M = zero
  | 0, _, _, hr, _ => absurd hr (Nat.not_lt_zero _)
  | 1, _, _, hr, _ => by exfalso; omega
  | k + 2, 0, M, _, hEq => det_row01_eq_zero k M hEq
  | k + 2, r + 1, M, hr, hEq =>
    rangeSum_eq_zero fun j _ => by
      have hm0 := det_adj_eq_zero (k + 1) r (minor M 0 j) (Nat.lt_of_succ_lt_succ hr)
        fun c hc => hEq (skipIdx j c) (skipIdx_lt hc)
      show signed j (mul (M 0 j) (det (k + 1) (minor M 0 j))) = zero
      rw [hm0, LawfulCommRing.mul_zero, signed_zero]

def swapAdjIdx (r i : Nat) : Nat := if i = r then r + 1 else if i = r + 1 then r else i

theorem det_swap_adj (k r : Nat) (M : Nat → Nat → R) (hr : r + 1 < k) :
    det k (fun i j => M (swapAdjIdx r i) j) = neg (det k M) := by
  let S := updRow (updRow M r (fun j => add (M r j) (M (r + 1) j)))
    (r + 1) (fun j => add (M r j) (M (r + 1) j))
  have hne : r ≠ r + 1 := by omega
  have hS0 : det k S = zero := det_adj_eq_zero k r S hr fun j _ => by
    dsimp only [S]; unfold updRow; rw [ite_neg hne, ite_pos rfl, ite_pos rfl]
  have hrLt : r < k := by omega
  dsimp only [S] at hS0; rw [det_updRow_add k (r + 1) _ _ _ hr] at hS0
  have h11 : det k (updRow (updRow M r (fun j => add (M r j) (M (r + 1) j))) (r + 1) (M r)) =
      det k (updRow (updRow M (r + 1) (M r)) r (fun j => add (M r j) (M (r + 1) j))) :=
    det_congr k fun i _ j _ => by
      unfold updRow
      if h1 : i = r then rw [h1, ite_neg hne, ite_pos rfl, ite_pos rfl]
      else if h2 : i = r + 1 then rw [h2, ite_pos rfl, ite_neg (Ne.symm hne), ite_pos rfl]
      else rw [ite_neg h2, ite_neg h1, ite_neg h1, ite_neg h2]
  have h12 : det k (updRow (updRow M r (fun j => add (M r j) (M (r + 1) j))) (r + 1) (M (r + 1))) =
      det k (updRow M r (fun j => add (M r j) (M (r + 1) j))) :=
    det_congr k fun i _ j _ => by
      unfold updRow
      if h2 : i = r + 1 then rw [h2, ite_pos rfl, ite_neg (Ne.symm hne)] else rw [ite_neg h2]
  rw [h11, h12, det_updRow_add k r _ _ _ hrLt, det_updRow_add k r _ _ _ hrLt] at hS0
  have hrr : det k (updRow (updRow M (r + 1) (M r)) r (M r)) = zero :=
    det_adj_eq_zero k r _ hr fun j _ => by unfold updRow; rw [ite_pos rfl, ite_neg (Ne.symm hne), ite_pos rfl]
  have hss : det k (updRow M r (M (r + 1))) = zero :=
    det_adj_eq_zero k r _ hr fun j _ => by unfold updRow; rw [ite_pos rfl, ite_neg (Ne.symm hne)]
  have hId : det k (updRow M r (M r)) = det k M :=
    det_congr k fun i _ j _ => by unfold updRow; if h1 : i = r then rw [h1, ite_pos rfl] else rw [ite_neg h1]
  have hSw : det k (updRow (updRow M (r + 1) (M r)) r (M (r + 1))) =
      det k (fun i j => M (swapAdjIdx r i) j) :=
    det_congr k fun i _ j _ => by
      unfold updRow swapAdjIdx
      if h1 : i = r then rw [h1, ite_pos rfl, ite_pos rfl]
      else if h2 : i = r + 1 then rw [h2, ite_neg (Ne.symm hne), ite_pos rfl, ite_neg (Ne.symm hne), ite_pos rfl]
      else rw [ite_neg h1, ite_neg h2, ite_neg h1, ite_neg h2]
  rw [hrr, hss, hId, hSw, LawfulCommRing.zero_add, LawfulCommRing.add_zero] at hS0
  apply LawfulCommRing.add_left_cancel (a := det k M)
  rw [LawfulCommRing.add_comm (det k M), hS0, LawfulCommRing.add_right_neg]

theorem det_eq_zero_of_row_eq (k r₁ r₂ : Nat) (M : Nat → Nat → R)
    (hr₁ : r₁ < r₂) (hr₂ : r₂ < k) (hEq : ∀ j, j < k → M r₁ j = M r₂ j) :
    det k M = zero := by
  have aux : ∀ (d r₂ : Nat) (M : Nat → Nat → R),
      r₂ - r₁ = d → r₁ < r₂ → r₂ < k → (∀ j, j < k → M r₁ j = M r₂ j) → det k M = zero := by
    intro d; induction d with
    | zero => intros; exfalso; omega
    | succ d ihd =>
      intro r₂ M hd hlt hk hE
      if hd0 : d = 0 then
        have hr₂Eq : r₂ = r₁ + 1 := by omega
        subst hr₂Eq; exact det_adj_eq_zero k r₁ M hk hE
      else
        let M' := fun i j => M (swapAdjIdx (r₂ - 1) i) j
        have hSw := det_swap_adj k (r₂ - 1) M (by omega)
        have hM'0 : det k M' = zero :=
          ihd (r₂ - 1) M' (by omega) (by omega) (by omega) fun j hj => by
            dsimp only [M']; unfold swapAdjIdx
            rw [ite_neg (show r₁ ≠ r₂ - 1 by omega), ite_neg (show r₁ ≠ r₂ - 1 + 1 by omega),
              ite_pos rfl, show r₂ - 1 + 1 = r₂ by omega]
            exact hE j hj
        rw [hM'0] at hSw; have h0 := congrArg neg hSw
        rw [LawfulCommRing.neg_zero, LawfulCommRing.neg_neg] at h0; exact h0.symm
  exact aux (r₂ - r₁) r₂ M rfl hr₁ hr₂ hEq

/-! ### Row-permutation factoring `det_perm_rows` and `det_matMul` -/

private def phiPot : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, σ => phiPot n σ + n * σ n

private theorem phiPot_le_cube :
    ∀ (n k : Nat) (σ : Nat → Nat), n ≤ k → (∀ i, i < k → σ i < k) → phiPot n σ ≤ n * k * k
  | 0, _, _, _, _ => Nat.zero_le _
  | n + 1, k, σ, hnk, hσ => by
    show phiPot n σ + n * σ n ≤ (n + 1) * k * k
    have ih := phiPot_le_cube n k σ (by omega) hσ
    have hsn : σ n < k := hσ n (by omega)
    have hmul : n * σ n ≤ k * k := Nat.mul_le_mul (by omega) (by omega)
    rw [Nat.succ_mul, Nat.add_mul]; omega

private theorem phiPot_swapAdj :
    ∀ (n r : Nat) (σ : Nat → Nat), r + 1 < n →
      phiPot n σ + σ r = phiPot n (fun i => σ (swapAdjIdx r i)) + σ (r + 1)
  | 0, _, _, hr => absurd hr (Nat.not_lt_zero _)
  | 1, _, _, hr => by omega
  | n + 2, r, σ, hr => by
    if hTop : r = n then
      subst r
      have aux : ∀ m, m ≤ n → phiPot m (fun i => σ (swapAdjIdx n i)) = phiPot m σ := by
        intro m; induction m with
        | zero => intro _; rfl
        | succ m ihm =>
          intro hm; show phiPot m _ + m * σ (swapAdjIdx n m) = phiPot m σ + m * σ m
          rw [ihm (by omega)]; unfold swapAdjIdx; rw [ite_neg (by omega), ite_neg (by omega)]
      show phiPot n σ + n * σ n + (n + 1) * σ (n + 1) + σ n =
        phiPot n (fun i => σ (swapAdjIdx n i)) + n * σ (swapAdjIdx n n) +
          (n + 1) * σ (swapAdjIdx n (n + 1)) + σ (n + 1)
      rw [aux n (Nat.le_refl _)]; unfold swapAdjIdx
      rw [ite_pos rfl, ite_neg (show n + 1 ≠ n by omega), ite_pos rfl, Nat.succ_mul, Nat.succ_mul]; omega
    else
      have ih := phiPot_swapAdj (n + 1) r σ (by omega)
      have hsk : swapAdjIdx r (n + 1) = n + 1 := by unfold swapAdjIdx; rw [ite_neg (by omega), ite_neg (by omega)]
      show phiPot (n + 1) σ + (n + 1) * σ (n + 1) + σ r =
        phiPot (n + 1) (fun i => σ (swapAdjIdx r i)) + (n + 1) * σ (swapAdjIdx r (n + 1)) + σ (r + 1)
      rw [hsk]; omega

private theorem find_dup_or_inv_or_inc (k : Nat) (σ : Nat → Nat) :
    (∃ i₁ i₂, i₁ < i₂ ∧ i₂ < k ∧ σ i₁ = σ i₂) ∨
    (∃ r, r + 1 < k ∧ σ (r + 1) < σ r) ∨ (∀ r, r + 1 < k → σ r < σ (r + 1)) := by
  have hAdj : ∀ m, m ≤ k →
      (∃ r, r + 1 < m ∧ σ (r + 1) ≤ σ r) ∨ (∀ r, r + 1 < m → σ r < σ (r + 1)) := by
    intro m; induction m with
    | zero => intro _; exact .inr fun _ h => absurd h (Nat.not_lt_zero _)
    | succ m ihm =>
      intro hm
      rcases ihm (Nat.le_of_succ_le hm) with ⟨r, hr, hle⟩ | hinc
      · exact .inl ⟨r, Nat.lt_succ_of_lt hr, hle⟩
      · if hm0 : m = 0 then exact .inr fun _ hr => by omega
        else if hle : σ m ≤ σ (m - 1) then
          exact .inl ⟨m - 1, by omega, by rwa [show m - 1 + 1 = m by omega]⟩
        else
          refine .inr fun r hr => ?_
          if hrEq : r = m - 1 then subst hrEq; rw [show m - 1 + 1 = m by omega]; omega
          else exact hinc r (by omega)
  rcases hAdj k (Nat.le_refl _) with ⟨r, hr, hle⟩ | hinc
  · if hEq : σ r = σ (r + 1) then exact .inl ⟨r, r + 1, Nat.lt_succ_self r, hr, hEq⟩
    else exact .inr (.inl ⟨r, hr, by omega⟩)
  · exact .inr (.inr hinc)

private theorem inc_endo_eq_id (k : Nat) (σ : Nat → Nat)
    (hBound : ∀ i, i < k → σ i < k) (hInc : ∀ r, r + 1 < k → σ r < σ (r + 1)) :
    ∀ i, i < k → σ i = i := by
  have hLo : ∀ i, i < k → i ≤ σ i := by
    intro i; induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ i ihi => intro hi; have := ihi (Nat.lt_of_succ_lt hi); have := hInc i hi; omega
  have hHi : ∀ d i, k - 1 - i = d → i < k → σ i ≤ i := by
    intro d; induction d with
    | zero =>
      intro i hd hi; have hiEq : i = k - 1 := by omega
      subst hiEq; have := hBound _ hi; omega
    | succ d ihd =>
      intro i hd hi; have hi1 : i + 1 < k := by omega
      have := ihd (i + 1) (by omega) hi1; have := hInc i hi1; omega
  intro i hi; exact Nat.le_antisymm (hHi (k - 1 - i) i rfl hi) (hLo i hi)

private theorem swapAdjIdx_lt {r i k : Nat} (hr : r + 1 < k) (hi : i < k) : swapAdjIdx r i < k := by
  unfold swapAdjIdx
  if h1 : i = r then rw [ite_pos h1]; exact hr
  else if h2 : i = r + 1 then rw [ite_neg h1, ite_pos h2]; omega
  else rw [ite_neg h1, ite_neg h2]; exact hi

theorem det_perm_rows (k : Nat) (B : Nat → Nat → R) (σ : Nat → Nat)
    (hBound : ∀ i, i < k → σ i < k) :
    det k (fun i j => B (σ i) j) = mul (det k (fun i j => idMat (σ i) j)) (det k B) := by
  have aux : ∀ (fuel : Nat) (σ : Nat → Nat),
      (∀ i, i < k → σ i < k) → k * k * k - phiPot k σ ≤ fuel →
      det k (fun i j => B (σ i) j) = mul (det k (fun i j => idMat (σ i) j)) (det k B) := by
    intro fuel; induction fuel with
    | zero =>
      intro σ hB hF
      rcases find_dup_or_inv_or_inc k σ with ⟨i₁, i₂, hi₁₂, hi₂k, hEq⟩ | ⟨r, hr, hinv⟩ | hinc
      · rw [det_eq_zero_of_row_eq k i₁ i₂ (fun i j => B (σ i) j) hi₁₂ hi₂k (fun j _ => congrArg (fun x => B x j) hEq),
          det_eq_zero_of_row_eq k i₁ i₂ (fun i j => idMat (σ i) j) hi₁₂ hi₂k (fun j _ => congrArg (fun x => idMat x j) hEq),
          LawfulCommRing.zero_mul]
      · exfalso
        let σ' := fun i => σ (swapAdjIdx r i)
        have hB' : ∀ i, i < k → σ' i < k := fun i hi => hB _ (swapAdjIdx_lt hr hi)
        have hCube := phiPot_le_cube k k σ' (Nat.le_refl k) hB'
        have hSw := phiPot_swapAdj k r σ hr
        dsimp only [σ'] at hCube; clear hB hB'; omega
      · have hId := inc_endo_eq_id k σ hB hinc
        rw [det_congr k (N := B) (fun i hi j _ => congrArg (fun x => B x j) (hId i hi)),
          det_congr k (N := idMat) (fun i hi j _ => congrArg (fun x => idMat x j) (hId i hi)),
          det_idMat, LawfulCommRing.one_mul]
    | succ fuel ih =>
      intro σ hB hF
      rcases find_dup_or_inv_or_inc k σ with ⟨i₁, i₂, hi₁₂, hi₂k, hEq⟩ | ⟨r, hr, hinv⟩ | hinc
      · rw [det_eq_zero_of_row_eq k i₁ i₂ (fun i j => B (σ i) j) hi₁₂ hi₂k (fun j _ => congrArg (fun x => B x j) hEq),
          det_eq_zero_of_row_eq k i₁ i₂ (fun i j => idMat (σ i) j) hi₁₂ hi₂k (fun j _ => congrArg (fun x => idMat x j) hEq),
          LawfulCommRing.zero_mul]
      · let σ' := fun i => σ (swapAdjIdx r i)
        have hB' : ∀ i, i < k → σ' i < k := fun i hi => hB _ (swapAdjIdx_lt hr hi)
        have hCube := phiPot_le_cube k k σ' (Nat.le_refl k) hB'
        have hSw := phiPot_swapAdj k r σ hr
        have hFuel' : k * k * k - phiPot k σ' ≤ fuel := by dsimp only [σ'] at hCube ⊢; clear ih hB hB'; omega
        have hStep := ih σ' hB' hFuel'
        have hNegB := det_swap_adj k r (fun i j => B (σ i) j) hr
        have hNegI := det_swap_adj k r (fun i j => idMat (R := R) (σ i) j) hr
        dsimp only [σ'] at hStep; rw [hNegB, hNegI] at hStep
        have h0 := congrArg neg hStep; rw [LawfulCommRing.neg_neg] at h0; rw [h0]; constructive_ring
      · have hId := inc_endo_eq_id k σ hB hinc
        rw [det_congr k (N := B) (fun i hi j _ => congrArg (fun x => B x j) (hId i hi)),
          det_congr k (N := idMat) (fun i hi j _ => congrArg (fun x => idMat x j) (hId i hi)),
          det_idMat, LawfulCommRing.one_mul]
  exact aux (k * k * k - phiPot k σ) σ hBound (Nat.le_refl _)

private theorem det_updRow_rangeSum (k r : Nat) (M : Nat → Nat → R) (hr : r < k) :
    ∀ (m : Nat) (c : Nat → R) (v : Nat → Nat → R),
      det k (updRow M r (fun j => rangeSum m (fun l => mul (c l) (v l j)))) =
        rangeSum m (fun l => mul (c l) (det k (updRow M r (v l))))
  | 0, _, _ => det_updRow_zero k r M hr
  | m + 1, c, v => by
    show det k (updRow M r (fun j => add _ _)) = add (rangeSum m _) _
    rw [det_updRow_add k r M _ _ hr, det_updRow_rangeSum k r M hr m c v,
      det_updRow_smul k r M (c m) (v m) hr]

def matMul (k : Nat) (A B : Nat → Nat → R) (i j : Nat) : R :=
  rangeSum k (fun l => mul (A i l) (B l j))

/-- **Multiplicativity of the determinant (`det_matMul`)**: over any `[LawfulCommRing R]`,
    `det k (matMul k A B) = mul (det k A) (det k B)`. -/
theorem det_matMul (k : Nat) (A B : Nat → Nat → R) :
    det k (matMul k A B) = mul (det k A) (det k B) := by
  let mix (m : Nat) (σ : Nat → Nat) (C : Nat → Nat → R) (i j : Nat) : R :=
    if i < m then matMul k A C i j else C (σ i) j
  have hStage : ∀ (m : Nat) (σ : Nat → Nat),
      m ≤ k → (∀ i, m ≤ i → i < k → σ i < k) →
      det k (mix m σ B) = mul (det k (mix m σ idMat)) (det k B) := by
    intro m; induction m with
    | zero => intro σ _ hσ; exact det_perm_rows k B σ (fun i hi => hσ i (Nat.zero_le i) hi)
    | succ m ihm =>
      intro σ hmk hσ
      have hmLt : m < k := hmk
      have hUpd (C : Nat → Nat → R) :
          det k (mix (m + 1) σ C) =
            det k (updRow (mix m σ C) m (fun j => rangeSum k (fun l => mul (A m l) (C l j)))) :=
        det_congr k fun i _ j _ => by
          show (if i < m + 1 then matMul k A C i j else C (σ i) j) =
            if i = m then rangeSum k (fun l => mul (A m l) (C l j))
            else if i < m then matMul k A C i j else C (σ i) j
          if hEq : i = m then rw [hEq, ite_pos (Nat.lt_succ_self m), ite_pos rfl]; rfl
          else if hLt : i < m then rw [ite_pos (Nat.lt_succ_of_lt hLt), ite_neg hEq, ite_pos hLt]
          else rw [ite_neg (by omega), ite_neg hEq, ite_neg hLt]
      rw [hUpd B, hUpd idMat, det_updRow_rangeSum k m (mix m σ B) hmLt k (A m) B,
        det_updRow_rangeSum k m (mix m σ idMat) hmLt k (A m) idMat, ← rangeSum_mul_right]
      refine rangeSum_congr fun l hl => ?_
      let σ' := fun i => if i = m then l else σ i
      have hMixEq (C : Nat → Nat → R) : det k (updRow (mix m σ C) m (C l)) = det k (mix m σ' C) :=
        det_congr k fun i _ j _ => by
          show (if i = m then C l j else if i < m then matMul k A C i j else C (σ i) j) =
            if i < m then matMul k A C i j else C (if i = m then l else σ i) j
          if hEq : i = m then rw [hEq, ite_pos rfl, ite_neg (Nat.lt_irrefl m), ite_pos rfl]
          else if hLt : i < m then rw [ite_neg hEq, ite_pos hLt, ite_pos hLt]
          else rw [ite_neg hEq, ite_neg hLt, ite_neg hLt, ite_neg hEq]
      rw [hMixEq B, hMixEq idMat,
        ihm σ' (Nat.le_of_succ_le hmk) (fun i hmi hik => by
          dsimp only [σ']; split
          · exact hl
          · next hne => exact hσ i (by omega) hik),
        LawfulCommRing.mul_assoc]
  have hAllB : det k (matMul k A B) = det k (mix k (fun i => i) B) :=
    det_congr k fun i hi _ _ => by dsimp only [mix]; rw [ite_pos hi]
  have hAllI : det k (mix k (fun i => i) idMat) = det k A :=
    det_congr k fun i hi j hj => by
      dsimp only [mix]; rw [ite_pos hi]; unfold matMul idMat
      rw [rangeSum_single hj _ fun l _ hne => by rw [ite_neg hne, LawfulCommRing.mul_zero]]
      rw [ite_pos rfl, LawfulCommRing.mul_one]
  rw [hAllB, hStage k (fun i => i) (Nat.le_refl k)
      (fun _ hle hlt => absurd hlt (Nat.not_lt_of_ge hle)), hAllI]

end Ring
end Mat


end Qsag

namespace Qsag.Math
/-! ## 2. Constructive Ring and Field Isomorphisms (`RingIso`, `FieldIso`) -/

/-- Constructive two-sided commutative ring isomorphism (`R ≃+* S`) preserving `0, 1, +, -, sub, *`. -/
structure RingIso (R S : Type) [CommRingOps R] [CommRingOps S] where
  toFun : R → S
  invFun : S → R
  left_inv : ∀ x : R, invFun (toFun x) = x
  right_inv : ∀ y : S, toFun (invFun y) = y
  map_zero : toFun CommRingOps.zero = CommRingOps.zero
  map_one : toFun CommRingOps.one = CommRingOps.one
  map_add : ∀ x y : R, toFun (CommRingOps.add x y) = CommRingOps.add (toFun x) (toFun y)
  map_neg : ∀ x : R, toFun (CommRingOps.neg x) = CommRingOps.neg (toFun x)
  map_sub : ∀ x y : R, toFun (CommRingOps.sub x y) = CommRingOps.sub (toFun x) (toFun y)
  map_mul : ∀ x y : R, toFun (CommRingOps.mul x y) = CommRingOps.mul (toFun x) (toFun y)

/-- Constructive two-sided field isomorphism extending `RingIso F G` with total `LawfulField.inv` preservation. -/
structure FieldIso (F G : Type) [LawfulField F] [LawfulField G] extends RingIso F G where
  map_inv : ∀ x : F, toFun (LawfulField.inv x) = LawfulField.inv (toFun x)

theorem RingIso.toFun_injective {R S : Type} [CommRingOps R] [CommRingOps S]
    (φ : RingIso R S) {x y : R} (h : φ.toFun x = φ.toFun y) : x = y := by
  have hInv := congrArg φ.invFun h
  rw [φ.left_inv, φ.left_inv] at hInv
  exact hInv

theorem RingIso.map_eq_zero_iff {R S : Type} [CommRingOps R] [CommRingOps S]
    (φ : RingIso R S) (x : R) :
    φ.toFun x = CommRingOps.zero ↔ x = CommRingOps.zero := by
  constructor
  · intro h
    apply φ.toFun_injective
    rw [h, φ.map_zero]
  · rintro rfl
    exact φ.map_zero

def RingIso.refl (R : Type) [CommRingOps R] : RingIso R R where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_zero := rfl
  map_one := rfl
  map_add _ _ := rfl
  map_neg _ := rfl
  map_sub _ _ := rfl
  map_mul _ _ := rfl

def RingIso.symm {R S : Type} [CommRingOps R] [CommRingOps S]
    (φ : RingIso R S) : RingIso S R where
  toFun := φ.invFun
  invFun := φ.toFun
  left_inv := φ.right_inv
  right_inv := φ.left_inv
  map_zero := by
    have h := congrArg φ.invFun φ.map_zero
    rw [φ.left_inv] at h
    exact h.symm
  map_one := by
    have h := congrArg φ.invFun φ.map_one
    rw [φ.left_inv] at h
    exact h.symm
  map_add x y := by
    apply φ.toFun_injective
    rw [φ.right_inv, φ.map_add, φ.right_inv, φ.right_inv]
  map_neg x := by
    apply φ.toFun_injective
    rw [φ.right_inv, φ.map_neg, φ.right_inv]
  map_sub x y := by
    apply φ.toFun_injective
    rw [φ.right_inv, φ.map_sub, φ.right_inv, φ.right_inv]
  map_mul x y := by
    apply φ.toFun_injective
    rw [φ.right_inv, φ.map_mul, φ.right_inv, φ.right_inv]

def RingIso.trans {R S T : Type} [CommRingOps R] [CommRingOps S] [CommRingOps T]
    (φ : RingIso R S) (ψ : RingIso S T) : RingIso R T where
  toFun x := ψ.toFun (φ.toFun x)
  invFun z := φ.invFun (ψ.invFun z)
  left_inv x := by rw [ψ.left_inv, φ.left_inv]
  right_inv z := by rw [φ.right_inv, ψ.right_inv]
  map_zero := by rw [φ.map_zero, ψ.map_zero]
  map_one := by rw [φ.map_one, ψ.map_one]
  map_add x y := by rw [φ.map_add, ψ.map_add]
  map_neg x := by rw [φ.map_neg, ψ.map_neg]
  map_sub x y := by rw [φ.map_sub, ψ.map_sub]
  map_mul x y := by rw [φ.map_mul, ψ.map_mul]

/-- **Automatic Inverse Preservation (`RingIso.toFieldIso`)**:
    Every `RingIso F G` between two `LawfulField`s preserves `LawfulField.inv` for all `x : F`:
    at `0` by the class law `inv 0 = 0`, elsewhere by uniqueness of multiplicative inverses. -/
def RingIso.toFieldIso {F G : Type} [LawfulField F] [LawfulField G] [DecidableEq F]
    (φ : RingIso F G) : FieldIso F G where
  toRingIso := φ
  map_inv x := by
    by_cases hx : x = CommRingOps.zero
    · rw [hx, LawfulField.inv_zero, φ.map_zero, LawfulField.inv_zero]
    · have hFxNe : φ.toFun x ≠ CommRingOps.zero := fun h0 => hx ((φ.map_eq_zero_iff x).mp h0)
      have hProd : CommRingOps.mul (φ.toFun x) (φ.toFun (LawfulField.inv x)) = CommRingOps.one := by
        rw [← φ.map_mul, LawfulField.mul_inv_cancel hx, φ.map_one]
      have hLeft := congrArg (CommRingOps.mul (LawfulField.inv (φ.toFun x))) hProd
      rw [← LawfulCommRing.mul_assoc,
          LawfulCommRing.mul_comm (LawfulField.inv (φ.toFun x)) (φ.toFun x),
          LawfulField.mul_inv_cancel hFxNe,
          LawfulCommRing.one_mul,
          LawfulCommRing.mul_one] at hLeft
      exact hLeft

def FieldIso.refl (F : Type) [LawfulField F] : FieldIso F F where
  toRingIso := RingIso.refl F
  map_inv _ := rfl

def FieldIso.symm {F G : Type} [LawfulField F] [LawfulField G]
    (φ : FieldIso F G) : FieldIso G F where
  toRingIso := φ.toRingIso.symm
  map_inv y := by
    apply φ.toRingIso.toFun_injective
    dsimp only [RingIso.symm]
    rw [φ.right_inv, φ.map_inv, φ.right_inv]

def FieldIso.trans {F G H : Type} [LawfulField F] [LawfulField G] [LawfulField H]
    (φ : FieldIso F G) (ψ : FieldIso G H) : FieldIso F H where
  toRingIso := φ.toRingIso.trans ψ.toRingIso
  map_inv x := by
    dsimp only [RingIso.trans]
    rw [φ.map_inv, ψ.map_inv]


end Qsag.Math

namespace Qsag
set_option autoImplicit false
theorem nodup_filter_bool {α : Type} (p : α → Bool) {l : List α} (h : l.Nodup) : (l.filter p).Nodup := List.Pairwise.filter p h
open CommRingOps RoundPoly UPoly

/-- A ring in which `1 ≠ 0`. -/
class NontrivialRing (D : Type) [CommRingOps D] : Prop where
  one_ne_zero : (one : D) ≠ zero

instance (F : Type) [LawfulField F] : NontrivialRing F := ⟨LawfulField.one_ne_zero⟩

/-- A numerator and a nonzero denominator. -/
structure PreFrac (D : Type) [CommRingOps D] where
  num : D
  den : D
  den_ne : den ≠ zero

section Domain
variable {D : Type} [LawfulCommRing D] [NoZeroDivisors D]

theorem mul_ne_zero' {a b : D} (ha : a ≠ zero) (hb : b ≠ zero) : mul a b ≠ zero := fun h =>
  (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h).elim ha hb

theorem mul_right_cancel' {x y d : D} (hd : d ≠ zero) (h : mul x d = mul y d) : x = y := by
  have h0 : mul (sub x y) d = zero := by
    rw [LawfulCommRing.sub_mul, h, LawfulCommRing.sub_self]
  rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h0 with h1 | h1
  · exact LawfulCommRing.sub_eq_zero_iff.mp h1
  · exact absurd h1 hd

end Domain

namespace PreFrac
variable {D : Type} [LawfulCommRing D] [NoZeroDivisors D]

/-- Equality of fractions by cross-multiplication. -/
def Rel (a b : PreFrac D) : Prop := mul a.num b.den = mul b.num a.den

theorem Rel.trans' {a b c : PreFrac D} (hab : Rel a b) (hbc : Rel b c) : Rel a c := by
  unfold Rel at *
  apply mul_right_cancel' b.den_ne
  have e1 : mul (mul a.num c.den) b.den = mul (mul a.num b.den) c.den := by constructive_ring
  have e2 : mul (mul b.num a.den) c.den = mul (mul b.num c.den) a.den := by constructive_ring
  have e3 : mul (mul c.num b.den) a.den = mul (mul c.num a.den) b.den := by constructive_ring
  rw [e1, hab, e2, hbc, e3]

instance setoid : Setoid (PreFrac D) where
  r := Rel
  iseqv := ⟨fun _ => by unfold Rel; rfl, fun h => by unfold Rel at *; exact h.symm, Rel.trans'⟩

def padd (a b : PreFrac D) : PreFrac D :=
  ⟨add (mul a.num b.den) (mul b.num a.den), mul a.den b.den, mul_ne_zero' a.den_ne b.den_ne⟩

def pmul (a b : PreFrac D) : PreFrac D :=
  ⟨mul a.num b.num, mul a.den b.den, mul_ne_zero' a.den_ne b.den_ne⟩

def pneg (a : PreFrac D) : PreFrac D := ⟨neg a.num, a.den, a.den_ne⟩

def pinv [DecidableEq D] [NontrivialRing D] (a : PreFrac D) : PreFrac D :=
  if h : a.num = zero then ⟨zero, one, NontrivialRing.one_ne_zero⟩ else ⟨a.den, a.num, h⟩

theorem padd_rel {a a' b b' : PreFrac D} (ha : Rel a a') (hb : Rel b b') :
    Rel (padd a b) (padd a' b') := by
  unfold Rel at *
  show mul (add (mul a.num b.den) (mul b.num a.den)) (mul a'.den b'.den) =
    mul (add (mul a'.num b'.den) (mul b'.num a'.den)) (mul a.den b.den)
  have e1 : mul (add (mul a.num b.den) (mul b.num a.den)) (mul a'.den b'.den) =
      add (mul (mul a.num a'.den) (mul b.den b'.den))
        (mul (mul b.num b'.den) (mul a.den a'.den)) := by constructive_ring
  rw [e1, ha, hb]; constructive_ring

theorem pmul_rel {a a' b b' : PreFrac D} (ha : Rel a a') (hb : Rel b b') :
    Rel (pmul a b) (pmul a' b') := by
  unfold Rel at *
  show mul (mul a.num b.num) (mul a'.den b'.den) = mul (mul a'.num b'.num) (mul a.den b.den)
  have e1 : mul (mul a.num b.num) (mul a'.den b'.den) =
      mul (mul a.num a'.den) (mul b.num b'.den) := by constructive_ring
  rw [e1, ha, hb]; constructive_ring

omit [NoZeroDivisors D] in
theorem pneg_rel {a a' : PreFrac D} (ha : Rel a a') : Rel (pneg a) (pneg a') := by
  unfold Rel at *
  show mul (neg a.num) a'.den = mul (neg a'.num) a.den
  rw [LawfulCommRing.neg_mul, ha, LawfulCommRing.neg_mul]

theorem pinv_rel [DecidableEq D] [NontrivialRing D] {a a' : PreFrac D} (ha : Rel a a') :
    Rel (pinv a) (pinv a') := by
  unfold Rel at ha
  have hiff : a.num = zero ↔ a'.num = zero := by
    constructor
    · intro h
      rw [h, LawfulCommRing.zero_mul] at ha
      exact (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero ha.symm).elim id
        (fun e => absurd e a.den_ne)
    · intro h
      rw [h, LawfulCommRing.zero_mul] at ha
      exact (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero ha).elim id
        (fun e => absurd e a'.den_ne)
  unfold pinv
  split
  · next h =>
    split
    · rfl
    · next h' => exact absurd (hiff.mp h) h'
  · next h =>
    split
    · next h' => exact absurd (hiff.mpr h') h
    · show mul a.den a'.num = mul a'.den a.num
      rw [LawfulCommRing.mul_comm, ← ha, LawfulCommRing.mul_comm]

end PreFrac

/-- The fraction field of the integral domain `D`. -/
abbrev Frac (D : Type) [LawfulCommRing D] [NoZeroDivisors D] : Type :=
  Quotient (PreFrac.setoid (D := D))

namespace Frac
variable {D : Type} [LawfulCommRing D] [NoZeroDivisors D] [DecidableEq D] [NontrivialRing D]
open PreFrac

/-- The class of `n/d`. -/
def mk (a : PreFrac D) : Frac D := Quotient.mk _ a

omit [DecidableEq D] [NontrivialRing D] in
theorem sound {a b : PreFrac D} (h : Rel a b) : mk a = mk b := Quotient.sound h

omit [DecidableEq D] [NontrivialRing D] in
theorem exact {a b : PreFrac D} (h : mk a = mk b) : Rel a b := Quotient.exact h

instance : DecidableEq (Frac D) := fun x y =>
  Quotient.recOnSubsingleton₂ x y fun a b =>
    if h : mul a.num b.den = mul b.num a.den then .isTrue (Quotient.sound (by change Rel a b; unfold Rel; exact h))
    else .isFalse (fun e => h (by have hr : Rel a b := Quotient.exact e; unfold Rel at hr; exact hr))

def fadd (x y : Frac D) : Frac D :=
  Quotient.liftOn₂ x y (fun a b => mk (padd a b)) (fun _ _ _ _ ha hb => sound (padd_rel ha hb))

def fmul (x y : Frac D) : Frac D :=
  Quotient.liftOn₂ x y (fun a b => mk (pmul a b)) (fun _ _ _ _ ha hb => sound (pmul_rel ha hb))

def fneg (x : Frac D) : Frac D :=
  Quotient.liftOn x (fun a => mk (pneg a)) (fun _ _ ha => sound (pneg_rel ha))

def finv (x : Frac D) : Frac D :=
  Quotient.liftOn x (fun a => mk (pinv a)) (fun _ _ ha => sound (pinv_rel ha))

/-- The class of `c/1`. -/
def ofD (c : D) : Frac D := mk ⟨c, one, NontrivialRing.one_ne_zero⟩

omit [DecidableEq D] [NontrivialRing D] in
theorem ind₁ {p : Frac D → Prop} (h : ∀ a, p (mk a)) : ∀ x, p x := Quotient.ind h

omit [DecidableEq D] [NontrivialRing D] in
theorem ind₂ {p : Frac D → Frac D → Prop} (h : ∀ a b, p (mk a) (mk b)) : ∀ x y, p x y :=
  fun x y => Quotient.inductionOn₂ x y h

omit [DecidableEq D] [NontrivialRing D] in
theorem ind₃ {p : Frac D → Frac D → Frac D → Prop}
    (h : ∀ a b c, p (mk a) (mk b) (mk c)) : ∀ x y z, p x y z :=
  fun x y z => Quotient.inductionOn₃ x y z h

instance instLawfulField : LawfulField (Frac D) where
  zero := ofD zero
  one := ofD one
  add := fadd
  mul := fmul
  neg := fneg
  sub x y := fadd x (fneg y)
  inv := finv
  add_assoc := ind₃ fun a b c => by
    exact sound (by unfold Rel padd; dsimp only; constructive_ring)
  add_comm := ind₂ fun a b => by exact sound (by unfold Rel padd; dsimp only; constructive_ring)
  zero_add := ind₁ fun a => by exact sound (by unfold Rel padd; dsimp only; constructive_ring)
  add_zero := ind₁ fun a => by exact sound (by unfold Rel padd; dsimp only; constructive_ring)
  add_left_neg := ind₁ fun a => by
    exact sound (by unfold Rel padd pneg; dsimp only; constructive_ring)
  sub_eq_add_neg _ _ := by rfl
  mul_assoc := ind₃ fun a b c => by
    exact sound (by unfold Rel pmul; dsimp only; constructive_ring)
  mul_comm := ind₂ fun a b => by exact sound (by unfold Rel pmul; dsimp only; constructive_ring)
  one_mul := ind₁ fun a => by exact sound (by unfold Rel pmul; dsimp only; constructive_ring)
  mul_one := ind₁ fun a => by exact sound (by unfold Rel pmul; dsimp only; constructive_ring)
  left_distrib := ind₃ fun a b c => by
    exact sound (by unfold Rel pmul padd; dsimp only; constructive_ring)
  right_distrib := ind₃ fun a b c => by
    exact sound (by unfold Rel pmul padd; dsimp only; constructive_ring)
  zero_ne_one := by
    intro h
    have h' : mul (zero : D) one = mul one one := exact h
    rw [LawfulCommRing.zero_mul, LawfulCommRing.mul_one] at h'
    exact NontrivialRing.one_ne_zero h'.symm
  inv_zero := by
    show mk (pinv ⟨zero, one, NontrivialRing.one_ne_zero⟩) = mk ⟨zero, one, NontrivialRing.one_ne_zero⟩
    unfold pinv
    split
    · rfl
    · next h => exact absurd rfl h
  mul_inv_cancel := by
    intro x
    induction x using ind₁ with | h a =>
    intro hx
    have hn : a.num ≠ zero := fun e => hx (sound (by
      show mul a.num one = mul zero a.den
      rw [e, LawfulCommRing.zero_mul, LawfulCommRing.zero_mul]))
    exact sound (by
      unfold pinv; split
      · next h => exact absurd h hn
      · show mul (mul a.num a.den) one = mul one (mul a.den a.num)
        constructive_ring)

/-- The embedding `D → Frac D`. -/
def of : RingHom D (Frac D) where
  toFun := ofD
  map_zero := by rfl
  map_one := by rfl
  map_add a b := sound (by
    show mul (add a b) (mul one one) = mul (add (mul a one) (mul b one)) one
    constructive_ring)
  map_mul a b := sound (by
    show mul (mul a b) (mul one one) = mul (mul a b) one
    constructive_ring)

theorem of_injective {a b : D} (h : (of (D := D)).toFun a = (of (D := D)).toFun b) : a = b := by
  have h' : mul a one = mul b one := exact h
  rwa [LawfulCommRing.mul_one, LawfulCommRing.mul_one] at h'

end Frac

/-! ## Base change of coefficients -/

namespace UPoly

section Map
variable {R S T : Type} [LawfulCommRing R] [DecidableEq R] [LawfulCommRing S] [DecidableEq S]
  [LawfulCommRing T]

/-- Coefficientwise base change `R[X] → S[X]`. -/
@[expose] def mapHom (φ : RingHom R S) : RingHom (UPoly R) (UPoly S) := eval₂Hom (CHom.comp φ) X

theorem mapHom_apply (φ : RingHom R S) (p : UPoly R) :
    (mapHom φ).toFun p = ofList (p.coeffs.map φ.toFun) := by
  show evalCoeffs (p.coeffs.map (CHom.comp φ).toFun) X = _
  generalize p.coeffs = l
  induction l with
  | nil => rfl
  | cons c cs ih =>
    show add (C (φ.toFun c)) (mul X (evalCoeffs (cs.map (CHom.comp φ).toFun) X)) =
      ofList (φ.toFun c :: cs.map φ.toFun)
    rw [ih, ofList_cons]

theorem coeffAt_mapHom (φ : RingHom R S) (p : UPoly R) (k : Nat) :
    coeffAt ((mapHom φ).toFun p).coeffs k = φ.toFun (coeffAt p.coeffs k) := by
  rw [mapHom_apply, coeffAt_ofList, RingHom.coeffAt_map]

theorem mapHom_C (φ : RingHom R S) (c : R) : (mapHom φ).toFun (C c) = C (φ.toFun c) :=
  eval₂_C _ _ _

theorem mapHom_inj (φ : RingHom R S) (hinj : ∀ x, φ.toFun x = zero → x = zero)
    (p : UPoly R) (h : (mapHom φ).toFun p = zero) : p = zero :=
  ext_coeffAt fun k => by
    have := congrArg (fun q : UPoly S => coeffAt q.coeffs k) h
    simp only [coeffAt_mapHom, coeffs_zero, coeffAt_nil] at this
    rw [coeffs_zero, coeffAt_nil]; exact hinj _ this

theorem natDeg_mapHom_le (φ : RingHom R S) (p : UPoly R) :
    ((mapHom φ).toFun p).natDeg ≤ p.natDeg :=
  natDeg_le_of_coeffAt _ _ (fun k hk => by
    rw [coeffAt_mapHom, p.coeffAt_eq_zero_of_natDeg_lt hk, φ.map_zero])

theorem natDeg_mapHom (φ : RingHom R S) (hinj : ∀ x, φ.toFun x = zero → x = zero)
    (p : UPoly R) : ((mapHom φ).toFun p).natDeg = p.natDeg := by
  apply Nat.le_antisymm (natDeg_mapHom_le φ p)
  apply Decidable.byContradiction
  intro hlt
  have hz := ((mapHom φ).toFun p).coeffAt_eq_zero_of_natDeg_lt (Nat.lt_of_not_le hlt)
  rw [coeffAt_mapHom] at hz
  have hp : p ≠ zero := fun e => by
    rw [e] at hlt; exact hlt (Nat.zero_le _)
  exact lead_ne_zero hp ((lead_eq p).trans (hinj _ hz))

theorem eval₂_mapHom (ψ : RingHom S T) (s : T) (φ : RingHom R S) (p : UPoly R) :
    eval₂ ψ s ((mapHom φ).toFun p) = eval₂ (ψ.comp φ) s p := by
  rw [mapHom_apply, eval₂_ofList, List.map_map]; rfl

theorem eval_mapHom (φ : RingHom R S) (p : UPoly R) (y : R) :
    ((mapHom φ).toFun p).eval (φ.toFun y) = φ.toFun (p.eval y) := by
  show eval₂ (RingHom.id S) (φ.toFun y) ((mapHom φ).toFun p) = φ.toFun (eval₂ (RingHom.id R) y p)
  rw [eval₂_mapHom, hom_eval₂]; rfl

/-- Evaluating a doubly base-changed polynomial at the image of a point. -/
theorem eval₂_mapHom_mapHom (φ : RingHom R S) (Q : UPoly (UPoly R)) (y z : R) :
    eval₂ (evalHom (φ.toFun y)) (φ.toFun z) ((mapHom (mapHom φ)).toFun Q) =
      φ.toFun (eval₂ (evalHom y) z Q) := by
  rw [eval₂_mapHom, hom_eval₂]
  show evalCoeffs (Q.coeffs.map _) _ = evalCoeffs (Q.coeffs.map _) _
  congr 1
  apply List.map_congr_left
  intro q _
  exact eval_mapHom φ q y

/-- Base change does not raise the total degree. -/
theorem wdeg_mapHom_mapHom_le (φ : RingHom R S) (Q : UPoly (UPoly R)) :
    ((mapHom (mapHom φ)).toFun Q).wdeg natDeg 1 ≤ Q.wdeg natDeg 1 := by
  apply wdeg_le
  intro k hk
  rw [coeffAt_mapHom] at hk ⊢
  have hne : coeffAt Q.coeffs k ≠ zero := fun e => hk (by rw [e, (mapHom φ).map_zero])
  have := le_wdeg natDeg 1 Q k hne
  have := natDeg_mapHom_le φ (coeffAt Q.coeffs k)
  omega

end Map


/-- The product of a list of polynomials. -/
def prodList {R : Type} [LawfulCommRing R] [DecidableEq R] : List (UPoly R) → UPoly R
  | [] => one
  | p :: ps => mul p (prodList ps)

end UPoly

instance (F : Type) [LawfulField F] [DecidableEq F] : NoZeroDivisors (UPoly F) :=
  letI : NoZeroDivisors F := LawfulField.toNoZeroDivisors F
  inferInstance

instance (R : Type) [LawfulCommRing R] [DecidableEq R] [NontrivialRing R] :
    NontrivialRing (UPoly R) where
  one_ne_zero := fun e => NontrivialRing.one_ne_zero (D := R) (by
    have := congrArg (fun p : UPoly R => coeffAt p.coeffs 0) e
    simp only [UPoly.one_eq_C, UPoly.coeffAt_C_zero, UPoly.coeffs_zero, coeffAt_nil] at this
    exact this)

/-- Rational functions `F(X)`. -/
abbrev RatFunc (F : Type) [LawfulField F] [DecidableEq F] := Frac (UPoly F)

namespace UPoly
variable {R : Type} [LawfulCommRing R] [DecidableEq R]

theorem natDeg_one : (one : UPoly R).natDeg = 0 := by
  have := trimPoly_length_le [(one : R)]
  show (ofList [one]).coeffs.length - 1 = 0
  rw [coeffs_ofList]
  simp only [List.length_cons, List.length_nil] at this; omega

theorem prodList_ne_zero [NoZeroDivisors R] [NontrivialRing R] :
    ∀ ps : List (UPoly R), (∀ p ∈ ps, p ≠ zero) → prodList ps ≠ zero
  | [], _ => NontrivialRing.one_ne_zero
  | p :: ps, h => mul_ne_zero' (h p (.head _))
      (prodList_ne_zero ps (fun q hq => h q (.tail _ hq)))

theorem eval_prodList_eq_zero (y : R) : ∀ ps : List (UPoly R),
    (∃ p ∈ ps, p.eval y = zero) → (prodList ps).eval y = zero
  | [], h => by obtain ⟨_, hp, _⟩ := h; cases hp
  | p :: ps, h => by
    show (evalHom y).toFun (mul p (prodList ps)) = zero
    rw [(evalHom y).map_mul]
    obtain ⟨q, hq, hz⟩ := h
    cases hq with
    | head => rw [evalHom_apply, hz, LawfulCommRing.zero_mul]
    | tail _ hq' =>
      rw [evalHom_apply, evalHom_apply, eval_prodList_eq_zero y ps ⟨q, hq', hz⟩,
        LawfulCommRing.mul_zero]

end UPoly

/-! ## Squarefree factors and `[CWYZ26]` Lemma 4.3 -/

/-! ## Dynamic GCD splitting over a field -/

namespace UPoly
variable {K : Type} [LawfulField K] [DecidableEq K]

local instance : NoZeroDivisors K := LawfulField.toNoZeroDivisors K

/-- Euclidean division in `K[Z]`. -/
def divMod (a b : UPoly K) : UPoly K × UPoly K :=
  (ofList (polyDivMod a.coeffs b.coeffs).1, ofList (polyDivMod a.coeffs b.coeffs).2)

theorem divMod_spec (a b : UPoly K) (hb : b ≠ zero) :
    a = add (mul (divMod a b).1 b) (divMod a b).2 ∧
      (divMod a b).2.coeffs.length < b.coeffs.length := by
  have hb' : trimPoly b.coeffs ≠ [] := by
    rw [b.trimmed]; exact fun e => hb ((eq_zero_iff b).mpr e)
  have h := polyDivMod_spec a.coeffs b.coeffs hb'
  unfold divMod
  generalize polyDivMod a.coeffs b.coeffs = qr at h
  obtain ⟨q, r⟩ := qr
  obtain ⟨hq, hr, heq, hlen⟩ := h
  have hq' : trimPoly q = q := hq
  have hr' : trimPoly r = r := hr
  refine ⟨ext ?_, ?_⟩
  · show a.coeffs = pAdd (pMul (trimPoly q) b.coeffs) (trimPoly r)
    rw [hq', hr', ← heq, a.trimmed]
  · show (trimPoly r).length < b.coeffs.length
    rw [hr']; rwa [b.trimmed] at hlen

/-- Extended Euclid: `(g, u, v)` with `u·a + v·b = g` and `g` dividing both. -/
def xgcdAux : Nat → UPoly K → UPoly K → UPoly K × UPoly K × UPoly K
  | 0, a, _ => (a, one, zero)
  | fuel + 1, a, b =>
    if b = zero then (a, one, zero)
    else
      let r := xgcdAux fuel b (divMod a b).2
      (r.1, r.2.2, sub r.2.1 (mul r.2.2 (divMod a b).1))

theorem xgcdAux_spec : ∀ (fuel : Nat) (a b : UPoly K), b.coeffs.length ≤ fuel →
    add (mul (xgcdAux fuel a b).2.1 a) (mul (xgcdAux fuel a b).2.2 b) = (xgcdAux fuel a b).1 ∧
      (∃ s, a = mul (xgcdAux fuel a b).1 s) ∧ (∃ t, b = mul (xgcdAux fuel a b).1 t)
  | 0, a, b, h => by
    have hb : b = zero := (eq_zero_iff b).mpr (List.eq_nil_of_length_eq_zero (by omega))
    subst hb
    exact ⟨by show add (mul one a) (mul zero zero) = a; constructive_ring,
      ⟨one, (LawfulCommRing.mul_one a).symm⟩, ⟨zero, (LawfulCommRing.mul_zero a).symm⟩⟩
  | fuel + 1, a, b, h => by
    unfold xgcdAux
    split
    · next hb =>
      subst hb
      exact ⟨by show add (mul one a) (mul zero zero) = a; constructive_ring,
        ⟨one, (LawfulCommRing.mul_one a).symm⟩, ⟨zero, (LawfulCommRing.mul_zero a).symm⟩⟩
    · next hb =>
      obtain ⟨hdiv, hlen⟩ := divMod_spec a b hb
      obtain ⟨hbez, ⟨s, hs⟩, ⟨t, ht⟩⟩ := xgcdAux_spec fuel b (divMod a b).2 (by omega)
      generalize xgcdAux fuel b (divMod a b).2 = res at hbez hs ht
      generalize (divMod a b).1 = q at hdiv
      generalize (divMod a b).2 = r at hdiv hbez ht
      refine ⟨?_, ⟨add (mul q s) t, ?_⟩, ⟨s, hs⟩⟩
      · show add (mul res.2.2 a) (mul (sub res.2.1 (mul res.2.2 q)) b) = res.1
        rw [← hbez, hdiv]; constructive_ring
      · rw [hdiv, hs, ht]; constructive_ring

/-- A gcd of `R` and `G` with its Bézout cofactors. -/
def xgcd (R G : UPoly K) : UPoly K × UPoly K × UPoly K := xgcdAux G.coeffs.length R G

/-- **D5 splitting step.** Testing `G` against a modulus `R ≠ 0` has three outcomes: `G` is
    invertible modulo `R`; or `R` divides `G`; or `R = g·q` splits into two factors of
    positive degree, with `deg g + deg q = deg R`, so the degree sum of a factor list is
    preserved and its length strictly grows. -/
theorem d5_split (R G : UPoly K) (hR : R ≠ zero) :
    (∃ u v, add (mul u R) (mul v G) = one) ∨ (∃ t, G = mul R t) ∨
      (∃ g q, R = mul g q ∧ 0 < g.natDeg ∧ 0 < q.natDeg ∧ g.natDeg + q.natDeg = R.natDeg ∧
        ∃ t, G = mul g t) := by
  obtain ⟨hbez, ⟨s, hs⟩, ⟨t, ht⟩⟩ := xgcdAux_spec G.coeffs.length R G (Nat.le_refl _)
  generalize (xgcdAux G.coeffs.length R G).1 = g at hbez hs ht
  generalize (xgcdAux G.coeffs.length R G).2.1 = u at hbez
  generalize (xgcdAux G.coeffs.length R G).2.2 = v at hbez
  have hg : g ≠ zero := fun e => hR (by rw [hs, e, LawfulCommRing.zero_mul])
  have hs0 : s ≠ zero := fun e => hR (by rw [hs, e, LawfulCommRing.mul_zero])
  have hdeg : R.natDeg = g.natDeg + s.natDeg := by rw [hs]; exact natDeg_mul hg hs0
  have unit : ∀ p : UPoly K, p ≠ zero → p.natDeg = 0 → mul p (C (LawfulField.inv p.lead)) = one := by
    intro p hp hd
    have hpC : p = C p.lead := ext_coeffAt fun k => by
      cases k with
      | zero => rw [coeffAt_C_zero]; rw [lead_eq, hd]
      | succ k => rw [coeffAt_C_succ]; exact p.coeffAt_eq_zero_of_natDeg_lt (by omega)
    have h1 : mul (C p.lead) (C (LawfulField.inv p.lead)) = C (mul p.lead (LawfulField.inv p.lead)) :=
      (CHom.map_mul _ _).symm
    rw [LawfulField.mul_inv_cancel (lead_ne_zero hp)] at h1
    exact (congrArg (fun x => mul x (C (LawfulField.inv p.lead))) hpC).trans h1
  if h0 : g.natDeg = 0 then
    refine .inl ⟨mul (C (LawfulField.inv g.lead)) u, mul (C (LawfulField.inv g.lead)) v, ?_⟩
    rw [← unit g hg h0, ← hbez]; constructive_ring
  else if h1 : s.natDeg = 0 then
    refine .inr (.inl ⟨mul (C (LawfulField.inv s.lead)) t, ?_⟩)
    have hu := unit s hs0 h1
    have : mul R (mul (C (LawfulField.inv s.lead)) t) =
        mul g (mul (mul s (C (LawfulField.inv s.lead))) t) := by rw [hs]; constructive_ring
    rw [this, hu, ht]; constructive_ring
  else
    exact .inr (.inr ⟨g, s, hs, by omega, by omega, hdeg.symm, t, ht⟩)

end UPoly

/-! ## Witnesses -/

end Qsag

namespace Qsag
open CommRingOps RoundPoly UPoly
namespace SylElim
theorem natRangeSum_const_add :
    ∀ (n c : Nat), Mat.natRangeSum n (fun i => c + i) = n * c + Mat.natRangeSum n (fun i => i)
  | 0, c => by show 0 = 0 * c + 0; omega
  | n + 1, c => by
    show Mat.natRangeSum n (fun i => c + i) + (c + n) = (n + 1) * c + (Mat.natRangeSum n (fun i => i) + n)
    rw [natRangeSum_const_add n c, Nat.succ_mul]; omega

theorem natRangeSum_split :
    ∀ (m N : Nat) (f : Nat → Nat),
      Mat.natRangeSum (m + N) f = Mat.natRangeSum m f + Mat.natRangeSum N (fun r => f (m + r))
  | m, 0, _ => by show Mat.natRangeSum m _ = Mat.natRangeSum m _ + 0; omega
  | m, N + 1, f => by
    show Mat.natRangeSum (m + N) f + f (m + N) =
      Mat.natRangeSum m f + (Mat.natRangeSum N (fun r => f (m + r)) + f (m + N))
    rw [natRangeSum_split m N f]; omega

theorem natRangeSum_split_id (m N : Nat) :
    Mat.natRangeSum (m + N) (fun i => i) =
      Mat.natRangeSum m (fun i => i) + Mat.natRangeSum N (fun i => i) + m * N := by
  rw [natRangeSum_split m N (fun i => i), natRangeSum_const_add N m, Nat.mul_comm N m]; omega

theorem rangeSum_split {R : Type} [LawfulCommRing R] (m : Nat) :
    ∀ (N : Nat) (f : Nat → R),
      Mat.rangeSum (m + N) f = add (Mat.rangeSum m f) (Mat.rangeSum N (fun r => f (m + r)))
  | 0, f => by show Mat.rangeSum m f = add (Mat.rangeSum m f) zero; rw [LawfulCommRing.add_zero]
  | N + 1, f => by
    show add (Mat.rangeSum (m + N) f) (f (m + N)) =
      add (Mat.rangeSum m f) (add (Mat.rangeSum N (fun r => f (m + r))) (f (m + N)))
    rw [rangeSum_split m N f, LawfulCommRing.add_assoc]

end SylElim
namespace RingHom

theorem map_npow {R S : Type} [LawfulCommRing R] [LawfulCommRing S] (φ : RingHom R S) (a : R) :
    ∀ k : Nat, φ.toFun (CRing.npow a k) = CRing.npow (φ.toFun a) k
  | 0 => φ.map_one
  | k + 1 => by
    show φ.toFun (mul (CRing.npow a k) a) = mul (CRing.npow (φ.toFun a) k) (φ.toFun a)
    rw [φ.map_mul, map_npow φ a k]

end RingHom

theorem npow_mul_self {R : Type} [LawfulCommRing R] (s : R) :
    ∀ j : Nat, CRing.npow (mul s s) j = CRing.npow s (2 * j)
  | 0 => rfl
  | j + 1 => by
    show mul (CRing.npow (mul s s) j) (mul s s) = mul (mul (CRing.npow s (2 * j)) s) s
    rw [npow_mul_self s j, LawfulCommRing.mul_assoc]

theorem degFn_npow_le {R : Type} [LawfulCommRing R] {δ : R → Nat} (hδ : DegFn δ)
    (h1 : δ one = 0) (a : R) (B : Nat) (ha : δ a ≤ B) : ∀ k : Nat, δ (CRing.npow a k) ≤ k * B
  | 0 => by show δ one ≤ 0 * B; rw [h1]; exact Nat.zero_le _
  | k + 1 => by
    have h := hδ.mul_le (CRing.npow a k) a
    have ih := degFn_npow_le hδ h1 a B ha k
    show δ (mul (CRing.npow a k) a) ≤ (k + 1) * B
    rw [Nat.succ_mul]; omega

namespace UPoly
variable {R : Type} [LawfulCommRing R] [DecidableEq R]
theorem mapHom_X {S : Type} [LawfulCommRing S] [DecidableEq S] (φ : RingHom R S) :
    (mapHom φ).toFun X = X := eval₂_X _ _

end UPoly


namespace Mat
@[simp] theorem natRangeSum_zero (f : Nat → Nat) : natRangeSum 0 f = 0 := by rfl
@[simp] theorem natRangeSum_succ (n : Nat) (f : Nat → Nat) : natRangeSum (n+1) f = natRangeSum n f + f n := by rfl
end Mat

namespace UPoly
variable {R : Type} [LawfulCommRing R] [DecidableEq R]
@[simp] theorem natDeg_zero : (zero : UPoly R).natDeg = 0 := by rfl
@[simp] theorem C_add_eq (a b : R) : C (add a b) = add (C a) (C b) := CHom.map_add a b
@[simp] theorem C_mul_eq (a b : R) : C (mul a b) = mul (C a) (C b) := CHom.map_mul a b
end UPoly
end Qsag

namespace Qsag
open CommRingOps RoundPoly UPoly
namespace Poly2
variable {E : Type} [LawfulField E] [DecidableEq E]
local instance : NoZeroDivisors E := LawfulField.toNoZeroDivisors E
theorem xgcd_spec (a b : UPoly E) :
    add (mul (UPoly.xgcd a b).2.1 a) (mul (UPoly.xgcd a b).2.2 b) = (UPoly.xgcd a b).1 ∧
      (∃ s, a = mul (UPoly.xgcd a b).1 s) ∧ (∃ t, b = mul (UPoly.xgcd a b).1 t) :=
  UPoly.xgcdAux_spec b.coeffs.length a b (Nat.le_refl _)

theorem eq_C_lead_of_natDeg_zero {u : UPoly E} (hd : u.natDeg = 0) : u = C u.lead :=
  ext_coeffAt fun k => by
    cases k with
    | zero => rw [coeffAt_C_zero]; rw [lead_eq, hd]
    | succ k => rw [coeffAt_C_succ]; exact u.coeffAt_eq_zero_of_natDeg_lt (by omega)

theorem divMod_exact_of_mul (g q : UPoly E) (hg : g ≠ zero) :
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

abbrev DvdU (g x : UPoly E) : Prop := ∃ q, x = mul g q

theorem dvdU_zero (g : UPoly E) : DvdU g zero :=
  ⟨zero, (LawfulCommRing.mul_zero g).symm⟩

theorem dvdU_add {g x y : UPoly E} (hx : DvdU g x) (hy : DvdU g y) : DvdU g (add x y) := by
  obtain ⟨qx, rfl⟩ := hx; obtain ⟨qy, rfl⟩ := hy
  exact ⟨add qx qy, (LawfulCommRing.left_distrib g qx qy).symm⟩

theorem dvdU_mul_right {g x : UPoly E} (hx : DvdU g x) (y : UPoly E) : DvdU g (mul x y) := by
  obtain ⟨q, rfl⟩ := hx; exact ⟨mul q y, LawfulCommRing.mul_assoc g q y⟩

theorem dvdU_trans {g' g x : UPoly E} (hg : DvdU g' g) (hx : DvdU g x) : DvdU g' x := by
  obtain ⟨t, rfl⟩ := hg; obtain ⟨q, rfl⟩ := hx
  exact ⟨mul t q, LawfulCommRing.mul_assoc g' t q⟩

theorem coeffAt_rawAddCoeffs (as bs : List (UPoly E)) (k : Nat) :
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

theorem dvdU_rawMul_lt (g : UPoly E) (bs : List (UPoly E)) (k : Nat)
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

theorem rawMul_pivot_congr (g : UPoly E) (bs : List (UPoly E)) (j₀ : Nat)
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

theorem refine_against_list :
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

theorem coeffAt_mem_or_zero :
    ∀ (cs : List (UPoly E)) (k : Nat), coeffAt cs k ∈ cs ∨ coeffAt cs k = zero
  | [], k => .inr (coeffAt_nil k)
  | _ :: _, 0 => .inl (.head _)
  | _ :: tl, k + 1 => (coeffAt_mem_or_zero tl k).elim (fun h => .inl (.tail _ h)) .inr

end Poly2
end Qsag

namespace Qsag
open CommRingOps RoundPoly
 theorem coeffAt_eq_getD {F : Type} [CommRingOps F] (cs : List F) (k : Nat) : coeffAt cs k = cs.getD k zero := by rfl
namespace Mat
variable {R : Type} [LawfulCommRing R]
@[simp] theorem rangeSum_zero (f : Nat → R) : rangeSum 0 f = zero := by rfl
@[simp] theorem rangeSum_succ (n : Nat) (f : Nat → R) : rangeSum (n+1) f = add (rangeSum n f) (f n) := by rfl
 theorem matMul_apply (k : Nat) (A B : Nat → Nat → R) (i j : Nat) : matMul k A B i j = rangeSum k (fun l => mul (A i l) (B l j)) := by rfl
omit [LawfulCommRing R] in
 theorem minor_zero_zero (M : Nat → Nat → R) (i j : Nat) : minor M 0 0 i j = M (i+1) (j+1) := by simp [minor, skipIdx]
 theorem idMat_eq (i j : Nat) : (idMat i j : R) = if i = j then one else zero := by rfl
end Mat
namespace UPoly
variable {R : Type} [LawfulCommRing R] [DecidableEq R]

 theorem eval_mul (a b : UPoly R) (x : R) : (mul a b).eval x = mul (a.eval x) (b.eval x) := (evalHom x).map_mul a b
 theorem eval_add (a b : UPoly R) (x : R) : (add a b).eval x = add (a.eval x) (b.eval x) := (evalHom x).map_add a b
 theorem C_zero_eq : (C zero : UPoly R) = zero := CHom.map_zero
end UPoly
end Qsag

namespace Qsag
open CommRingOps RoundPoly UPoly
namespace SylElim
variable {R : Type} [LawfulCommRing R] [DecidableEq R]
theorem ite_pos {α : Type} {p : Prop} [Decidable p] (hp : p) {a b : α} :
    (if p then a else b) = a := by
  split
  · rfl
  · next hn => exact absurd hp hn

theorem ite_neg {α : Type} {p : Prop} [Decidable p] (hnp : ¬ p) {a b : α} :
    (if p then a else b) = b := by
  split
  · next hp => exact absurd hp hnp
  · rfl

def divXSubList (ζ : R) : List R → List R
  | [] => []
  | [_] => []
  | _ :: c₁ :: cs => evalCoeffs (c₁ :: cs) ζ :: divXSubList ζ (c₁ :: cs)

def divXSub (p : UPoly R) (ζ : R) : UPoly R :=
  ofList (divXSubList ζ p.coeffs)

omit [DecidableEq R] in
theorem length_divXSubList (ζ : R) :
    ∀ l : List R, (divXSubList ζ l).length = l.length - 1
  | [] => rfl
  | [_] => rfl
  | _ :: c₁ :: cs => by
    show (divXSubList ζ (c₁ :: cs)).length + 1 = (c₁ :: cs).length
    rw [length_divXSubList ζ (c₁ :: cs)]; rfl

theorem divXSubList_spec (ζ : R) :
    ∀ l : List R, ofList l = add (C (evalCoeffs l ζ)) (mul (sub X (C ζ)) (ofList (divXSubList ζ l)))
  | [] => by
    show zero = add (C zero) (mul (sub X (C ζ)) zero)
    rw [UPoly.C_zero_eq, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | [c] => by
    show ofList [c] = add (C (add c (mul ζ zero))) (mul (sub X (C ζ)) zero)
    rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    rfl
  | c₀ :: c₁ :: cs => by
    rw [ofList_cons c₀ (c₁ :: cs), divXSubList_spec ζ (c₁ :: cs)]
    show add (C c₀) (mul X (add (C (evalCoeffs (c₁ :: cs) ζ))
        (mul (sub X (C ζ)) (ofList (divXSubList ζ (c₁ :: cs)))))) =
      add (C (add c₀ (mul ζ (evalCoeffs (c₁ :: cs) ζ))))
        (mul (sub X (C ζ)) (ofList (evalCoeffs (c₁ :: cs) ζ :: divXSubList ζ (c₁ :: cs))))
    rw [ofList_cons, UPoly.C_add_eq, UPoly.C_mul_eq]; constructive_ring

theorem divXSub_spec (p : UPoly R) (ζ : R) :
    p = add (C (p.eval ζ)) (mul (sub X (C ζ)) (divXSub p ζ)) ∧
      (divXSub p ζ).natDeg ≤ p.natDeg - 1 := by
  refine ⟨?_, ?_⟩
  · have h := divXSubList_spec ζ p.coeffs
    rwa [ofList_coeffs, ← eval_eq] at h
  · unfold divXSub natDeg
    have htr := trimPoly_length_le (divXSubList ζ p.coeffs)
    have hlen := length_divXSubList ζ p.coeffs
    rw [coeffs_ofList]; omega

/-! ## Monomials & Coefficient Extraction -/

def monom : Nat → UPoly R
  | 0 => one
  | k + 1 => mul X (monom k)

theorem coeffAt_monom :
    ∀ (k j : Nat), coeffAt (monom (R := R) k).coeffs j = if j = k then one else zero
  | 0, 0 => coeffAt_C_zero one
  | 0, j + 1 => coeffAt_C_succ one j
  | k + 1, 0 => coeffAt_X_mul_zero (monom k)
  | k + 1, j + 1 => by
    rw [monom, coeffAt_X_mul_succ, coeffAt_monom k j]
    if h : j = k then rw [h, ite_pos rfl, ite_pos rfl]
    else rw [ite_neg (fun e => h (Nat.succ.inj e)), ite_neg h]

theorem coeffAt_monom_mul :
    ∀ (d : Nat) (G : UPoly R) (j : Nat),
      coeffAt (mul (monom d) G).coeffs j = if d ≤ j then coeffAt G.coeffs (j - d) else zero
  | 0, G, j => by
    show coeffAt (mul one G).coeffs j = _
    rw [LawfulCommRing.one_mul, ite_pos (Nat.zero_le j), Nat.sub_zero]
  | d + 1, G, 0 => by
    show coeffAt (mul (mul X (monom d)) G).coeffs 0 = _
    rw [LawfulCommRing.mul_assoc, coeffAt_X_mul_zero, ite_neg (Nat.not_succ_le_zero d)]
  | d + 1, G, j + 1 => by
    show coeffAt (mul (mul X (monom d)) G).coeffs (j + 1) = _
    rw [LawfulCommRing.mul_assoc, coeffAt_X_mul_succ, coeffAt_monom_mul d G j]
    if h : d ≤ j then rw [ite_pos h, ite_pos (Nat.succ_le_succ h), Nat.succ_sub_succ]
    else rw [ite_neg h, ite_neg (fun hs => h (Nat.le_of_succ_le_succ hs))]

/-! ## Master Linear-Factor Identity `sylRes_mul_X_sub` -/

theorem coeffAt_sub_X_C_mul (ζ : R) (G : UPoly R) :
    (coeffAt (mul (sub X (C ζ)) G).coeffs 0 = neg (mul ζ (coeffAt G.coeffs 0))) ∧
      ∀ s : Nat, coeffAt (mul (sub X (C ζ)) G).coeffs (s + 1) =
        sub (coeffAt G.coeffs s) (mul ζ (coeffAt G.coeffs (s + 1))) := by
  have hExpand : mul (sub X (C ζ)) G = sub (mul X G) (mul (C ζ) G) := by constructive_ring
  refine ⟨?_, fun s => ?_⟩
  · rw [hExpand, coeffAt_sub, coeffAt_X_mul_zero, coeffAt_C_mul]; constructive_ring
  · rw [hExpand, coeffAt_sub, coeffAt_X_mul_succ, coeffAt_C_mul]

omit [DecidableEq R] in
theorem rangeSum_eval_eq (ζ : R) :
    ∀ (l : List R) (K : Nat),
      l.length ≤ K → Mat.rangeSum K (fun j => mul (coeffAt l j) (CRing.npow ζ j)) = evalCoeffs l ζ
  | [], K, _ => Mat.rangeSum_eq_zero fun j _ => by rw [coeffAt_nil, LawfulCommRing.zero_mul]
  | _ :: _, 0, h => by simp only [List.length_cons] at h; exfalso; omega
  | c :: cs, K + 1, h => by
    have hShift : ∀ m, Mat.rangeSum (m + 1) (fun j => mul (coeffAt (c :: cs) j) (CRing.npow ζ j)) =
        add c (mul ζ (Mat.rangeSum m (fun j => mul (coeffAt cs j) (CRing.npow ζ j)))) := by
      intro m; induction m with
      | zero =>
        show add zero (mul c one) = add c (mul ζ zero)
        rw [LawfulCommRing.zero_add, LawfulCommRing.mul_one, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
      | succ m ihm =>
        show add (Mat.rangeSum (m + 1) _) (mul (coeffAt cs m) (mul (CRing.npow ζ m) ζ)) =
          add c (mul ζ (add (Mat.rangeSum m _) (mul (coeffAt cs m) (CRing.npow ζ m))))
        rw [ihm]; constructive_ring
    rw [hShift K, rangeSum_eval_eq ζ cs K (by simp only [List.length_cons] at h; omega)]; rfl

theorem telescope_col0 (ζ : R) (G : UPoly R) :
    ∀ s : Nat,
      Mat.rangeSum (s + 1) (fun j => mul (coeffAt (mul (sub X (C ζ)) G).coeffs j) (CRing.npow ζ j)) =
        neg (mul (coeffAt G.coeffs s) (CRing.npow ζ (s + 1)))
  | 0 => by
    show add zero (mul (coeffAt (mul (sub X (C ζ)) G).coeffs 0) one) = neg (mul (coeffAt G.coeffs 0) (mul one ζ))
    rw [(coeffAt_sub_X_C_mul ζ G).1]; constructive_ring
  | s + 1 => by
    show add (Mat.rangeSum (s + 1) _)
        (mul (coeffAt (mul (sub X (C ζ)) G).coeffs (s + 1)) (CRing.npow ζ (s + 1))) =
      neg (mul (coeffAt G.coeffs (s + 1)) (mul (CRing.npow ζ (s + 1)) ζ))
    rw [telescope_col0 ζ G s, (coeffAt_sub_X_C_mul ζ G).2 s]; constructive_ring

theorem telescope_col_succ (ζ : R) (G : UPoly R) (c : Nat) :
    ∀ d : Nat,
      Mat.rangeSum (c + 1 + (d + 1))
        (fun j => mul (coeffAt (mul (sub X (C ζ)) G).coeffs j)
          (if c + 1 ≤ j then CRing.npow ζ (j - (c + 1)) else zero)) =
        sub (coeffAt G.coeffs c) (mul (coeffAt G.coeffs (c + 1 + d)) (CRing.npow ζ (d + 1)))
  | 0 => by
    have hz : Mat.rangeSum (c + 1)
        (fun j => mul (coeffAt (mul (sub X (C ζ)) G).coeffs j)
          (if c + 1 ≤ j then CRing.npow ζ (j - (c + 1)) else zero)) = zero :=
      Mat.rangeSum_eq_zero fun j hj => by rw [ite_neg (by omega), LawfulCommRing.mul_zero]
    show add (Mat.rangeSum (c + 1) _) _ = sub (coeffAt G.coeffs c) (mul (coeffAt G.coeffs (c + 1 + 0)) (mul one ζ))
    rw [hz, LawfulCommRing.zero_add]
    dsimp only
    rw [ite_pos (Nat.le_refl (c + 1)), Nat.sub_self, (coeffAt_sub_X_C_mul ζ G).2 c]
    show mul _ one = _; constructive_ring
  | d + 1 => by
    show add (Mat.rangeSum (c + 1 + (d + 1)) _)
        (mul (coeffAt (mul (sub X (C ζ)) G).coeffs (c + 1 + (d + 1)))
          (if c + 1 ≤ c + 1 + (d + 1) then CRing.npow ζ (c + 1 + (d + 1) - (c + 1)) else zero)) =
      sub (coeffAt G.coeffs c) (mul (coeffAt G.coeffs (c + 1 + (d + 1))) (mul (CRing.npow ζ (d + 1)) ζ))
    rw [telescope_col_succ ζ G c d, ite_pos (by omega), show c + 1 + (d + 1) - (c + 1) = d + 1 by omega,
      show c + 1 + (d + 1) = (c + 1 + d) + 1 by omega, (coeffAt_sub_X_C_mul ζ G).2 (c + 1 + d)]
    constructive_ring

def polyOfRange : Nat → (Nat → R) → UPoly R
  | 0, _ => zero
  | n + 1, f => add (polyOfRange n f) (mul (C (f n)) (monom n))

theorem coeffAt_polyOfRange :
    ∀ (n : Nat) (f : Nat → R) (i : Nat),
      coeffAt (polyOfRange n f).coeffs i = if i < n then f i else zero
  | 0, _, i => by show coeffAt (zero : UPoly R).coeffs i = zero; rw [coeffs_zero, coeffAt_nil]
  | n + 1, f, i => by
    show coeffAt (add (polyOfRange n f) (mul (C (f n)) (monom n))).coeffs i = _
    rw [coeffAt_add, coeffAt_polyOfRange n f i, coeffAt_C_mul, coeffAt_monom]
    if hEq : i = n then
      subst hEq; rw [ite_neg (Nat.lt_irrefl i), ite_pos rfl, ite_pos (Nat.lt_succ_self i)]; constructive_ring
    else if hLt : i < n then
      rw [ite_pos hLt, ite_neg hEq, ite_pos (Nat.lt_succ_of_lt hLt)]; constructive_ring
    else
      rw [ite_neg hLt, ite_neg hEq, ite_neg (by omega)]; constructive_ring

theorem coeffAt_mul_polyOfRange (B : UPoly R) :
    ∀ (n : Nat) (f : Nat → R) (j : Nat),
      coeffAt (mul (polyOfRange n f) B).coeffs j =
        Mat.rangeSum n (fun i => mul (f i) (if i ≤ j then coeffAt B.coeffs (j - i) else zero))
  | 0, _, _ => by show coeffAt (mul zero B).coeffs _ = zero; rw [LawfulCommRing.zero_mul, coeffs_zero, coeffAt_nil]
  | n + 1, f, j => by
    show coeffAt (mul (add (polyOfRange n f) (mul (C (f n)) (monom n))) B).coeffs j = add _ _
    have hDist : mul (add (polyOfRange n f) (mul (C (f n)) (monom n))) B =
        add (mul (polyOfRange n f) B) (mul (C (f n)) (mul (monom n) B)) := by constructive_ring
    rw [hDist, coeffAt_add, coeffAt_mul_polyOfRange B n f j, coeffAt_C_mul, coeffAt_monom_mul]

theorem bezout_step (mK U0 A V0 B q r : UPoly R)
    (h1 : mul mK (add (mul U0 A) (mul V0 B)) = mK)
    (h2 : mul mK V0 = add (mul q A) r) :
    add (mul (add (mul mK U0) (mul q B)) A) (mul r B) = mK := by
  have hRhs : mK = add (mul (mul mK U0) A) (mul (add (mul q A) r) B) := by
    conv => lhs; rw [← h1]
    rw [LawfulCommRing.left_distrib, ← LawfulCommRing.mul_assoc mK V0 B, h2]
    constructive_ring
  conv => rhs; rw [hRhs]
  constructive_ring

end SylElim
theorem exists_mem_ne_zero_of_coeffAt {R : Type} [CommRingOps R] : ∀ (l : List R) (k : Nat),
    coeffAt l k ≠ zero → ∃ c ∈ l, c ≠ zero
  | [], k, h => absurd (coeffAt_nil k) h
  | c :: _, 0, h => ⟨c, .head _, by rwa [coeffAt_cons_zero] at h⟩
  | _ :: cs, k + 1, h => by
    rw [coeffAt_cons_succ] at h
    obtain ⟨c', hc', hne⟩ := exists_mem_ne_zero_of_coeffAt cs k h
    exact ⟨c', .tail _ hc', hne⟩

namespace Frac
variable {D : Type} [LawfulCommRing D] [NoZeroDivisors D] [DecidableEq D] [NontrivialRing D]
theorem exists_mul_denominator (c : Frac D) : ∃ n d : D, d ≠ zero ∧ mul (of.toFun d) c = of.toFun n := by
  induction c using ind₁ with | h a =>
  refine ⟨a.num, a.den, a.den_ne, sound ?_⟩
  show mul (mul a.den a.num) one = mul a.num (mul one a.den)
  constructive_ring
end Frac
namespace UPoly
variable {R : Type} [LawfulCommRing R] [DecidableEq R]
theorem prodList_nil : prodList ([] : List (UPoly R)) = one := by rfl
theorem prodList_cons (p : UPoly R) (ps : List (UPoly R)) : prodList (p :: ps) = mul p (prodList ps) := by rfl
end UPoly
end Qsag

namespace Qsag.UPoly
open Qsag CommRingOps
 theorem coeffAt_mul_raw {R : Type} [LawfulCommRing R] [DecidableEq R] (A B : UPoly R) (k : Nat) :
   coeffAt (mul A B).coeffs k = coeffAt (rawMul A.coeffs B.coeffs) k := coeffAt_trimPoly _ _
end Qsag.UPoly

namespace Qsag.RingHom
theorem comp_toFun {R S T : Type} [LawfulCommRing R] [LawfulCommRing S] [LawfulCommRing T]
 (ψ : RingHom S T) (φ : RingHom R S) : (ψ.comp φ).toFun = fun x => ψ.toFun (φ.toFun x) := by rfl
theorem id_toFun {R : Type} [CommRingOps R] : (id R).toFun = fun x => x := by rfl
end Qsag.RingHom

namespace Qsag
/-- Variable-length polynomial coefficient addition over any ring `F`. -/
abbrev polyAddVar {F : Type} [CommRingOps F] : List F → List F → List F := rawAddCoeffs

/-- Variable-length polynomial subtraction `P - Q` over any ring `F`. -/
def polySubVar {F : Type} [CommRingOps F] : List F → List F → List F
  | xs, [] => xs
  | [], y :: ys => CommRingOps.sub CommRingOps.zero y :: polySubVar [] ys
  | x :: xs, y :: ys => CommRingOps.sub x y :: polySubVar xs ys

/-- Scalar multiplication `c * P(X)` over any ring `F`. -/
def polyScaleVar {F : Type} [CommRingOps F] (c : F) : List F → List F :=
  List.map (CommRingOps.mul c)

/-- Monomial shift `X * P(X)` (`0` constant term prepended). -/
def shiftPoly {F : Type} [CommRingOps F] (xs : List F) : List F :=
  CommRingOps.zero :: xs

/-- `[CWYZ26]` §5.1 / `affine.rs:fold_step` equal-degree affine combiner:
    `affineCombine θ α β F G(Y) = G(Y) + (α + β Y) (F(Y) + θ G(Y))`. -/
def affineCombine {F : Type} [CommRingOps F] (θ α β : F) (F_poly G_poly : List F) : List F :=
  let H_comb := polyAddVar F_poly (polyScaleVar θ G_poly)
  polyAddVar G_poly (polyAddVar (polyScaleVar α H_comb) (polyScaleVar β (shiftPoly H_comb)))

theorem polyAddVar_length_le {F : Type} [CommRingOps F] :
    ∀ (xs ys : List F) (b : Nat), xs.length ≤ b → ys.length ≤ b → (polyAddVar xs ys).length ≤ b
  | [], _, _, _, hy => hy
  | _ :: _, [], _, hx, _ => hx
  | _ :: _, _ :: _, 0, hx, _ => by simp at hx
  | _ :: xs, _ :: ys, b + 1, hx, hy => by
    simp only [polyAddVar, rawAddCoeffs, List.length_cons] at hx hy ⊢
    exact Nat.succ_le_succ (polyAddVar_length_le xs ys b (Nat.le_of_succ_le_succ hx) (Nat.le_of_succ_le_succ hy))

theorem polySubVar_length_le {F : Type} [CommRingOps F] :
    ∀ (xs ys : List F) (b : Nat), xs.length ≤ b → ys.length ≤ b → (polySubVar xs ys).length ≤ b
  | _, [], _, hx, _ => hx
  | [], _ :: _, 0, _, hy => by simp at hy
  | [], _ :: ys, b + 1, _, hy => by
    simp only [polySubVar, List.length_cons] at hy ⊢
    exact Nat.succ_le_succ (polySubVar_length_le [] ys b (Nat.zero_le b) (Nat.le_of_succ_le_succ hy))
  | _ :: _, _ :: _, 0, hx, _ => by simp at hx
  | _ :: xs, _ :: ys, b + 1, hx, hy => by
    simp only [polySubVar, List.length_cons] at hx hy ⊢
    exact Nat.succ_le_succ (polySubVar_length_le xs ys b (Nat.le_of_succ_le_succ hx) (Nat.le_of_succ_le_succ hy))

theorem evalCoeffs_polyAddVar {F : Type} [LawfulCommRing F] :
    ∀ (xs ys : List F) (z : F),
      RoundPoly.evalCoeffs (polyAddVar xs ys) z =
        CommRingOps.add (RoundPoly.evalCoeffs xs z) (RoundPoly.evalCoeffs ys z)
  | xs, ys, z => by unfold polyAddVar; exact evalCoeffs_rawAdd xs ys z

private theorem add_neg_distrib {F : Type} [LawfulCommRing F] (a b : F) :
    CommRingOps.add (CommRingOps.neg a) (CommRingOps.neg b) =
      CommRingOps.neg (CommRingOps.add a b) := by
  have hZero :
      CommRingOps.add (CommRingOps.add a b)
        (CommRingOps.add (CommRingOps.neg a) (CommRingOps.neg b)) = CommRingOps.zero := by
    rw [LawfulCommRing.add_assoc a b _,
        ← LawfulCommRing.add_assoc b (CommRingOps.neg a) _,
        LawfulCommRing.add_comm b (CommRingOps.neg a),
        LawfulCommRing.add_assoc (CommRingOps.neg a) b _,
        LawfulCommRing.add_right_neg,
        LawfulCommRing.add_zero,
        LawfulCommRing.add_right_neg]
  have hAdd := congrArg (CommRingOps.add (CommRingOps.neg (CommRingOps.add a b))) hZero
  rw [LawfulCommRing.add_zero,
      ← LawfulCommRing.add_assoc (CommRingOps.neg (CommRingOps.add a b)),
      LawfulCommRing.add_left_neg,
      LawfulCommRing.zero_add] at hAdd
  exact hAdd

theorem evalCoeffs_polySubVar {F : Type} [LawfulCommRing F] :
    ∀ (xs ys : List F) (z : F),
      RoundPoly.evalCoeffs (polySubVar xs ys) z =
        CommRingOps.sub (RoundPoly.evalCoeffs xs z) (RoundPoly.evalCoeffs ys z)
  | xs, [], z => by
    change RoundPoly.evalCoeffs xs z = CommRingOps.sub (RoundPoly.evalCoeffs xs z) CommRingOps.zero
    have hNeg0 : CommRingOps.neg (CommRingOps.zero : F) = CommRingOps.zero := by
      have h := LawfulCommRing.add_left_neg (CommRingOps.zero : F)
      rw [LawfulCommRing.add_zero] at h
      exact h
    rw [LawfulCommRing.sub_eq_add_neg, hNeg0, LawfulCommRing.add_zero]
  | [], y :: ys, z => by
    simp only [polySubVar, RoundPoly.evalCoeffs_cons, evalCoeffs_polySubVar [] ys z]
    change CommRingOps.add (CommRingOps.sub CommRingOps.zero y)
        (CommRingOps.mul z (CommRingOps.sub CommRingOps.zero (RoundPoly.evalCoeffs ys z))) =
      CommRingOps.sub CommRingOps.zero
        (CommRingOps.add y (CommRingOps.mul z (RoundPoly.evalCoeffs ys z)))
    rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.sub_eq_add_neg,
        LawfulCommRing.sub_eq_add_neg,
        LawfulCommRing.zero_add, LawfulCommRing.zero_add, LawfulCommRing.zero_add,
        LawfulCommRing.mul_neg, add_neg_distrib]
  | x :: xs, y :: ys, z => by
    simp only [polySubVar, RoundPoly.evalCoeffs_cons, evalCoeffs_polySubVar xs ys z]
    rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.sub_eq_add_neg,
        LawfulCommRing.sub_eq_add_neg,
        LawfulCommRing.left_distrib, LawfulCommRing.mul_neg, ← add_neg_distrib,
        LawfulCommRing.add_assoc x (CommRingOps.neg y) _,
        ← LawfulCommRing.add_assoc (CommRingOps.neg y) (CommRingOps.mul z (RoundPoly.evalCoeffs xs z)) _,
        LawfulCommRing.add_comm (CommRingOps.neg y) (CommRingOps.mul z (RoundPoly.evalCoeffs xs z)),
        LawfulCommRing.add_assoc (CommRingOps.mul z (RoundPoly.evalCoeffs xs z)) (CommRingOps.neg y) _,
        ← LawfulCommRing.add_assoc x _ _]

theorem evalCoeffs_polyScaleVar {F : Type} [LawfulCommRing F] (c : F) :
    ∀ (xs : List F) (z : F),
      RoundPoly.evalCoeffs (polyScaleVar c xs) z = CommRingOps.mul c (RoundPoly.evalCoeffs xs z)
  | [], _ => (LawfulCommRing.mul_zero c).symm
  | x :: xs, z => by
    simp only [polyScaleVar, List.map_cons, RoundPoly.evalCoeffs_cons]
    change CommRingOps.add (CommRingOps.mul c x)
        (CommRingOps.mul z (RoundPoly.evalCoeffs (polyScaleVar c xs) z)) = _
    rw [evalCoeffs_polyScaleVar c xs z,
        ← LawfulCommRing.mul_assoc z c _,
        LawfulCommRing.mul_comm z c,
        LawfulCommRing.mul_assoc c z _,
        ← LawfulCommRing.left_distrib]

theorem evalCoeffs_shiftPoly {F : Type} [LawfulCommRing F] (xs : List F) (z : F) :
    RoundPoly.evalCoeffs (shiftPoly xs) z = CommRingOps.mul z (RoundPoly.evalCoeffs xs z) := by
  simp only [shiftPoly, RoundPoly.evalCoeffs_cons, LawfulCommRing.zero_add]

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

end Qsag

namespace Qsag
open CommRingOps
namespace UPoly
variable {R : Type} [LawfulCommRing R] [DecidableEq R]
theorem coeffAt_natDeg_ne_zero [NoZeroDivisors R] {p : UPoly R} (h : p ≠ zero) : coeffAt p.coeffs p.natDeg ≠ zero := fun e => lead_ne_zero h ((lead_eq p).trans e)
theorem eval₂_id (x : R) (p : UPoly R) : eval₂ (RingHom.id R) x p = p.eval x := rfl
theorem eval_zero_poly (x : R) : (zero : UPoly R).eval x = zero := (evalHom x).map_zero
end UPoly
end Qsag

namespace Qsag
open CommRingOps
namespace RingHom
variable {R S : Type} [LawfulCommRing R] [LawfulCommRing S]
theorem comp_id (φ : RingHom R S) : φ.comp (RingHom.id R) = φ := by cases φ; rfl
theorem id_comp (φ : RingHom R S) : (RingHom.id S).comp φ = φ := by cases φ; rfl
end RingHom
end Qsag

namespace Qsag
theorem polyScaleVar_length {F : Type} [CommRingOps F] (c : F) (xs : List F) :
    (polyScaleVar c xs).length = xs.length := by unfold polyScaleVar; exact List.length_map _
theorem shiftPoly_length {F : Type} [CommRingOps F] (xs : List F) :
    (shiftPoly xs).length = xs.length + 1 := by unfold shiftPoly; rfl
end Qsag

namespace Qsag
/-! ### Exports for lane agg-whir-cert -/

theorem shiftPoly_eq {F : Type} [CommRingOps F] (xs : List F) :
    shiftPoly xs = CommRingOps.zero :: xs := by rfl

/-! ### Exports for lane agg-budget -/

/- Defining equations `f_def : f x = body` of definitions whose bodies are not exposed, for
   downstream modules that import this one without `import all`. -/

theorem polyAddVar_def {F : Type} [CommRingOps F] :
    (polyAddVar : List F → List F → List F) = rawAddCoeffs := by rfl

theorem polyScaleVar_def {F : Type} [CommRingOps F] (c : F) :
    polyScaleVar c = List.map (CommRingOps.mul c) := by rfl

theorem affineCombine_def {F : Type} [CommRingOps F] (θ α β : F) (F_poly G_poly : List F) :
    affineCombine θ α β F_poly G_poly =
      polyAddVar G_poly
        (polyAddVar (polyScaleVar α (polyAddVar F_poly (polyScaleVar θ G_poly)))
          (polyScaleVar β (shiftPoly (polyAddVar F_poly (polyScaleVar θ G_poly))))) := by
  rfl

-- (end exports for lane agg-budget)

end Qsag
