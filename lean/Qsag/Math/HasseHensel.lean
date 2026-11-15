module
public import Qsag.Math.PolyRing

/-!
# Qsag.Math.HasseHensel

Hasse–Taylor calculus and Hensel lifting for the Guruswami–Sudan / `[CWYZ26]` arguments.

* `GsUniPoly` (an alias of `UPoly`): `gsTaylor`, univariate Hasse derivatives `gsUniHasse`,
  linear-factor multiplicities;
* powers of a principal ideal `InPow`, the Newton fixed-point operator, composition of Hasse
  derivatives;
* `Hensel`: root-series numerators, base change, and their degree bounds;
* `Poly3` jets: numerators of `R(t₀ + W, Y + V·W, Z + U)`, specialization at a point,
  reconstruction from the jet, triangular index sets, and the generic-point jet over `RatFunc`;
* Newton interpolation `newtonInterp` and agreement-forces-equality lemmas.
-/

public section
-- Avoid the choice-based LawfulBEq derived from the Fin order package.
attribute [-instance] Fin.instLinearOrderPackage
namespace Qsag
set_option autoImplicit false
open CommRingOps RoundPoly

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
def hasse (k : Nat) (p : UPoly R) : UPoly R := gsUniHasse (p.coeffs.map C) k X

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

theorem coeffAt_shift_list (b : R) : ∀ (l : List R) (k : Nat),
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
def degZ (Q : Poly3 F) : Nat := Q.natDeg

theorem degZ_eq (Q : Poly3 F) : Q.degZ = Q.natDeg := by unfold degZ; rfl

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


end Qsag

namespace Qsag

namespace Poly3
variable {F : Type} [LawfulCommRing F] [DecidableEq F]
theorem hasseZ_eq (s : Nat) (Q : Poly3 F) : hasseZ s Q = UPoly.hasse s Q := by unfold hasseZ; rfl
theorem evalAffineLine_eq (Q : Poly3 F) (α β : F) (P : UPoly F) :
    evalAffineLine Q α β P = (affineLineHom α β P).toFun Q := by unfold evalAffineLine; rfl
theorem evalAffineLine_eq_eval₂ (Q : Poly3 F) (α β : F) (P : UPoly F) :
    evalAffineLine Q α β P = UPoly.eval₂ (UPoly.evalHom (line α β)) P Q := by
  unfold evalAffineLine affineLineHom; rfl
theorem evalAffineLine_one (α β : F) (P : UPoly F) :
    evalAffineLine CommRingOps.one α β P = CommRingOps.one := by
  rw [evalAffineLine_eq]; exact (affineLineHom α β P).map_one
end Poly3
end Qsag

namespace Qsag
open CommRingOps
namespace Poly3
variable {F : Type} [LawfulCommRing F] [DecidableEq F]
theorem line_zero : line (zero : F) zero = zero := by
  unfold line
  apply UPoly.ext_coeffAt; intro k
  rw [UPoly.coeffAt_ofList, UPoly.coeffs_zero, coeffAt_nil]
  cases k with
  | zero => rfl
  | succ k => cases k <;> rfl
theorem line_one_zero : line (one : F) zero = one := by
  unfold line
  apply UPoly.ext_coeffAt; intro k
  rw [UPoly.coeffAt_ofList]
  cases k with
  | zero => change one = coeffAt (UPoly.C (one : F)).coeffs 0; rw [UPoly.coeffAt_C_zero]
  | succ k => change _ = coeffAt (UPoly.C (one : F)).coeffs (k + 1); rw [UPoly.coeffAt_C_succ]; cases k <;> rfl
end Poly3
end Qsag

namespace Qsag
open CommRingOps RoundPoly UPoly
namespace UPoly
section Hasse
variable {R : Type} [LawfulCommRing R] [DecidableEq R]

/-- Hasse derivatives respect coefficient filtrations: the `i`-th coefficient of the `k`-th
    derivative is an integer combination of the coefficient of index `i + k`. -/
theorem coeffAt_hasse_graded : ∀ (l : List R) (L : Nat → R → Prop), (∀ j, L j zero) →
    (∀ j x y, L j x → L j y → L j (add x y)) → (∀ j, L j (coeffAt l j)) →
    ∀ k i, L (i + k) (coeffAt (gsUniHasse (l.map C) k (X : UPoly R)).coeffs i)
  | [], L, hz, _, _, k, i => by
    show L (i + k) (coeffAt (zero : UPoly R).coeffs i); rw [coeffs_zero, coeffAt_nil]; exact hz _
  | c :: cs, L, hz, hadd, hl, k, i => by
    have ih := coeffAt_hasse_graded cs (fun j => L (j + 1)) (fun _ => hz _) (fun _ => hadd _)
      (fun j => hl (j + 1))
    cases k with
    | zero =>
      show L (i + 0) (coeffAt (add (C c) (mul X (gsUniHasse (cs.map C) 0 X))).coeffs i)
      rw [coeffAt_add]
      cases i with
      | zero => rw [coeffAt_X_mul_zero, coeffAt_C_zero, LawfulCommRing.add_zero]; exact hl 0
      | succ i => rw [coeffAt_X_mul_succ, coeffAt_C_succ, LawfulCommRing.zero_add]; exact ih 0 i
    | succ k =>
      show L (i + (k + 1)) (coeffAt (add (gsUniHasse (cs.map C) k X)
        (mul X (gsUniHasse (cs.map C) (k + 1) X))).coeffs i)
      rw [coeffAt_add]
      apply hadd
      · exact ih k i
      · cases i with
        | zero => rw [coeffAt_X_mul_zero]; exact hz _
        | succ i =>
          rw [coeffAt_X_mul_succ]
          have := ih (k + 1) i
          rwa [show i + (k + 1) + 1 = i + 1 + (k + 1) by omega] at this

/-- Differentiating `k` times lowers the weighted degree by `k` times the variable weight. -/
theorem wdeg_hasse_le (w : R → Nat) (hw : DegFn w) (s k : Nat) (p : UPoly R) :
    (hasse k p).wdeg w s ≤ p.wdeg w s - s * k := by
  apply wdeg_le
  intro i h
  have key : coeffAt (hasse k p).coeffs i ≠ zero →
      w (coeffAt (hasse k p).coeffs i) + s * (i + k) ≤ p.wdeg w s :=
    coeffAt_hasse_graded p.coeffs (fun j x => x ≠ zero → w x + s * j ≤ p.wdeg w s)
      (fun _ h => absurd rfl h) (fun _ _ _ hx hy h => bnd_add hw hx hy h) (le_wdeg w s p) k i
  have := key h
  rw [Nat.mul_add] at this; omega
end Hasse
end UPoly
end Qsag

namespace Qsag
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


end Qsag

namespace Qsag
open RoundPoly

/-- Natural scalar in the supplied constructive ring. -/
def gsNat {F : Type} [CommRingOps F] : Nat → F
  | 0 => CommRingOps.zero
  | n + 1 => CommRingOps.add (gsNat n) CommRingOps.one

/-- Powers in the supplied constructive ring. -/
def gsPow {F : Type} [CommRingOps F] (x : F) : Nat → F
  | 0 => CommRingOps.one
  | n + 1 => CommRingOps.mul x (gsPow x n)

/-- Pascal recursion for binomial coefficients. -/
def gsChoose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => gsChoose n k + gsChoose n (k + 1)

/-- Formal `(r,s)` Hasse derivative of the monomial `X^i Y^j`, evaluated at `(x,y)`.
    Binomial coefficients, rather than factorial division, make this valid in every characteristic. -/
def gsHasseMonomial {F : Type} [CommRingOps F]
    (e order : Nat × Nat) (point : F × F) : F :=
  CommRingOps.mul (gsNat (gsChoose e.1 order.1 * gsChoose e.2 order.2))
    (CommRingOps.mul (gsPow point.1 (e.1 - order.1)) (gsPow point.2 (e.2 - order.2)))

/-- Taylor coefficients of `cs` at `b` by repeated synthetic division:
    `cs(Y) = ∑ₛ (gsTaylor n cs b)[s] · (Y - b)^s` whenever `cs.length ≤ n`. Entry `s` is the
    `s`-th Hasse derivative of `cs` at `b`. No binomial or factorial division occurs, so the
    expansion holds over every commutative ring and in every characteristic. -/
def gsTaylor {R : Type} [CommRingOps R] : Nat → List R → R → List R
  | 0, _, _ => []
  | n + 1, cs, b => evalCoeffs cs b :: gsTaylor n (quotLinear cs b) b

/-- Taylor re-expansion preserves evaluation at every point of the ring. Over `R = F[X]` this
    quantifies over all substituted polynomials, so it is a formal identity in `Y`. -/
theorem gsTaylor_eval {R : Type} [LawfulCommRing R] (b y : R) :
    ∀ (n : Nat) (cs : List R), cs.length ≤ n →
      evalCoeffs cs y = evalCoeffs (gsTaylor n cs b) (CommRingOps.sub y b)
  | 0, cs, h => by
    have hcs : cs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero h)
    subst hcs
    rfl
  | n + 1, cs, h => by
    have ih := gsTaylor_eval b y n (quotLinear cs b) (by rw [quotLinear_length]; omega)
    show evalCoeffs cs y = CommRingOps.add (evalCoeffs cs b)
      (CommRingOps.mul (CommRingOps.sub y b)
        (evalCoeffs (gsTaylor n (quotLinear cs b) b) (CommRingOps.sub y b)))
    rw [← ih]
    exact (evalCoeffs_eq_mul_quotLinear_add cs b y).trans (LawfulCommRing.add_comm _ _)

theorem gsPow_zero_mul {R : Type} [LawfulCommRing R] (t w : R) :
    CommRingOps.mul (gsPow t 0) w = w :=
  LawfulCommRing.one_mul w

theorem gsPow_succ_mul {R : Type} [LawfulCommRing R] (t : R) (k : Nat) (w : R) :
    CommRingOps.mul (gsPow t (k + 1)) w = CommRingOps.mul t (CommRingOps.mul (gsPow t k) w) :=
  LawfulCommRing.mul_assoc t (gsPow t k) w

theorem gs_mul_mul_mul_comm {R : Type} [LawfulCommRing R] (a b c d : R) :
    CommRingOps.mul (CommRingOps.mul a b) (CommRingOps.mul c d) =
      CommRingOps.mul (CommRingOps.mul a c) (CommRingOps.mul b d) := by
  rw [LawfulCommRing.mul_assoc a b, ← LawfulCommRing.mul_assoc b c d,
    LawfulCommRing.mul_comm b c, LawfulCommRing.mul_assoc c b d, ← LawfulCommRing.mul_assoc a c]

/-- If the coefficient of `Y^s` is divisible by `t^(m - s)` for every `s < m`, then substituting
    `Y := t * u` gives a value divisible by `t^m`. -/
theorem gs_low_order_divisible {R : Type} [LawfulCommRing R] (t u : R) :
    ∀ (cs : List R) (m : Nat),
      (∀ s : Nat, s < m → ∃ h : R, coeffAt cs s = CommRingOps.mul (gsPow t (m - s)) h) →
      ∃ k : R, evalCoeffs cs (CommRingOps.mul t u) = CommRingOps.mul (gsPow t m) k
  | [], _, _ => ⟨CommRingOps.zero, (LawfulCommRing.mul_zero _).symm⟩
  | c :: cs, 0, _ =>
    ⟨evalCoeffs (c :: cs) (CommRingOps.mul t u), (LawfulCommRing.one_mul _).symm⟩
  | c :: cs, m + 1, h => by
    obtain ⟨h0, hh0⟩ := h 0 (Nat.succ_pos m)
    rw [coeffAt_cons_zero, Nat.sub_zero] at hh0
    have htail : ∀ s : Nat, s < m →
        ∃ h' : R, coeffAt cs s = CommRingOps.mul (gsPow t (m - s)) h' := by
      intro s hs
      obtain ⟨h', hh'⟩ := h (s + 1) (Nat.succ_lt_succ hs)
      rw [coeffAt_cons_succ, Nat.add_sub_add_right] at hh'
      exact ⟨h', hh'⟩
    obtain ⟨k, hk⟩ := gs_low_order_divisible t u cs m htail
    refine ⟨CommRingOps.add h0 (CommRingOps.mul u k), ?_⟩
    show CommRingOps.add c
        (CommRingOps.mul (CommRingOps.mul t u) (evalCoeffs cs (CommRingOps.mul t u))) =
      CommRingOps.mul (gsPow t (m + 1)) (CommRingOps.add h0 (CommRingOps.mul u k))
    rw [hk, hh0, LawfulCommRing.left_distrib]
    exact congrArg (CommRingOps.add (CommRingOps.mul (gsPow t (m + 1)) h0))
      (gs_mul_mul_mul_comm t u (gsPow t m) k)

theorem gsLinear_trimmed {F : Type} [LawfulField F] [DecidableEq F] (a : F) :
    trimPoly [CommRingOps.neg a, CommRingOps.one] = [CommRingOps.neg a, CommRingOps.one] := by
  simp [trimPoly, LawfulField.one_ne_zero]

/-- The monic linear polynomial `X - a` as a canonical element of `F[X]`. -/
def gsLinear {F : Type} [LawfulField F] [DecidableEq F] (a : F) : GsUniPoly F :=
  ⟨[CommRingOps.neg a, CommRingOps.one], gsLinear_trimmed a⟩

/-- The constant polynomial `b` as a canonical element of `F[X]`. -/
def gsConst {F : Type} [LawfulField F] [DecidableEq F] (b : F) : GsUniPoly F :=
  GsUniPoly.ofCoeffs [b]

theorem gsLinear_eval {F : Type} [LawfulField F] [DecidableEq F] (a c : F) :
    evalCoeffs (gsLinear a).coeffs c = CommRingOps.sub c a := by
  show evalCoeffs [CommRingOps.neg a, CommRingOps.one] c = CommRingOps.sub c a
  rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_comm c (CommRingOps.neg a)]
  simp only [evalCoeffs_cons, evalCoeffs_nil, LawfulCommRing.mul_zero, LawfulCommRing.add_zero,
    LawfulCommRing.mul_one]

/-- Formal factor theorem in `F[X]`: a polynomial vanishing at `a` is `(X - a)` times a
    polynomial, with the quotient produced by `polyDivMod`. -/
theorem gsLinear_factor {F : Type} [LawfulField F] [DecidableEq F] (a : F)
    (c : GsUniPoly F) (hroot : evalCoeffs c.coeffs a = CommRingOps.zero) :
    ∃ u : GsUniPoly F, c = CommRingOps.mul (gsLinear a) u := by
  have hLne : trimPoly [CommRingOps.neg a, CommRingOps.one] ≠ [] := by
    rw [gsLinear_trimmed]
    exact List.cons_ne_nil _ _
  have hspec := polyDivMod_spec c.coeffs [CommRingOps.neg a, CommRingOps.one] hLne
  dsimp only at hspec
  rcases hspec with ⟨hqTrim, hrTrim, hDecomp, hrLt⟩
  rw [gsLinear_trimmed] at hrLt
  have hLeval : evalCoeffs [CommRingOps.neg a, CommRingOps.one] a = CommRingOps.zero :=
    (gsLinear_eval a a).trans (LawfulCommRing.sub_self a)
  have hEv : evalCoeffs (polyDivMod c.coeffs [CommRingOps.neg a, CommRingOps.one]).2 a =
      CommRingOps.zero := by
    have h1 : evalCoeffs (trimPoly c.coeffs) a = evalCoeffs _ a :=
      congrArg (fun p => evalCoeffs p a) hDecomp
    rw [evalCoeffs_trimPoly, hroot, evalCoeffs_pAdd, evalCoeffs_pMul, hLeval,
      LawfulCommRing.mul_zero, LawfulCommRing.zero_add] at h1
    exact h1.symm
  have hrNil : (polyDivMod c.coeffs [CommRingOps.neg a, CommRingOps.one]).2 = [] := by
    cases hr : (polyDivMod c.coeffs [CommRingOps.neg a, CommRingOps.one]).2 with
    | nil => rfl
    | cons r0 rs =>
      rw [hr] at hrLt hrTrim hEv
      cases rs with
      | cons r1 rs' =>
        have h2 : 2 ≤ (r0 :: r1 :: rs').length :=
          Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))
        have h3 : ([CommRingOps.neg a, CommRingOps.one] : List F).length = 2 := rfl
        exfalso
        omega
      | nil =>
        have hr0 : r0 = CommRingOps.zero := by
          simpa only [evalCoeffs_cons, evalCoeffs_nil, LawfulCommRing.mul_zero,
            LawfulCommRing.add_zero] using hEv
        have hz : trimPoly [(CommRingOps.zero : F)] = [] := by simp [trimPoly]
        rw [hr0] at hrTrim
        exact absurd (hz.symm.trans hrTrim) (List.cons_ne_nil _ _).symm
  rw [hrNil, pAdd_nil_right] at hDecomp
  exact ⟨⟨(polyDivMod c.coeffs [CommRingOps.neg a, CommRingOps.one]).1, hqTrim⟩,
    UPoly.ext (c.trimmed.symm.trans (hDecomp.trans
      ((trimPoly_idem (rawMul (polyDivMod c.coeffs [CommRingOps.neg a, CommRingOps.one]).1
          [CommRingOps.neg a, CommRingOps.one])).trans
        (pMul_comm (polyDivMod c.coeffs [CommRingOps.neg a, CommRingOps.one]).1
          [CommRingOps.neg a, CommRingOps.one]))))⟩

theorem gsLinear_mul_cancel {F : Type} [LawfulField F] [DecidableEq F] (c : F)
    (x y : GsUniPoly F)
    (h : CommRingOps.mul (gsLinear c) x = CommRingOps.mul (gsLinear c) y) : x = y := by
  have hz : CommRingOps.mul (gsLinear c) (CommRingOps.sub x y) = CommRingOps.zero := by
    rw [LawfulCommRing.mul_sub, h, LawfulCommRing.sub_self]
  cases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hz with
  | inl hT =>
    exact absurd (show ([CommRingOps.neg c, CommRingOps.one] : List F) = [] from
      congrArg UPoly.coeffs hT) (List.cons_ne_nil _ _)
  | inr hs => exact LawfulCommRing.sub_eq_zero_iff.mp hs

/-- Distinct linear factors are coprime: `(X - c)^k ∣ (X - a) · v` with `c ≠ a` forces
    `(X - c)^k ∣ v`. Evaluation at `c` and the formal factor theorem replace Bézout. -/
theorem gsLinear_coprime_cancel_one {F : Type} [LawfulField F] [DecidableEq F]
    (c a : F) (hne : c ≠ a) :
    ∀ (k : Nat) (w v : GsUniPoly F),
      CommRingOps.mul (gsPow (gsLinear c) k) w = CommRingOps.mul (gsLinear a) v →
      ∃ w' : GsUniPoly F, v = CommRingOps.mul (gsPow (gsLinear c) k) w'
  | 0, _, v, _ => ⟨v, (gsPow_zero_mul (gsLinear c) v).symm⟩
  | k + 1, w, v, h => by
    letI : NoZeroDivisors F := LawfulField.toNoZeroDivisors F
    have hstep := gsPow_succ_mul (gsLinear c) k w
    have hL : evalCoeffs (CommRingOps.mul (gsPow (gsLinear c) (k + 1)) w).coeffs c =
        CommRingOps.zero := by
      rw [hstep]
      show evalCoeffs (pMul (gsLinear c).coeffs
        (CommRingOps.mul (gsPow (gsLinear c) k) w).coeffs) c = CommRingOps.zero
      rw [evalCoeffs_pMul, gsLinear_eval, LawfulCommRing.sub_self, LawfulCommRing.zero_mul]
    have hR : evalCoeffs (CommRingOps.mul (gsLinear a) v).coeffs c =
        CommRingOps.mul (CommRingOps.sub c a) (evalCoeffs v.coeffs c) := by
      show evalCoeffs (pMul (gsLinear a).coeffs v.coeffs) c =
        CommRingOps.mul (CommRingOps.sub c a) (evalCoeffs v.coeffs c)
      rw [evalCoeffs_pMul, gsLinear_eval]
    have hev : evalCoeffs (CommRingOps.mul (gsPow (gsLinear c) (k + 1)) w).coeffs c =
        evalCoeffs (CommRingOps.mul (gsLinear a) v).coeffs c := by rw [h]
    have hv0 : evalCoeffs v.coeffs c = CommRingOps.zero := by
      cases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero
          (hR.symm.trans (hev.symm.trans hL)) with
      | inl hs => exact absurd (LawfulCommRing.sub_eq_zero_iff.mp hs) hne
      | inr hv => exact hv
    obtain ⟨v1, hv1⟩ := gsLinear_factor c v hv0
    have h2 : CommRingOps.mul (gsLinear c) (CommRingOps.mul (gsPow (gsLinear c) k) w) =
        CommRingOps.mul (gsLinear c) (CommRingOps.mul (gsLinear a) v1) := by
      rw [← hstep, h, hv1, ← LawfulCommRing.mul_assoc, ← LawfulCommRing.mul_assoc,
        LawfulCommRing.mul_comm (gsLinear a) (gsLinear c)]
    obtain ⟨w1, hw1⟩ :=
      gsLinear_coprime_cancel_one c a hne k w v1 (gsLinear_mul_cancel c _ _ h2)
    exact ⟨w1, by rw [hv1, hw1]; exact (gsPow_succ_mul (gsLinear c) k w1).symm⟩

theorem gsLinear_pow_coprime_cancel {F : Type} [LawfulField F] [DecidableEq F]
    (c a : F) (hne : c ≠ a) (k : Nat) :
    ∀ (e : Nat) (w v : GsUniPoly F),
      CommRingOps.mul (gsPow (gsLinear c) k) w = CommRingOps.mul (gsPow (gsLinear a) e) v →
      ∃ w' : GsUniPoly F, v = CommRingOps.mul (gsPow (gsLinear c) k) w'
  | 0, w, v, h => ⟨w, (gsPow_zero_mul (gsLinear a) v).symm.trans h.symm⟩
  | e + 1, w, v, h => by
    obtain ⟨w1, hw1⟩ := gsLinear_coprime_cancel_one c a hne k w
      (CommRingOps.mul (gsPow (gsLinear a) e) v) (h.trans (gsPow_succ_mul (gsLinear a) e v))
    exact gsLinear_pow_coprime_cancel c a hne k e w1 v hw1.symm

theorem gsLinear_mul_length {F : Type} [LawfulField F] [DecidableEq F] (x : F)
    (h : GsUniPoly F) (hh : h.coeffs ≠ []) :
    (CommRingOps.mul (gsLinear x) h).coeffs.length = h.coeffs.length + 1 ∧
      (CommRingOps.mul (gsLinear x) h).coeffs ≠ [] := by
  have hl := pMul_length_of_trimmed_ne_nil (a := [CommRingOps.neg x, CommRingOps.one])
    (b := h.coeffs) (gsLinear_trimmed x) h.trimmed (List.cons_ne_nil _ _) hh
  have h2 : ([CommRingOps.neg x, CommRingOps.one] : List F).length = 2 := rfl
  rw [h2] at hl
  refine ⟨?_, hl.2⟩
  have h1 := hl.1
  show (pMul [CommRingOps.neg x, CommRingOps.one] h.coeffs).length = h.coeffs.length + 1
  omega

theorem gsLinear_pow_mul_length {F : Type} [LawfulField F] [DecidableEq F] (x : F) :
    ∀ (m : Nat) (h : GsUniPoly F), h.coeffs ≠ [] →
      (CommRingOps.mul (gsPow (gsLinear x) m) h).coeffs.length = m + h.coeffs.length ∧
        (CommRingOps.mul (gsPow (gsLinear x) m) h).coeffs ≠ []
  | 0, h, hh => by
    rw [gsPow_zero_mul]
    exact ⟨(Nat.zero_add _).symm, hh⟩
  | m + 1, h, hh => by
    have ih := gsLinear_pow_mul_length x m h hh
    have hl := gsLinear_mul_length x _ ih.2
    rw [gsPow_succ_mul]
    exact ⟨by rw [hl.1, ih.1]; omega, hl.2⟩

/-- A nonzero polynomial divisible by `(X - x)^m` at each of `A` distinct points has more than
    `m * A` coefficients. -/
theorem gs_multiplicity_length {F : Type} [LawfulField F] [DecidableEq F] (m : Nat) :
    ∀ (xs : List F) (g : GsUniPoly F), xs.Nodup → g.coeffs ≠ [] →
      (∀ x ∈ xs, ∃ k : GsUniPoly F, g = CommRingOps.mul (gsPow (gsLinear x) m) k) →
      m * xs.length + 1 ≤ g.coeffs.length
  | [], g, _, hg, _ => by
    cases hv : g.coeffs with
    | nil => exact absurd hv hg
    | cons _ _ => simp
  | x :: xs, g, hnd, hg, hdiv => by
    obtain ⟨h, hh⟩ := hdiv x (.head _)
    have hhne : h.coeffs ≠ [] := by
      intro h0
      have hzero : h = CommRingOps.zero := UPoly.ext h0
      have hg0 : g = CommRingOps.zero := by
        rw [hh, hzero]
        exact LawfulCommRing.mul_zero _
      exact hg (congrArg UPoly.coeffs hg0)
    have hrest : ∀ y ∈ xs, ∃ k : GsUniPoly F,
        h = CommRingOps.mul (gsPow (gsLinear y) m) k := by
      intro y hy
      obtain ⟨k, hk⟩ := hdiv y (.tail _ hy)
      have hne : y ≠ x := fun e => (List.pairwise_cons.mp hnd).1 y hy e.symm
      exact gsLinear_pow_coprime_cancel y x hne m m k h (hk.symm.trans hh)
    have ih := gs_multiplicity_length m xs h (List.pairwise_cons.mp hnd).2 hhne hrest
    have hl := (gsLinear_pow_mul_length x m h hhne).1
    have e : m * (x :: xs).length = m * xs.length + m := Nat.mul_succ m xs.length
    rw [hh, hl, e]
    omega

theorem gsUniHasse_zero_eq_evalCoeffs {R : Type} [CommRingOps R] :
    ∀ (cs : List R) (b : R), gsUniHasse cs 0 b = evalCoeffs cs b
  | [], _ => rfl
  | c :: cs, b => by
    show CommRingOps.add c (CommRingOps.mul b (gsUniHasse cs 0 b)) =
      CommRingOps.add c (CommRingOps.mul b (evalCoeffs cs b))
    rw [gsUniHasse_zero_eq_evalCoeffs cs b]

theorem gsUniHasse_quotLinear {R : Type} [LawfulCommRing R] :
    ∀ (cs : List R) (k : Nat) (b : R),
      gsUniHasse (quotLinear cs b) k b = gsUniHasse cs (k + 1) b
  | [], _, _ => rfl
  | [c₀], k, b => by
    show CommRingOps.zero =
      CommRingOps.add (gsUniHasse ([] : List R) k b)
        (CommRingOps.mul b (gsUniHasse ([] : List R) (k + 1) b))
    change CommRingOps.zero =
      CommRingOps.add CommRingOps.zero (CommRingOps.mul b CommRingOps.zero)
    rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | c₀ :: c₁ :: tl, 0, b => by
    have ih := gsUniHasse_quotLinear (c₁ :: tl) 0 b
    show CommRingOps.add (evalCoeffs (c₁ :: tl) b)
        (CommRingOps.mul b (gsUniHasse (quotLinear (c₁ :: tl) b) 0 b)) =
      CommRingOps.add (gsUniHasse (c₁ :: tl) 0 b)
        (CommRingOps.mul b (gsUniHasse (c₁ :: tl) 1 b))
    rw [ih, gsUniHasse_zero_eq_evalCoeffs (c₁ :: tl) b]
  | c₀ :: c₁ :: tl, k + 1, b => by
    have ih0 := gsUniHasse_quotLinear (c₁ :: tl) k b
    have ih1 := gsUniHasse_quotLinear (c₁ :: tl) (k + 1) b
    show CommRingOps.add (gsUniHasse (quotLinear (c₁ :: tl) b) k b)
        (CommRingOps.mul b (gsUniHasse (quotLinear (c₁ :: tl) b) (k + 1) b)) =
      CommRingOps.add (gsUniHasse (c₁ :: tl) (k + 1) b)
        (CommRingOps.mul b (gsUniHasse (c₁ :: tl) (k + 2) b))
    rw [ih0, ih1]

/-- Every synthetic-division Taylor coefficient `(gsTaylor n cs b)[k]` equals `gsUniHasse cs k b`. -/
theorem coeffAt_gsTaylor_eq_gsUniHasse {R : Type} [LawfulCommRing R] :
    ∀ (n : Nat) (cs : List R) (k : Nat) (b : R),
      cs.length ≤ n → coeffAt (gsTaylor n cs b) k = gsUniHasse cs k b
  | 0, cs, k, b, h => by
    have hcs : cs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero h)
    subst hcs
    rfl
  | n + 1, cs, 0, b, _ => by
    show coeffAt (evalCoeffs cs b :: gsTaylor n (quotLinear cs b) b) 0 = gsUniHasse cs 0 b
    rw [coeffAt_cons_zero, gsUniHasse_zero_eq_evalCoeffs]
  | n + 1, cs, k + 1, b, h => by
    show coeffAt (evalCoeffs cs b :: gsTaylor n (quotLinear cs b) b) (k + 1) =
      gsUniHasse cs (k + 1) b
    rw [coeffAt_cons_succ,
        coeffAt_gsTaylor_eq_gsUniHasse n (quotLinear cs b) k b (by rw [quotLinear_length]; omega),
        gsUniHasse_quotLinear]

theorem gsNat_add {R : Type} [LawfulCommRing R] (u : Nat) :
    ∀ (v : Nat), (gsNat (u + v) : R) = CommRingOps.add (gsNat u) (gsNat v)
  | 0 => (LawfulCommRing.add_zero _).symm
  | v + 1 => by
    show CommRingOps.add (gsNat (u + v)) CommRingOps.one =
      CommRingOps.add (gsNat u) (CommRingOps.add (gsNat v) CommRingOps.one)
    rw [gsNat_add u v, LawfulCommRing.add_assoc]

theorem gsNat_mul {R : Type} [LawfulCommRing R] (u : Nat) :
    ∀ (v : Nat), (gsNat (u * v) : R) = CommRingOps.mul (gsNat u) (gsNat v)
  | 0 => (LawfulCommRing.mul_zero _).symm
  | v + 1 => by
    rw [Nat.mul_succ, gsNat_add]
    show CommRingOps.add (gsNat (u * v)) (gsNat u) =
      CommRingOps.mul (gsNat u) (CommRingOps.add (gsNat v) CommRingOps.one)
    rw [gsNat_mul u v, LawfulCommRing.left_distrib, LawfulCommRing.mul_one]

theorem gsChoose_eq_zero_of_lt :
    ∀ (i r : Nat), i < r → gsChoose i r = 0
  | 0, _ + 1, _ => rfl
  | i + 1, r + 1, h => by
    have hlt := Nat.lt_of_succ_lt_succ h
    show gsChoose i r + gsChoose i (r + 1) = 0
    rw [gsChoose_eq_zero_of_lt i r hlt,
        gsChoose_eq_zero_of_lt i (r + 1) (Nat.lt_succ_of_lt hlt)]

/-- Univariate binomial-Hasse basis element `(i choose r) * a^(i - r)`. -/
def gsUniHasseBasis {R : Type} [CommRingOps R] (r : Nat) (a : R) (i : Nat) : R :=
  CommRingOps.mul (gsNat (gsChoose i r)) (gsPow a (i - r))

theorem gsUniHasseBasis_zero_succ {R : Type} [LawfulCommRing R] (a : R) (i : Nat) :
    gsUniHasseBasis 0 a (i + 1) = CommRingOps.mul a (gsUniHasseBasis 0 a i) := by
  unfold gsUniHasseBasis
  have h1 : (gsNat (gsChoose (i + 1) 0) : R) = CommRingOps.one :=
    LawfulCommRing.zero_add CommRingOps.one
  have h2 : (gsNat (gsChoose i 0) : R) = CommRingOps.one := by
    cases i <;> exact LawfulCommRing.zero_add CommRingOps.one
  have hsub1 : i + 1 - 0 = i + 1 := rfl
  have hsub2 : i - 0 = i := rfl
  rw [h1, h2, hsub1, hsub2, LawfulCommRing.one_mul, LawfulCommRing.one_mul]
  rfl

theorem gsUniHasseBasis_succ_succ {R : Type} [LawfulCommRing R] (r : Nat) (a : R) (i : Nat) :
    gsUniHasseBasis (r + 1) a (i + 1) =
      CommRingOps.add (gsUniHasseBasis r a i)
        (CommRingOps.mul a (gsUniHasseBasis (r + 1) a i)) := by
  unfold gsUniHasseBasis
  have hsub : (i + 1) - (r + 1) = i - r := Nat.add_sub_add_right i 1 r
  show CommRingOps.mul (gsNat (gsChoose i r + gsChoose i (r + 1))) (gsPow a ((i + 1) - (r + 1))) = _
  rw [hsub, gsNat_add, LawfulCommRing.right_distrib]
  apply congrArg (CommRingOps.add _)
  if hle : i ≤ r then
    have hc0 : gsChoose i (r + 1) = 0 := gsChoose_eq_zero_of_lt i (r + 1) (Nat.lt_succ_of_le hle)
    rw [hc0]
    change CommRingOps.mul CommRingOps.zero _ =
      CommRingOps.mul a (CommRingOps.mul CommRingOps.zero _)
    rw [LawfulCommRing.zero_mul, LawfulCommRing.zero_mul, LawfulCommRing.mul_zero]
  else
    have hstep : i - r = (i - (r + 1)) + 1 := by omega
    rw [hstep]
    show CommRingOps.mul (gsNat (gsChoose i (r + 1)))
        (CommRingOps.mul a (gsPow a (i - (r + 1)))) =
      CommRingOps.mul a (CommRingOps.mul (gsNat (gsChoose i (r + 1))) (gsPow a (i - (r + 1))))
    rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm _ a, LawfulCommRing.mul_assoc]

theorem gs_range_succ_map :
    ∀ (n : Nat), List.range (n + 1) = 0 :: (List.range n).map (· + 1)
  | 0 => rfl
  | n + 1 => by
    conv => lhs; rw [List.range_succ, gs_range_succ_map n]
    conv => rhs; rw [List.range_succ]
    simp [List.map_append]

theorem dotVec_map_add {R : Type} [LawfulCommRing R] {α : Type} (f g : α → R) :
    ∀ (xs : List α) (cs : List R),
      dotVec (xs.map (fun x => CommRingOps.add (f x) (g x))) cs =
        CommRingOps.add (dotVec (xs.map f) cs) (dotVec (xs.map g) cs)
  | [], _ => (LawfulCommRing.add_zero _).symm
  | _ :: _, [] => (LawfulCommRing.add_zero _).symm
  | x :: xs, c :: cs => by
    show CommRingOps.add (CommRingOps.mul (CommRingOps.add (f x) (g x)) c)
        (dotVec (xs.map (fun y => CommRingOps.add (f y) (g y))) cs) =
      CommRingOps.add
        (CommRingOps.add (CommRingOps.mul (f x) c) (dotVec (xs.map f) cs))
        (CommRingOps.add (CommRingOps.mul (g x) c) (dotVec (xs.map g) cs))
    rw [dotVec_map_add f g xs cs, LawfulCommRing.right_distrib, LawfulCommRing.add_add_add_comm]

/-- Equivalence between Horner-Hasse evaluation and binomial dot-product evaluation. -/
theorem gsUniHasse_eq_dotVec {R : Type} [LawfulCommRing R] :
    ∀ (cs : List R) (r : Nat) (a : R),
      gsUniHasse cs r a = dotVec ((List.range cs.length).map (gsUniHasseBasis r a)) cs
  | [], _, _ => rfl
  | c :: cs, 0, a => by
    rw [List.length_cons, gs_range_succ_map, List.map_cons, List.map_map]
    have h0 : gsUniHasseBasis 0 a 0 = (CommRingOps.one : R) := by
      unfold gsUniHasseBasis
      change CommRingOps.mul (CommRingOps.add CommRingOps.zero CommRingOps.one) CommRingOps.one = _
      rw [LawfulCommRing.zero_add, LawfulCommRing.mul_one]
    have hmap : (List.range cs.length).map (gsUniHasseBasis 0 a ∘ (· + 1)) =
        scaleVec a ((List.range cs.length).map (gsUniHasseBasis 0 a)) := by
      rw [scaleVec_eq]
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      exact gsUniHasseBasis_zero_succ a i
    show CommRingOps.add c (CommRingOps.mul a (gsUniHasse cs 0 a)) =
      CommRingOps.add (CommRingOps.mul (gsUniHasseBasis 0 a 0) c)
        (dotVec ((List.range cs.length).map (gsUniHasseBasis 0 a ∘ (· + 1))) cs)
    rw [h0, LawfulCommRing.one_mul, hmap, dotVec_scaleVec, gsUniHasse_eq_dotVec cs 0 a]
  | c :: cs, r + 1, a => by
    rw [List.length_cons, gs_range_succ_map, List.map_cons, List.map_map]
    have h0 : gsUniHasseBasis (r + 1) a 0 = (CommRingOps.zero : R) := by
      unfold gsUniHasseBasis
      change CommRingOps.mul CommRingOps.zero _ = _
      exact LawfulCommRing.zero_mul _
    have hmap : (List.range cs.length).map (gsUniHasseBasis (r + 1) a ∘ (· + 1)) =
        (List.range cs.length).map (fun i =>
          CommRingOps.add (gsUniHasseBasis r a i)
            (CommRingOps.mul a (gsUniHasseBasis (r + 1) a i))) := by
      apply List.map_congr_left
      intro i _
      exact gsUniHasseBasis_succ_succ r a i
    have hscale : (List.range cs.length).map (fun i =>
        CommRingOps.mul a (gsUniHasseBasis (r + 1) a i)) =
        scaleVec a ((List.range cs.length).map (gsUniHasseBasis (r + 1) a)) := by
      rw [scaleVec_eq]
      rw [List.map_map]
      rfl
    show CommRingOps.add (gsUniHasse cs r a) (CommRingOps.mul a (gsUniHasse cs (r + 1) a)) =
      CommRingOps.add (CommRingOps.mul (gsUniHasseBasis (r + 1) a 0) c)
        (dotVec ((List.range cs.length).map (gsUniHasseBasis (r + 1) a ∘ (· + 1))) cs)
    rw [h0, LawfulCommRing.zero_mul, LawfulCommRing.zero_add, hmap, dotVec_map_add,
        hscale, dotVec_scaleVec, gsUniHasse_eq_dotVec cs r a, gsUniHasse_eq_dotVec cs (r + 1) a]

theorem gsUniHasse_trimPoly {F : Type} [LawfulCommRing F] [DecidableEq F] :
    ∀ (cs : List F) (r : Nat) (a : F),
      gsUniHasse (trimPoly cs) r a = gsUniHasse cs r a
  | [], _, _ => rfl
  | c :: cs, r, a => by
    simp only [trimPoly]
    split
    · next h =>
      rcases h with ⟨hcs, hc⟩
      have ih0 := gsUniHasse_trimPoly cs 0 a
      rw [hcs] at ih0
      cases r with
      | zero =>
        show CommRingOps.zero = CommRingOps.add c (CommRingOps.mul a (gsUniHasse cs 0 a))
        rw [hc, ← ih0]
        change CommRingOps.zero = CommRingOps.add CommRingOps.zero (CommRingOps.mul a CommRingOps.zero)
        rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
      | succ r' =>
        have ihr := gsUniHasse_trimPoly cs r' a
        have ihr1 := gsUniHasse_trimPoly cs (r' + 1) a
        rw [hcs] at ihr ihr1
        show CommRingOps.zero =
          CommRingOps.add (gsUniHasse cs r' a) (CommRingOps.mul a (gsUniHasse cs (r' + 1) a))
        rw [← ihr, ← ihr1]
        change CommRingOps.zero = CommRingOps.add CommRingOps.zero (CommRingOps.mul a CommRingOps.zero)
        rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    · cases r with
      | zero =>
        show CommRingOps.add c (CommRingOps.mul a (gsUniHasse (trimPoly cs) 0 a)) =
          CommRingOps.add c (CommRingOps.mul a (gsUniHasse cs 0 a))
        rw [gsUniHasse_trimPoly cs 0 a]
      | succ r' =>
        show CommRingOps.add (gsUniHasse (trimPoly cs) r' a)
            (CommRingOps.mul a (gsUniHasse (trimPoly cs) (r' + 1) a)) =
          CommRingOps.add (gsUniHasse cs r' a) (CommRingOps.mul a (gsUniHasse cs (r' + 1) a))
        rw [gsUniHasse_trimPoly cs r' a, gsUniHasse_trimPoly cs (r' + 1) a]

theorem gsUniHasse_rawAdd {F : Type} [LawfulCommRing F] :
    ∀ (u v : List F) (r : Nat) (a : F),
      gsUniHasse (rawAddCoeffs u v) r a =
        CommRingOps.add (gsUniHasse u r a) (gsUniHasse v r a)
  | [], v, r, a => by
    show gsUniHasse v r a = CommRingOps.add CommRingOps.zero (gsUniHasse v r a)
    exact (LawfulCommRing.zero_add _).symm
  | u, [], r, a => by
    cases u <;> exact (LawfulCommRing.add_zero _).symm
  | c :: cs, d :: ds, 0, a => by
    show CommRingOps.add (CommRingOps.add c d)
        (CommRingOps.mul a (gsUniHasse (rawAddCoeffs cs ds) 0 a)) =
      CommRingOps.add
        (CommRingOps.add c (CommRingOps.mul a (gsUniHasse cs 0 a)))
        (CommRingOps.add d (CommRingOps.mul a (gsUniHasse ds 0 a)))
    rw [gsUniHasse_rawAdd cs ds 0 a, LawfulCommRing.left_distrib, LawfulCommRing.add_add_add_comm]
  | _ :: cs, _ :: ds, r + 1, a => by
    show CommRingOps.add (gsUniHasse (rawAddCoeffs cs ds) r a)
        (CommRingOps.mul a (gsUniHasse (rawAddCoeffs cs ds) (r + 1) a)) =
      CommRingOps.add
        (CommRingOps.add (gsUniHasse cs r a) (CommRingOps.mul a (gsUniHasse cs (r + 1) a)))
        (CommRingOps.add (gsUniHasse ds r a) (CommRingOps.mul a (gsUniHasse ds (r + 1) a)))
    rw [gsUniHasse_rawAdd cs ds r a, gsUniHasse_rawAdd cs ds (r + 1) a,
        LawfulCommRing.left_distrib, LawfulCommRing.add_add_add_comm]

theorem gsUniHasse_map_mul {F : Type} [LawfulCommRing F] (c : F) :
    ∀ (u : List F) (r : Nat) (a : F),
      gsUniHasse (u.map (CommRingOps.mul c)) r a =
        CommRingOps.mul c (gsUniHasse u r a)
  | [], _, _ => (LawfulCommRing.mul_zero c).symm
  | x :: xs, 0, a => by
    show CommRingOps.add (CommRingOps.mul c x)
        (CommRingOps.mul a (gsUniHasse (xs.map (CommRingOps.mul c)) 0 a)) =
      CommRingOps.mul c (CommRingOps.add x (CommRingOps.mul a (gsUniHasse xs 0 a)))
    rw [gsUniHasse_map_mul c xs 0 a, LawfulCommRing.left_distrib,
        ← LawfulCommRing.mul_assoc a c _, LawfulCommRing.mul_comm a c, LawfulCommRing.mul_assoc]
  | _ :: xs, r + 1, a => by
    show CommRingOps.add (gsUniHasse (xs.map (CommRingOps.mul c)) r a)
        (CommRingOps.mul a (gsUniHasse (xs.map (CommRingOps.mul c)) (r + 1) a)) =
      CommRingOps.mul c
        (CommRingOps.add (gsUniHasse xs r a) (CommRingOps.mul a (gsUniHasse xs (r + 1) a)))
    rw [gsUniHasse_map_mul c xs r a, gsUniHasse_map_mul c xs (r + 1) a,
        LawfulCommRing.left_distrib,
        ← LawfulCommRing.mul_assoc a c _, LawfulCommRing.mul_comm a c, LawfulCommRing.mul_assoc]

theorem gsConst_mul_val {F : Type} [LawfulField F] [DecidableEq F]
    (c : F) (p : GsUniPoly F) :
    (CommRingOps.mul (gsConst c) p).coeffs = pScale c p.coeffs := by
  show pMul (trimPoly [c]) p.coeffs = pScale c p.coeffs
  rw [pMul_trimPoly_left]
  unfold pMul; rw [pScale_eq]
  rw [trimPoly_eq_iff_coeffAt]
  intro k
  simp only [rawMul, coeffAt_addCoeffs]
  cases k with
  | zero => rw [coeffAt_cons_zero, LawfulCommRing.add_zero]
  | succ k' => rw [coeffAt_cons_succ, coeffAt_nil, LawfulCommRing.add_zero]

theorem gsUniHasse_bivariate_comm {F : Type} [LawfulField F] [DecidableEq F]
    (r : Nat) (a b : F) :
    ∀ (Q : List (GsUniPoly F)) (s : Nat),
      gsUniHasse (gsUniHasse Q s (gsConst b)).coeffs r a =
        gsUniHasse (Q.map (fun p => gsUniHasse p.coeffs r a)) s b
  | [], _ => rfl
  | q₀ :: qs, 0 => by
    show gsUniHasse (CommRingOps.add q₀ (CommRingOps.mul (gsConst b) (gsUniHasse qs 0 (gsConst b)))).coeffs r a =
      CommRingOps.add (gsUniHasse q₀.coeffs r a)
        (CommRingOps.mul b (gsUniHasse (qs.map (fun p => gsUniHasse p.coeffs r a)) 0 b))
    change gsUniHasse (pAdd q₀.coeffs (CommRingOps.mul (gsConst b) (gsUniHasse qs 0 (gsConst b))).coeffs) r a = _
    rw [pAdd_eq, gsUniHasse_trimPoly, gsUniHasse_rawAdd, gsConst_mul_val,
        pScale_eq, gsUniHasse_trimPoly, gsUniHasse_map_mul, gsUniHasse_bivariate_comm r a b qs 0]
  | _ :: qs, s + 1 => by
    show gsUniHasse (CommRingOps.add (gsUniHasse qs s (gsConst b))
        (CommRingOps.mul (gsConst b) (gsUniHasse qs (s + 1) (gsConst b)))).coeffs r a =
      CommRingOps.add (gsUniHasse (qs.map (fun p => gsUniHasse p.coeffs r a)) s b)
        (CommRingOps.mul b (gsUniHasse (qs.map (fun p => gsUniHasse p.coeffs r a)) (s + 1) b))
    change gsUniHasse (pAdd (gsUniHasse qs s (gsConst b)).coeffs
        (CommRingOps.mul (gsConst b) (gsUniHasse qs (s + 1) (gsConst b))).coeffs) r a = _
    rw [pAdd_eq, gsUniHasse_trimPoly, gsUniHasse_rawAdd, gsConst_mul_val,
        pScale_eq, gsUniHasse_trimPoly, gsUniHasse_map_mul,
        gsUniHasse_bivariate_comm r a b qs s, gsUniHasse_bivariate_comm r a b qs (s + 1)]

/-- Slice a flat vector into consecutive blocks of prescribed widths. -/
def gsVarX {F : Type} [LawfulField F] [DecidableEq F] : GsUniPoly F :=
  ⟨[CommRingOps.zero, CommRingOps.one], by simp [trimPoly, LawfulField.one_ne_zero]⟩

theorem gsConst_zero {F : Type} [LawfulField F] [DecidableEq F] :
    (gsConst CommRingOps.zero : GsUniPoly F) = CommRingOps.zero := by
  apply UPoly.ext
  show trimPoly [CommRingOps.zero] = []
  simp [trimPoly]

theorem gsVarX_sub_gsConst {F : Type} [LawfulField F] [DecidableEq F] (a : F) :
    CommRingOps.sub gsVarX (gsConst a) = gsLinear a := by
  apply UPoly.ext
  apply eq_of_isTrimmed_coeffAt _ _ (CommRingOps.sub gsVarX (gsConst a)).trimmed (gsLinear_trimmed a)
  intro k
  change coeffAt (pSub [CommRingOps.zero, CommRingOps.one] (trimPoly [a])) k =
    coeffAt [CommRingOps.neg a, CommRingOps.one] k
  rw [coeffAt_pSub, coeffAt_trimPoly]
  cases k with
  | zero =>
    simp [coeffAt, LawfulCommRing.sub_eq_add_neg, LawfulCommRing.zero_add]
  | succ k' =>
    cases k' <;> simp [coeffAt, LawfulCommRing.sub_zero]

theorem evalCoeffs_map_gsConst_gsVarX {F : Type} [LawfulField F] [DecidableEq F] :
    ∀ (cs : List F), evalCoeffs (cs.map gsConst) gsVarX = GsUniPoly.ofCoeffs cs
  | [] => rfl
  | c :: cs => by
    show CommRingOps.add (gsConst c) (CommRingOps.mul gsVarX (evalCoeffs (cs.map gsConst) gsVarX)) =
      GsUniPoly.ofCoeffs (c :: cs)
    rw [evalCoeffs_map_gsConst_gsVarX cs]
    apply UPoly.ext
    apply eq_of_isTrimmed_coeffAt _ _
      (CommRingOps.add (gsConst c) (CommRingOps.mul gsVarX (GsUniPoly.ofCoeffs cs))).trimmed
      (trimPoly_idem (c :: cs))
    intro k
    change coeffAt (pAdd (trimPoly [c]) (pMul [CommRingOps.zero, CommRingOps.one] (trimPoly cs))) k =
      coeffAt (trimPoly (c :: cs)) k
    rw [coeffAt_pAdd, coeffAt_trimPoly, pMul, coeffAt_trimPoly, coeffAt_trimPoly,
        rawMul, coeffAt_addCoeffs, coeffAt_map_mul, LawfulCommRing.zero_mul,
        LawfulCommRing.zero_add]
    cases k with
    | zero =>
      rw [coeffAt_cons_zero, coeffAt_cons_zero, coeffAt_cons_zero, LawfulCommRing.add_zero]
    | succ k' =>
      rw [coeffAt_cons_succ, coeffAt_nil, LawfulCommRing.zero_add,
          coeffAt_cons_succ, coeffAt_cons_succ,
          rawMul, coeffAt_addCoeffs, coeffAt_map_mul, LawfulCommRing.one_mul, coeffAt_trimPoly]
      cases k' with
      | zero => rw [coeffAt_cons_zero, LawfulCommRing.add_zero]
      | succ k'' => rw [coeffAt_cons_succ, rawMul, coeffAt_nil, LawfulCommRing.add_zero]

theorem gsConst_add {F : Type} [LawfulField F] [DecidableEq F] (x y : F) :
    gsConst (CommRingOps.add x y) = CommRingOps.add (gsConst x) (gsConst y) := by
  apply UPoly.ext
  apply eq_of_isTrimmed_coeffAt _ _ (trimPoly_idem _) (CommRingOps.add (gsConst x) (gsConst y)).trimmed
  intro k
  change coeffAt (trimPoly [CommRingOps.add x y]) k =
    coeffAt (pAdd (trimPoly [x]) (trimPoly [y])) k
  rw [coeffAt_pAdd, coeffAt_trimPoly, coeffAt_trimPoly, coeffAt_trimPoly]
  cases k <;> simp [coeffAt, LawfulCommRing.add_zero]

theorem gsConst_mul {F : Type} [LawfulField F] [DecidableEq F] (x y : F) :
    gsConst (CommRingOps.mul x y) = CommRingOps.mul (gsConst x) (gsConst y) := by
  apply UPoly.ext
  show trimPoly [CommRingOps.mul x y] = (CommRingOps.mul (gsConst x) (gsConst y)).coeffs
  rw [gsConst_mul_val]
  rw [pScale_eq]
  rw [trimPoly_eq_iff_coeffAt]
  intro k
  change coeffAt [CommRingOps.mul x y] k = coeffAt (List.map (CommRingOps.mul x) (trimPoly [y])) k
  rw [coeffAt_map_mul, coeffAt_trimPoly]
  cases k <;> simp [coeffAt, LawfulCommRing.mul_zero]

theorem evalCoeffs_map_gsConst {F : Type} [LawfulField F] [DecidableEq F] (a : F) :
    ∀ (cs : List F), evalCoeffs (cs.map gsConst) (gsConst a) = gsConst (evalCoeffs cs a)
  | [] => gsConst_zero.symm
  | c :: cs => by
    show CommRingOps.add (gsConst c) (CommRingOps.mul (gsConst a) (evalCoeffs (cs.map gsConst) (gsConst a))) =
      gsConst (CommRingOps.add c (CommRingOps.mul a (evalCoeffs cs a)))
    rw [evalCoeffs_map_gsConst a cs, ← gsConst_mul, ← gsConst_add]

theorem quotLinear_map_gsConst {F : Type} [LawfulField F] [DecidableEq F] (a : F) :
    ∀ (cs : List F), quotLinear (cs.map gsConst) (gsConst a) = (quotLinear cs a).map gsConst
  | [] => rfl
  | [_] => rfl
  | _ :: c₁ :: tl => by
    show evalCoeffs ((c₁ :: tl).map gsConst) (gsConst a) ::
        quotLinear ((c₁ :: tl).map gsConst) (gsConst a) =
      gsConst (evalCoeffs (c₁ :: tl) a) :: (quotLinear (c₁ :: tl) a).map gsConst
    rw [evalCoeffs_map_gsConst, quotLinear_map_gsConst a (c₁ :: tl)]

theorem gsTaylor_map_gsConst {F : Type} [LawfulField F] [DecidableEq F] (a : F) :
    ∀ (n : Nat) (cs : List F),
      gsTaylor n (cs.map gsConst) (gsConst a) = (gsTaylor n cs a).map gsConst
  | 0, _ => rfl
  | n + 1, cs => by
    show evalCoeffs (cs.map gsConst) (gsConst a) ::
        gsTaylor n (quotLinear (cs.map gsConst) (gsConst a)) (gsConst a) =
      gsConst (evalCoeffs cs a) :: (gsTaylor n (quotLinear cs a) a).map gsConst
    rw [evalCoeffs_map_gsConst, quotLinear_map_gsConst, gsTaylor_map_gsConst a n]

theorem coeffAt_map_gsConst {F : Type} [LawfulField F] [DecidableEq F] :
    ∀ (cs : List F) (r : Nat), coeffAt (cs.map gsConst) r = gsConst (coeffAt cs r)
  | [], _ => gsConst_zero.symm
  | _ :: _, 0 => rfl
  | _ :: cs, r + 1 => coeffAt_map_gsConst cs r


end Qsag

namespace Qsag
open CommRingOps
open RoundPoly
theorem gsTaylor_zero {R : Type} [CommRingOps R] (cs : List R) (b : R) : gsTaylor 0 cs b = [] := by rfl
theorem gsTaylor_succ {R : Type} [CommRingOps R] (n : Nat) (cs : List R) (b : R) : gsTaylor (n+1) cs b = evalCoeffs cs b :: gsTaylor n (quotLinear cs b) b := by rfl
theorem gsConst_coeffs {F : Type} [LawfulField F] [DecidableEq F] (b : F) : (gsConst b).coeffs = trimPoly [b] := by rfl
end Qsag

namespace Qsag
open CommRingOps RoundPoly UPoly
/-! ## Polynomial lemmas -/

namespace UPoly

theorem coeffAt_tail {R : Type} [LawfulCommRing R] :
    ∀ (l : List R) (k : Nat), coeffAt l.tail k = coeffAt l (k + 1)
  | [], k => by rw [List.tail_nil, coeffAt_nil, coeffAt_nil]
  | _ :: _, k => by rw [List.tail_cons, coeffAt_cons_succ]

section Ring
variable {R : Type} [LawfulCommRing R] [DecidableEq R]

theorem eval_zero_eq (p : UPoly R) : p.eval zero = coeffAt p.coeffs 0 := by
  rw [eval_eq]
  generalize p.coeffs = l
  cases l with
  | nil => rfl
  | cons c cs =>
    show add c (mul zero (evalCoeffs cs zero)) = c
    rw [LawfulCommRing.zero_mul, LawfulCommRing.add_zero]

/-- Drop the constant term and divide by the variable. -/
def shiftDown (p : UPoly R) : UPoly R := ofList p.coeffs.tail

