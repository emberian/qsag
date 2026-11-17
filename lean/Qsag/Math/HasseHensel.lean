module
public import Qsag.Math.PolyRing
import Qsag.Tactic.AssuranceKit

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

theorem coeffAt_shiftDown (p : UPoly R) (k : Nat) :
    coeffAt (shiftDown p).coeffs k = coeffAt p.coeffs (k + 1) := by
  show coeffAt (ofList p.coeffs.tail).coeffs k = _
  rw [coeffAt_ofList, coeffAt_tail]

/-- Split off the constant term: `a = a₀ + X · a'`. -/
theorem eq_C_add_X_mul (a : UPoly R) :
    a = add (C (coeffAt a.coeffs 0)) (mul X (shiftDown a)) :=
  ext_coeffAt fun k => by
    rw [coeffAt_add]
    cases k with
    | zero => rw [coeffAt_C_zero, coeffAt_X_mul_zero, LawfulCommRing.add_zero]
    | succ k =>
      rw [coeffAt_C_succ, coeffAt_X_mul_succ, coeffAt_shiftDown, LawfulCommRing.zero_add]

theorem hom_split {S : Type} [LawfulCommRing S] (ψ : RingHom (UPoly R) S) (p : UPoly R) :
    ψ.toFun p = add (ψ.toFun (C (coeffAt p.coeffs 0))) (mul (ψ.toFun X) (ψ.toFun (shiftDown p))) :=
  (congrArg ψ.toFun (eq_C_add_X_mul p)).trans (by rw [ψ.map_add, ψ.map_mul])

/-- Homomorphisms out of `R[X]` are determined on constants and the variable. -/
theorem hom_ext {S : Type} [LawfulCommRing S]
    (φ ψ : RingHom (UPoly R) S) (hC : ∀ c, φ.toFun (C c) = ψ.toFun (C c))
    (hX : φ.toFun X = ψ.toFun X) (p : UPoly R) : φ.toFun p = ψ.toFun p := by
  have key : ∀ l : List R, φ.toFun (ofList l) = ψ.toFun (ofList l) := by
    intro l
    induction l with
    | nil => exact φ.map_zero.trans ψ.map_zero.symm
    | cons c cs ih => rw [ofList_cons, φ.map_add, φ.map_mul, ψ.map_add, ψ.map_mul, hC, hX, ih]
  have := key p.coeffs
  rwa [ofList_coeffs] at this

theorem eval₂_congr {S : Type} [LawfulCommRing S] (φ ψ : RingHom R S)
    (h : ∀ c, φ.toFun c = ψ.toFun c) (s : S) (p : UPoly R) : eval₂ φ s p = eval₂ ψ s p := by
  show evalCoeffs (p.coeffs.map φ.toFun) s = evalCoeffs (p.coeffs.map ψ.toFun) s
  rw [List.map_congr_left (fun c _ => h c)]

theorem taylorShift_C (b c : R) : (taylorShift b).toFun (C c) = C c := eval₂_C _ _ _

theorem taylorShift_X (b : R) : (taylorShift b).toFun X = add (C b) X := eval₂_X _ _

/-- A polynomial is the evaluation of its constant-lifted coefficients at the variable. -/
theorem evalCoeffs_C_X (p : UPoly R) : evalCoeffs (p.coeffs.map (CHom (R := R)).toFun) X = p := by
  have h := mapHom_apply (RingHom.id R) p
  have e : (mapHom (RingHom.id R)).toFun p = evalCoeffs (p.coeffs.map (CHom (R := R)).toFun) X :=
    rfl
  rw [← e, h]
  show ofList (p.coeffs.map (fun a => a)) = p
  rw [List.map_id', ofList_coeffs]

theorem natDeg_C_eq (c : R) : (C c).natDeg = 0 :=
  Nat.le_zero.mp (natDeg_le_of_coeffAt _ 0 (fun k hk => by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact coeffAt_C_succ c j))

theorem wdeg_C_le (w : R → Nat) (s : Nat) (c : R) : (C c).wdeg w s ≤ w c := by
  apply wdeg_le
  intro k hk
  cases k with
  | zero => rw [coeffAt_C_zero]; exact Nat.le_refl _
  | succ k => exact absurd (coeffAt_C_succ c k) hk

theorem wdeg_X_le (w : R → Nat) (s : Nat) : (X : UPoly R).wdeg w s ≤ w one + s := by
  apply wdeg_le
  intro k hk
  have e : coeffAt (X : UPoly R).coeffs k = coeffAt [zero, one] k := coeffAt_ofList _ k
  rw [e] at hk ⊢
  cases k with
  | zero => exact absurd rfl hk
  | succ k =>
    cases k with
    | zero => show w one + s * 1 ≤ w one + s; rw [Nat.mul_one]; exact Nat.le_refl _
    | succ k => exact absurd rfl hk

/-- Coefficients after the scaling `X ↦ c·X`. -/
theorem coeffAt_scale (c : R) : ∀ (l : List R) (j : Nat),
    coeffAt (evalCoeffs (l.map (CHom (R := R)).toFun) (mul (C c) X)).coeffs j =
      mul (CRing.npow c j) (coeffAt l j)
  | [], j => by
    show coeffAt (zero : UPoly R).coeffs j = _
    rw [coeffs_zero, coeffAt_nil, LawfulCommRing.mul_zero]
  | a :: l, 0 => by
    show coeffAt (add (C a) (mul (mul (C c) X)
      (evalCoeffs (l.map (CHom (R := R)).toFun) (mul (C c) X)))).coeffs 0 = mul one a
    rw [coeffAt_add, coeffAt_C_zero, LawfulCommRing.mul_assoc, coeffAt_C_mul, coeffAt_X_mul_zero,
      LawfulCommRing.mul_zero, LawfulCommRing.add_zero, LawfulCommRing.one_mul]
  | a :: l, j + 1 => by
    show coeffAt (add (C a) (mul (mul (C c) X)
      (evalCoeffs (l.map (CHom (R := R)).toFun) (mul (C c) X)))).coeffs (j + 1) =
        mul (mul (CRing.npow c j) c) (coeffAt (a :: l) (j + 1))
    rw [coeffAt_add, coeffAt_C_succ, LawfulCommRing.zero_add, LawfulCommRing.mul_assoc,
      coeffAt_C_mul, coeffAt_X_mul_succ, coeffAt_scale c l j, coeffAt_cons_succ]
    generalize CRing.npow c j = p
    constructive_ring

end Ring
end UPoly

/-! ## Powers of a principal ideal -/

/-- `x ∈ u^k · S`. -/
def InPow {S : Type} [CommRingOps S] (u : S) (k : Nat) (x : S) : Prop :=
  ∃ q, x = mul (CRing.npow u k) q

namespace InPow
variable {S : Type} [LawfulCommRing S]

theorem base (u x : S) : InPow u 0 x := ⟨x, (LawfulCommRing.one_mul x).symm⟩

theorem zero_mem (u : S) (k : Nat) : InPow u k zero := ⟨zero, (LawfulCommRing.mul_zero _).symm⟩

theorem add_mem {u : S} {k : Nat} {x y : S} (hx : InPow u k x) (hy : InPow u k y) :
    InPow u k (add x y) := by
  obtain ⟨q, rfl⟩ := hx
  obtain ⟨q', rfl⟩ := hy
  exact ⟨add q q', (LawfulCommRing.left_distrib _ _ _).symm⟩

theorem mul_mem {u : S} {k : Nat} {x : S} (a : S) (hx : InPow u k x) : InPow u k (mul a x) := by
  obtain ⟨q, rfl⟩ := hx
  refine ⟨mul a q, ?_⟩
  generalize CRing.npow u k = p
  constructive_ring

theorem step {u : S} {k : Nat} {x : S} (w : S) (hx : InPow u k x) :
    InPow u (k + 1) (mul (mul u w) x) := by
  obtain ⟨q, rfl⟩ := hx
  refine ⟨mul w q, ?_⟩
  show _ = mul (mul (CRing.npow u k) u) (mul w q)
  generalize CRing.npow u k = p
  constructive_ring

theorem of_one {u x : S} (h : InPow u 1 x) : ∃ a, x = mul u a := by
  obtain ⟨q, hq⟩ := h
  exact ⟨q, hq.trans (by show mul (mul one u) q = mul u q; rw [LawfulCommRing.one_mul])⟩

theorem to_one (u a : S) : InPow u 1 (mul u a) :=
  ⟨a, by show mul u a = mul (mul one u) a; rw [LawfulCommRing.one_mul]⟩

theorem mono {u : S} {j k : Nat} {x : S} (hjk : j ≤ k) (hx : InPow u k x) : InPow u j x := by
  obtain ⟨q, rfl⟩ := hx
  obtain ⟨i, rfl⟩ : ∃ i, k = j + i := ⟨k - j, by omega⟩
  exact ⟨mul (CRing.npow u i) q, by rw [CRing.npow_add, LawfulCommRing.mul_assoc]⟩

/-- A polynomial with vanishing coefficients below `k`, evaluated at `u`, lies in `u^k`. -/
theorem evalCoeffs_low {R : Type} [LawfulCommRing R] (φ : RingHom R S) (u : S) :
    ∀ (k : Nat) (l : List R), (∀ r, r < k → coeffAt l r = zero) →
      InPow u k (evalCoeffs (l.map φ.toFun) u)
  | 0, _, _ => base u _
  | _ + 1, [], _ => zero_mem u _
  | k + 1, c :: cs, h => by
    have hc : c = zero := h 0 (Nat.succ_pos k)
    obtain ⟨q, hq⟩ := evalCoeffs_low φ u k cs (fun r hr => by
      have := h (r + 1) (Nat.succ_lt_succ hr)
      rwa [coeffAt_cons_succ] at this)
    refine ⟨q, ?_⟩
    show add (φ.toFun c) (mul u (evalCoeffs (cs.map φ.toFun) u)) =
      mul (mul (CRing.npow u k) u) q
    rw [hq, hc, φ.map_zero]
    generalize CRing.npow u k = p
    constructive_ring

/-- Evaluating a polynomial whose coefficients all lie in `u^k`. -/
theorem evalCoeffs_all (u y : S) (k : Nat) : ∀ l : List S, (∀ t, InPow u k (coeffAt l t)) →
    InPow u k (evalCoeffs l y)
  | [], _ => zero_mem u k
  | c :: cs, h =>
    add_mem (h 0) (mul_mem y (evalCoeffs_all u y k cs (fun t => by
      have := h (t + 1)
      rwa [coeffAt_cons_succ] at this)))

/-- If the coefficient of `Z^s` lies in `u^(m - s)`, evaluating at `Z = u·w` lands in `u^m`. -/
theorem evalCoeffs_graded (u w : S) : ∀ (l : List S) (m : Nat),
    (∀ s, InPow u (m - s) (coeffAt l s)) → InPow u m (evalCoeffs l (mul u w))
  | [], m, _ => zero_mem u m
  | _ :: _, 0, _ => base u _
  | c :: cs, m + 1, h => by
    have hc := h 0
    rw [Nat.sub_zero, coeffAt_cons_zero] at hc
    have ih := evalCoeffs_graded u w cs m (fun s => by
      have := h (s + 1)
      rwa [coeffAt_cons_succ, Nat.add_sub_add_right] at this)
    exact add_mem hc (step w ih)

end InPow

namespace UPoly
variable {R : Type} [LawfulCommRing R] [DecidableEq R]

/-- `X^k ∣ p` when the coefficients of `p` below `k` vanish. -/
theorem inPow_of_coeff_zero (p : UPoly R) (k : Nat)
    (h : ∀ j, j < k → coeffAt p.coeffs j = zero) : InPow X k p := by
  have := InPow.evalCoeffs_low (CHom (R := R)) X k p.coeffs h
  rwa [evalCoeffs_C_X] at this

/-- The coefficients of a multiple of `X^k` below `k` vanish. -/
theorem coeff_zero_of_inPow : ∀ (k : Nat) (p : UPoly R), InPow X k p →
    ∀ j, j < k → coeffAt p.coeffs j = zero
  | 0, _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | k + 1, p, ⟨q, hq⟩, j, hj => by
    have e : p = mul X (mul (CRing.npow X k) q) := by
      rw [hq]
      show mul (mul (CRing.npow X k) X) q = _
      generalize CRing.npow (X : UPoly R) k = P
      constructive_ring
    rw [e]
    cases j with
    | zero => exact coeffAt_X_mul_zero _
    | succ j =>
      rw [coeffAt_X_mul_succ]
      exact coeff_zero_of_inPow k _ ⟨q, rfl⟩ j (Nat.lt_of_succ_lt_succ hj)

end UPoly

/-! ## The fixed-point operator -/

namespace RingHom
variable {R S : Type} [LawfulCommRing R] [LawfulCommRing S]

/-- Synthetic division by `X - r` commutes with ring homomorphisms. -/
theorem map_quotLinear (φ : RingHom R S) (r : R) : ∀ l : List R,
    (quotLinear l r).map φ.toFun = quotLinear (l.map φ.toFun) (φ.toFun r)
  | [] => rfl
  | [_] => rfl
  | _ :: c₁ :: cs => by
    show φ.toFun (evalCoeffs (c₁ :: cs) r) :: (quotLinear (c₁ :: cs) r).map φ.toFun =
      evalCoeffs ((c₁ :: cs).map φ.toFun) (φ.toFun r) ::
        quotLinear ((c₁ :: cs).map φ.toFun) (φ.toFun r)
    rw [map_quotLinear φ r (c₁ :: cs), RingHom.map_evalCoeffs]

end RingHom

namespace UPoly

section Ring
variable {R S : Type} [LawfulCommRing R] [DecidableEq R] [LawfulCommRing S]

/-- The derivative at `z` by synthetic division: `(p(U) - p(z))/(U - z)` at `U = z`. -/
theorem evalCoeffs_quotLinear_self (g : List S) (z : S) :
    evalCoeffs (quotLinear g z) z = gsUniHasse g 1 z :=
  (gsUniHasse_zero_eq_evalCoeffs _ _).symm.trans (gsUniHasse_quotLinear g 0 z)

/-- The image of a Hasse derivative under `eval₂`. -/
theorem eval₂_hasse (χ : RingHom R S) (z : S) (k : Nat) (Q : UPoly R) :
    eval₂ χ z (hasse k Q) = gsUniHasse (Q.coeffs.map χ.toFun) k z := by
  show (eval₂Hom χ z).toFun (gsUniHasse (Q.coeffs.map C) k X) = _
  rw [RingHom.map_gsUniHasse, List.map_map]
  show gsUniHasse (Q.coeffs.map (fun c => eval₂ χ z (C c))) k (eval₂ χ z X) = _
  rw [eval₂_X]
  congr 1
  exact List.map_congr_left (fun c _ => eval₂_C χ z c)

/-- Shifting by `t` and then by `-t` is the identity. -/
theorem taylorShift_neg_cancel (t : R) (p : UPoly R) :
    (taylorShift (neg t)).toFun ((taylorShift t).toFun p) = p := by
  show (taylorShift (neg t)).toFun (eval₂ CHom (add (C t) X) p) = p
  rw [hom_eval₂, RingHom.map_add]
  have h1 : (taylorShift (neg t)).toFun (C t) = C t := eval₂_C _ _ _
  have h2 : (taylorShift (neg t)).toFun X = add (C (neg t)) X := eval₂_X _ _
  have h3 : add (C t) (add (C (neg t)) X) = (X : UPoly R) := by
    rw [← LawfulCommRing.add_assoc, ← CHom_apply t, ← CHom_apply (neg t), ← CHom.map_add,
      LawfulCommRing.add_right_neg, CHom.map_zero, LawfulCommRing.zero_add]
  rw [h1, h2, h3]
  have h4 : eval₂ ((taylorShift (neg t)).comp CHom) X p =
      (mapHom (RingHom.id R)).toFun p := by
    show evalCoeffs (p.coeffs.map _) X = evalCoeffs (p.coeffs.map _) X
    congr 1
    exact List.map_congr_left (fun c _ => eval₂_C _ _ c)
  rw [h4, mapHom_apply]
  show ofList (p.coeffs.map (fun a => a)) = p
  rw [List.map_id', ofList_coeffs]

end Ring

section Field
variable {K : Type} [LawfulField K] [DecidableEq K]

/-- In `K[W]`, a factor with nonzero constant term cancels modulo `W^n`. -/
theorem trunc_cancel : ∀ (n : Nat) (a b : UPoly K), coeffAt b.coeffs 0 ≠ zero →
    (∀ k, k < n → coeffAt (mul a b).coeffs k = zero) → ∀ k, k < n → coeffAt a.coeffs k = zero
  | 0, _, _, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, a, b, hb, h, k, hk => by
    have ha := eq_C_add_X_mul a
    have hmul : mul a b = add (mul (C (coeffAt a.coeffs 0)) b)
        (mul X (mul (shiftDown a) b)) := by
      have e : mul (add (C (coeffAt a.coeffs 0)) (mul X (shiftDown a))) b =
          add (mul (C (coeffAt a.coeffs 0)) b) (mul X (mul (shiftDown a) b)) := by
        constructive_ring
      rw [← ha] at e; exact e
    have h0 := h 0 (by omega)
    rw [hmul, coeffAt_add, coeffAt_C_mul, coeffAt_X_mul_zero, LawfulCommRing.add_zero] at h0
    have hc : coeffAt a.coeffs 0 = zero :=
      (LawfulField.mul_eq_zero h0).elim id (fun e => absurd e hb)
    have htail : ∀ j, j < n → coeffAt (mul (shiftDown a) b).coeffs j = zero := by
      intro j hj
      have := h (j + 1) (by omega)
      rw [hmul, coeffAt_add, coeffAt_C_mul, coeffAt_X_mul_succ, hc, LawfulCommRing.zero_mul,
        LawfulCommRing.zero_add] at this
      exact this
    have ih := trunc_cancel n (shiftDown a) b hb htail
    cases k with
    | zero => exact hc
    | succ k =>
      have := ih k (by omega)
      rwa [coeffAt_shiftDown] at this

/-- **Hensel uniqueness** (`[CWYZ26]` Lemma 3.11, uniqueness). Let `Q` have coefficients in
    a ring mapping to `K[W]` by `ψ`, so that `e ↦ eval₂ ψ e Q` is `E ↦ G(W, E)`. If `e₁` and
    `e₂` have the same constant term `z₀`, both solve `G(W, E) ≡ 0 (mod W^n)`, and
    `∂_U G(0, z₀) ≠ 0`, then `e₁ ≡ e₂ (mod W^n)`. -/
theorem hensel_unique {B : Type} [LawfulCommRing B] [DecidableEq B] (Q : UPoly B)
    (ψ : RingHom B (UPoly K)) (e₁ e₂ : UPoly K) (z₀ : K) (h₁ : e₁.eval zero = z₀)
    (h₂ : e₂.eval zero = z₀)
    (hS : eval₂ ((evalHom zero).comp ψ) z₀ (hasse 1 Q) ≠ zero) (n : Nat)
    (hr₁ : ∀ k, k < n → coeffAt (eval₂ ψ e₁ Q).coeffs k = zero)
    (hr₂ : ∀ k, k < n → coeffAt (eval₂ ψ e₂ Q).coeffs k = zero) :
    ∀ k, k < n → coeffAt e₁.coeffs k = coeffAt e₂.coeffs k := by
  have hfac := evalCoeffs_eq_mul_quotLinear_add (Q.coeffs.map ψ.toFun) e₂ e₁
  have hH : coeffAt (evalCoeffs (quotLinear (Q.coeffs.map ψ.toFun) e₂) e₁).coeffs 0 ≠ zero := by
    rw [← eval_zero_eq]
    show (evalHom (zero : K)).toFun (evalCoeffs (quotLinear (Q.coeffs.map ψ.toFun) e₂) e₁) ≠ zero
    rw [RingHom.map_evalCoeffs, RingHom.map_quotLinear, List.map_map, evalHom_apply,
      evalHom_apply, h₁, h₂, evalCoeffs_quotLinear_self]
    rw [eval₂_hasse] at hS
    exact hS
  have hdiff : ∀ k, k < n → coeffAt (mul (sub e₁ e₂)
      (evalCoeffs (quotLinear (Q.coeffs.map ψ.toFun) e₂) e₁)).coeffs k = zero := by
    intro k hk
    have e : mul (sub e₁ e₂) (evalCoeffs (quotLinear (Q.coeffs.map ψ.toFun) e₂) e₁) =
        sub (eval₂ ψ e₁ Q) (eval₂ ψ e₂ Q) := by
      show _ = sub (evalCoeffs (Q.coeffs.map ψ.toFun) e₁) (evalCoeffs (Q.coeffs.map ψ.toFun) e₂)
      rw [hfac]; constructive_ring
    rw [e, coeffAt_sub, hr₁ k hk, hr₂ k hk, LawfulCommRing.sub_self]
  intro k hk
  have := trunc_cancel n _ _ hH hdiff k hk
  rw [coeffAt_sub] at this
  exact LawfulCommRing.sub_eq_zero_iff.mp this

end Field
end UPoly

/-- A decidable predicate fails throughout `0..n`, or has a first point where it holds. -/
theorem first_or_none (p : Nat → Prop) [DecidablePred p] : ∀ n,
    (∀ k, k ≤ n → ¬ p k) ∨ ∃ μ, μ ≤ n ∧ p μ ∧ ∀ k, k < μ → ¬ p k
  | 0 =>
    if h : p 0 then .inr ⟨0, Nat.le_refl 0, h, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
    else .inl (fun k hk => by
      obtain rfl : k = 0 := Nat.le_zero.mp hk
      exact h)
  | n + 1 => by
    rcases first_or_none p n with hall | ⟨μ, hμ, hp, hlt⟩
    · if h : p (n + 1) then
        exact .inr ⟨n + 1, Nat.le_refl _, h, fun k hk => hall k (Nat.le_of_lt_succ hk)⟩
      else
        refine .inl (fun k hk => ?_)
        if hk' : k ≤ n then exact hall k hk'
        else
          obtain rfl : k = n + 1 := by omega
          exact h
    · exact .inr ⟨μ, Nat.le_succ_of_le hμ, hp, hlt⟩

namespace RingHom

theorem map_natCast {R S : Type} [LawfulCommRing R] [LawfulCommRing S] (φ : RingHom R S) :
    ∀ n : Nat, φ.toFun (CRing.natCast n) = CRing.natCast n
  | 0 => φ.map_zero
  | n + 1 => by
    rw [CRing.natCast_succ, CRing.natCast_succ, φ.map_add, map_natCast φ n, φ.map_one]

end RingHom

/-! ## Composition of Hasse derivatives -/

namespace UPoly

theorem gsUniHasse_eq_zero_of_length_le {S : Type} [LawfulCommRing S] (s : S) :
    ∀ (l : List S) (k : Nat), l.length ≤ k → gsUniHasse l k s = zero
  | [], _, _ => rfl
  | _ :: _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | _ :: cs, k + 1, h => by
    show add (gsUniHasse cs k s) (mul s (gsUniHasse cs (k + 1) s)) = zero
    rw [gsUniHasse_eq_zero_of_length_le s cs k (Nat.le_of_succ_le_succ h),
      gsUniHasse_eq_zero_of_length_le s cs (k + 1)
        (Nat.le_succ_of_le (Nat.le_of_succ_le_succ h)),
      LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

section
variable {R : Type} [LawfulCommRing R] [DecidableEq R]

/-- A coefficient list all of whose Hasse derivatives vanish at one point is zero. -/
theorem coeffs_zero_of_hasse_zero (l : List R) (s : R) (h : ∀ k, gsUniHasse l k s = zero) :
    ∀ j, coeffAt l j = zero := by
  have hT : (taylorShift s).toFun (ofList l) = zero := ext_coeffAt fun k => by
    show coeffAt (eval₂ CHom (add (C s) X) (ofList l)).coeffs k = _
    rw [eval₂_ofList, coeffs_zero, coeffAt_nil]
    exact (coeffAt_shift_list s l k).trans (h k)
  have h2 := congrArg (taylorShift (neg s)).toFun hT
  rw [taylorShift_neg_cancel, RingHom.map_zero] at h2
  intro j
  rw [← coeffAt_ofList, h2, coeffs_zero, coeffAt_nil]

/-- `p(X) ↦ p(X + T) ∈ R[X][T]`. -/
def shift2 : RingHom (UPoly R) (UPoly (UPoly R)) := eval₂Hom (CHom.comp CHom) (add (C X) X)

/-- The `k`-th Hasse derivative is the coefficient of `T^k` in `p(X + T)`. -/
theorem hasse_eq_coeff (k : Nat) (p : UPoly R) :
    hasse k p = coeffAt ((shift2 (R := R)).toFun p).coeffs k := by
  have h := coeffAt_shift_list (X : UPoly R) (p.coeffs.map C) k
  rw [List.map_map] at h
  exact h.symm

theorem hasse_add (k : Nat) (p q : UPoly R) :
    hasse k (add p q) = add (hasse k p) (hasse k q) := by
  rw [hasse_eq_coeff, hasse_eq_coeff, hasse_eq_coeff, RingHom.map_add, coeffAt_add]

theorem hasse_one_zero : hasse 1 (zero : UPoly R) = zero := by
  rw [hasse_eq_coeff, RingHom.map_zero, coeffs_zero, coeffAt_nil]

theorem hasse_one_C (c : R) : hasse 1 (C c) = zero := by
  rw [hasse_eq_coeff]
  show coeffAt (eval₂ (CHom.comp CHom) (add (C X) X) (C c)).coeffs 1 = zero
  rw [eval₂_C]
  exact coeffAt_C_succ (C c) 0

theorem _root_.Qsag.Poly3.hasse_zero {R : Type} [LawfulCommRing R] [DecidableEq R] (p : UPoly R) :
    hasse 0 p = p := by
  show gsUniHasse (p.coeffs.map C) 0 X = p
  rw [gsUniHasse_zero_eq_evalCoeffs]
  exact evalCoeffs_C_X p

/-- The product rule against the variable. -/
theorem hasse_one_X_mul (p : UPoly R) : hasse 1 (mul X p) = add p (mul X (hasse 1 p)) := by
  have hX : (shift2 (R := R)).toFun X = add (C X) X := eval₂_X _ _
  have h0 : coeffAt ((shift2 (R := R)).toFun p).coeffs 0 = p :=
    (hasse_eq_coeff 0 p).symm.trans (Poly3.hasse_zero p)
  rw [hasse_eq_coeff, hasse_eq_coeff 1 p, RingHom.map_mul, hX, LawfulCommRing.right_distrib,
    coeffAt_add, coeffAt_C_mul, coeffAt_X_mul_succ, h0]
  exact LawfulCommRing.add_comm _ _

theorem hasse_one_hasse_list : ∀ (l : List R) (k : Nat),
    hasse 1 (gsUniHasse (l.map C) k (X : UPoly R)) =
      mul (CRing.natCast (k + 1)) (gsUniHasse (l.map C) (k + 1) X)
  | [], k => by
    show hasse 1 (zero : UPoly R) = mul _ zero
    rw [hasse_one_zero, LawfulCommRing.mul_zero]
  | c :: cs, 0 => by
    show hasse 1 (add (C c) (mul X (gsUniHasse (cs.map C) 0 X))) =
      mul one (add (gsUniHasse (cs.map C) 0 X) (mul X (gsUniHasse (cs.map C) 1 X)))
    rw [hasse_add, hasse_one_C, hasse_one_X_mul, hasse_one_hasse_list cs 0]
    show add zero (add _ (mul X (mul one _))) = _
    constructive_ring
  | c :: cs, k + 1 => by
    show hasse 1 (add (gsUniHasse (cs.map C) k X) (mul X (gsUniHasse (cs.map C) (k + 1) X))) =
      mul (CRing.natCast (k + 1 + 1)) (add (gsUniHasse (cs.map C) (k + 1) X)
        (mul X (gsUniHasse (cs.map C) (k + 1 + 1) X)))
    rw [hasse_add, hasse_one_X_mul, hasse_one_hasse_list cs k, hasse_one_hasse_list cs (k + 1),
      CRing.natCast_succ (k + 1)]
    generalize (CRing.natCast (k + 1) : UPoly R) = n
    constructive_ring

/-- **Composition of Hasse derivatives**: `∂^{(1)} ∂^{(k)} = (k + 1)·∂^{(k+1)}`. -/
theorem hasse_one_hasse (k : Nat) (p : UPoly R) :
    hasse 1 (hasse k p) = mul (CRing.natCast (k + 1)) (hasse (k + 1) p) :=
  hasse_one_hasse_list p.coeffs k

theorem natCast_ne_zero (n : Nat) (h : (CRing.natCast n : R) ≠ zero) :
    (CRing.natCast n : UPoly R) ≠ zero := fun e => h (by
  have h1 : (CRing.natCast n : UPoly R) = C (CRing.natCast n) :=
    ((CHom (R := R)).map_natCast n).symm
  have h2 := congrArg (fun p : UPoly R => coeffAt p.coeffs 0) (h1.symm.trans e)
  simp only [coeffAt_C_zero, coeffs_zero, coeffAt_nil] at h2
  exact h2)

end
end UPoly

/-! ## Excluded lines and multiplicities -/

end Qsag

section
namespace Qsag

set_option autoImplicit false

open CommRingOps RoundPoly

namespace Hensel
open UPoly

section Generic
variable {Λ : Type} [LawfulCommRing Λ] [DecidableEq Λ]

/-- The separant `[W⁰U¹] G`. -/
def sep (G : UPoly (UPoly Λ)) : Λ := coeffAt (coeffAt G.coeffs 1).coeffs 0

/-- The residue `[W⁰U⁰] G`. -/
def res (G : UPoly (UPoly Λ)) : Λ := coeffAt (coeffAt G.coeffs 0).coeffs 0

/-- `W ↦ S²·W`. -/
def evW (G : UPoly (UPoly Λ)) : RingHom (UPoly Λ) (UPoly Λ) :=
  eval₂Hom CHom (mul (C (mul (sep G) (sep G))) X)

/-- `W ↦ S²·W`, `U ↦ S·N`. -/
def evG (G : UPoly (UPoly Λ)) (N : UPoly Λ) : RingHom (UPoly (UPoly Λ)) (UPoly Λ) :=
  eval₂Hom (evW G) (mul (C (sep G)) N)

@[simp] theorem evW_apply (G : UPoly (UPoly Λ)) (q : UPoly Λ) :
    (evW G).toFun q = eval₂ CHom (mul (C (mul (sep G) (sep G))) X) q := by
  unfold evW; rw [eval₂Hom_apply]
@[simp] theorem evG_apply (G : UPoly (UPoly Λ)) (N : UPoly Λ) (p : UPoly (UPoly Λ)) :
    (evG G N).toFun p = eval₂ (evW G) (mul (C (sep G)) N) p := by
  unfold evG; rw [eval₂Hom_apply]

def e12 (G : UPoly (UPoly Λ)) : UPoly Λ := (evW G).toFun (shiftDown (coeffAt G.coeffs 1))
def e2 (G : UPoly (UPoly Λ)) : UPoly Λ := (evW G).toFun (shiftDown (coeffAt G.coeffs 0))
def e11 (G : UPoly (UPoly Λ)) (N : UPoly Λ) : UPoly Λ :=
  (evG G N).toFun (shiftDown (shiftDown G))

/-- `Φ(N) = -(S·N·W·G₁₂(S²W) + N²·G₁₁(S²W, S·N) + W·G₂(S²W))`. -/
def phi (G : UPoly (UPoly Λ)) (N : UPoly Λ) : UPoly Λ :=
  neg (add (add (mul (mul (mul (C (sep G)) N) X) (e12 G)) (mul (mul N N) (e11 G N)))
    (mul X (e2 G)))

/-- `G(S²W, S·N) = [W⁰U⁰]G + S²·(N - Φ(N))`, for every `N`. -/
theorem evG_eq (G : UPoly (UPoly Λ)) (N : UPoly Λ) :
    (evG G N).toFun G = add (C (res G)) (mul (C (mul (sep G) (sep G))) (sub N (phi G N))) := by
  have hC : ∀ q, (evG G N).toFun (C q) = (evW G).toFun q := fun q => by rw [evG_apply, eval₂_C]
  have hX : (evG G N).toFun X = mul (C (sep G)) N := by rw [evG_apply, eval₂_X]
  have hWC : ∀ a, (evW G).toFun (C a) = C a := fun a => by rw [evW_apply, eval₂_C, CHom_apply]
  have hWX : (evW G).toFun X = mul (C (mul (sep G) (sep G))) X := by rw [evW_apply, eval₂_X]
  have h1 : coeffAt (shiftDown G).coeffs 0 = coeffAt G.coeffs 1 := coeffAt_shiftDown G 0
  have hSS : C (mul (sep G) (sep G)) = mul (C (sep G)) (C (sep G)) := C_mul_eq _ _
  rw [hom_split (evG G N) G, hom_split (evG G N) (shiftDown G), hC, hC, hX, h1,
    hom_split (evW G) (coeffAt G.coeffs 0), hom_split (evW G) (coeffAt G.coeffs 1), hWC, hWC, hWX]
  show add (add (C (res G)) (mul _ (e2 G))) (mul _ (add (add (C (sep G)) (mul _ (e12 G)))
    (mul _ (e11 G N)))) = add (C (res G)) (mul _ (sub N (neg (add (add
      (mul (mul (mul (C (sep G)) N) X) (e12 G)) (mul (mul N N) (e11 G N))) (mul X (e2 G))))))
  rw [hSS]
  constructive_ring

/-- `Φ` preserves the ideal `(W)`. -/
theorem phi_mem (G : UPoly (UPoly Λ)) (N : UPoly Λ) (hN : InPow X 1 N) :
    InPow X 1 (phi G N) := by
  obtain ⟨a, rfl⟩ := InPow.of_one hN
  refine ⟨neg (add (add (mul (mul (mul (C (sep G)) a) X) (e12 G))
    (mul (mul a (mul X a)) (e11 G (mul X a)))) (e2 G)), ?_⟩
  show neg (add (add (mul (mul (mul (C (sep G)) (mul X a)) X) (e12 G))
    (mul (mul (mul X a) (mul X a)) (e11 G (mul X a)))) (mul X (e2 G))) = mul (mul one X) _
  constructive_ring

/-- **`Φ` is a contraction**: `N ≡ N' (mod W^k)` gives `Φ(N) ≡ Φ(N') (mod W^(k+1))` for
    `N, N'` without constant term. -/
theorem phi_contract (G : UPoly (UPoly Λ)) (N N' : UPoly Λ) (k : Nat) (hN : InPow X 1 N)
    (hN' : InPow X 1 N') (hd : InPow X k (sub N N')) :
    InPow X (k + 1) (sub (phi G N) (phi G N')) := by
  obtain ⟨a, ha⟩ := InPow.of_one hN
  obtain ⟨a', ha'⟩ := InPow.of_one hN'
  obtain ⟨t, ht⟩ := hd
  obtain ⟨hq, hfac⟩ : ∃ hq, e11 G N = add (mul (sub (mul (C (sep G)) N) (mul (C (sep G)) N')) hq)
      (e11 G N') := ⟨_, evalCoeffs_eq_mul_quotLinear_add
        ((shiftDown (shiftDown G)).coeffs.map (evW G).toFun) (mul (C (sep G)) N')
        (mul (C (sep G)) N)⟩
  refine ⟨neg (add (add (mul (mul (C (sep G)) (e12 G)) t) (mul (mul t (add a a')) (e11 G N')))
    (mul (mul (mul (mul X a) a) (mul (C (sep G)) t)) hq)), ?_⟩
  show sub (neg (add (add (mul (mul (mul (C (sep G)) N) X) (e12 G)) (mul (mul N N) (e11 G N)))
    (mul X (e2 G)))) (neg (add (add (mul (mul (mul (C (sep G)) N') X) (e12 G))
      (mul (mul N' N') (e11 G N'))) (mul X (e2 G)))) = mul (mul (CRing.npow X k) X) _
  rw [hfac]
  generalize CRing.npow (X : UPoly Λ) k = P at ht ⊢
  generalize e11 G N' = E
  refine Eq.trans (b := neg (add (add (mul (mul (mul (C (sep G)) X) (e12 G)) (sub N N'))
    (mul (mul (sub N N') (add N N')) E))
    (mul (mul (mul N N) (mul (C (sep G)) (sub N N'))) hq))) (by constructive_ring) ?_
  rw [ht, ha, ha']
  constructive_ring

/-- The iterates `Φ^k(0)`. -/
def iter (G : UPoly (UPoly Λ)) : Nat → UPoly Λ
  | 0 => zero
  | k + 1 => phi G (iter G k)

/-- **The cleared numerator `N_j`** of `[CWYZ26]` Lemma 3.11. -/
def num (G : UPoly (UPoly Λ)) (j : Nat) : Λ := coeffAt (iter G j).coeffs j

theorem iter_mem (G : UPoly (UPoly Λ)) : ∀ k, InPow X 1 (iter G k)
  | 0 => InPow.zero_mem X 1
  | k + 1 => phi_mem G _ (iter_mem G k)

/-- `W ↦ S²·W` preserves the `W`-adic filtration. -/
theorem evW_mem (G : UPoly (UPoly Λ)) (k : Nat) (p : UPoly Λ) (hp : InPow X k p) :
    InPow X k ((evW G).toFun p) := by
  have hpow : ∀ k : Nat, ∃ r, (evW G).toFun (CRing.npow X k) = mul (CRing.npow X k) r := by
    intro k
    induction k with
    | zero => exact ⟨one, by
        show (evW G).toFun one = mul one one
        rw [RingHom.map_one, LawfulCommRing.mul_one]⟩
    | succ k ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨mul r (C (mul (sep G) (sep G))), ?_⟩
      show (evW G).toFun (mul (CRing.npow X k) X) = mul (mul (CRing.npow X k) X) _
      rw [RingHom.map_mul, hr, show (evW G).toFun X = mul (C (mul (sep G) (sep G))) X from
        by rw [evW_apply, eval₂_X]]
      generalize CRing.npow (X : UPoly Λ) k = P
      constructive_ring
  obtain ⟨q, rfl⟩ := hp
  obtain ⟨r, hr⟩ := hpow k
  exact ⟨mul r ((evW G).toFun q), by rw [RingHom.map_mul, hr, LawfulCommRing.mul_assoc]⟩

end Generic

/-! ## Base change -/

section Map
variable {Λ Γ : Type} [LawfulCommRing Λ] [DecidableEq Λ] [LawfulCommRing Γ] [DecidableEq Γ]

theorem map_shiftDown (π : RingHom Λ Γ) (p : UPoly Λ) :
    (mapHom π).toFun (shiftDown p) = shiftDown ((mapHom π).toFun p) :=
  ext_coeffAt fun k => by
    rw [coeffAt_mapHom, coeffAt_shiftDown, coeffAt_shiftDown, coeffAt_mapHom]

theorem map_sep (π : RingHom Λ Γ) (G : UPoly (UPoly Λ)) :
    π.toFun (sep G) = sep ((mapHom (mapHom π)).toFun G) := by
  show _ = coeffAt (coeffAt ((mapHom (mapHom π)).toFun G).coeffs 1).coeffs 0
  rw [coeffAt_mapHom, coeffAt_mapHom]; rfl

theorem map_res (π : RingHom Λ Γ) (G : UPoly (UPoly Λ)) :
    π.toFun (res G) = res ((mapHom (mapHom π)).toFun G) := by
  show _ = coeffAt (coeffAt ((mapHom (mapHom π)).toFun G).coeffs 0).coeffs 0
  rw [coeffAt_mapHom, coeffAt_mapHom]; rfl

theorem map_evW (π : RingHom Λ Γ) (G : UPoly (UPoly Λ)) (q : UPoly Λ) :
    (mapHom π).toFun ((evW G).toFun q) =
      (evW ((mapHom (mapHom π)).toFun G)).toFun ((mapHom π).toFun q) := by
  simp only [evW_apply]
  show (mapHom π).toFun (eval₂ CHom (mul (C (mul (sep G) (sep G))) X) q) =
    eval₂ CHom (mul (C (mul (sep ((mapHom (mapHom π)).toFun G))
      (sep ((mapHom (mapHom π)).toFun G)))) X) ((mapHom π).toFun q)
  rw [hom_eval₂, eval₂_mapHom, RingHom.map_mul, mapHom_C, mapHom_X, π.map_mul, map_sep]
  exact eval₂_congr _ _ (fun c => mapHom_C π c) _ q

theorem map_evG (π : RingHom Λ Γ) (G : UPoly (UPoly Λ)) (N : UPoly Λ) (p : UPoly (UPoly Λ)) :
    (mapHom π).toFun ((evG G N).toFun p) =
      (evG ((mapHom (mapHom π)).toFun G) ((mapHom π).toFun N)).toFun
        ((mapHom (mapHom π)).toFun p) := by
  simp only [evG_apply]
  show (mapHom π).toFun (eval₂ (evW G) (mul (C (sep G)) N) p) =
    eval₂ (evW ((mapHom (mapHom π)).toFun G))
      (mul (C (sep ((mapHom (mapHom π)).toFun G))) ((mapHom π).toFun N))
      ((mapHom (mapHom π)).toFun p)
  rw [hom_eval₂, eval₂_mapHom, RingHom.map_mul, mapHom_C, map_sep]
  exact eval₂_congr _ _ (fun c => map_evW π G c) _ p

/-- `Φ` commutes with base change. -/
theorem map_phi (π : RingHom Λ Γ) (G : UPoly (UPoly Λ)) (N : UPoly Λ) :
    (mapHom π).toFun (phi G N) = phi ((mapHom (mapHom π)).toFun G) ((mapHom π).toFun N) := by
  have h12 : (mapHom π).toFun (e12 G) = e12 ((mapHom (mapHom π)).toFun G) := by
    show (mapHom π).toFun ((evW G).toFun (shiftDown (coeffAt G.coeffs 1))) =
      (evW _).toFun (shiftDown (coeffAt ((mapHom (mapHom π)).toFun G).coeffs 1))
    rw [map_evW, map_shiftDown, coeffAt_mapHom]
  have h2 : (mapHom π).toFun (e2 G) = e2 ((mapHom (mapHom π)).toFun G) := by
    show (mapHom π).toFun ((evW G).toFun (shiftDown (coeffAt G.coeffs 0))) =
      (evW _).toFun (shiftDown (coeffAt ((mapHom (mapHom π)).toFun G).coeffs 0))
    rw [map_evW, map_shiftDown, coeffAt_mapHom]
  have h11 : (mapHom π).toFun (e11 G N) =
      e11 ((mapHom (mapHom π)).toFun G) ((mapHom π).toFun N) := by
    show (mapHom π).toFun ((evG G N).toFun (shiftDown (shiftDown G))) =
      (evG _ _).toFun (shiftDown (shiftDown ((mapHom (mapHom π)).toFun G)))
    rw [map_evG, map_shiftDown, map_shiftDown]
  show (mapHom π).toFun (neg (add (add (mul (mul (mul (C (sep G)) N) X) (e12 G))
    (mul (mul N N) (e11 G N))) (mul X (e2 G)))) = neg (add (add (mul (mul (mul
      (C (sep ((mapHom (mapHom π)).toFun G))) ((mapHom π).toFun N)) X) (e12 _))
      (mul (mul ((mapHom π).toFun N) ((mapHom π).toFun N)) (e11 _ _))) (mul X (e2 _)))
  rw [RingHom.map_neg, RingHom.map_add, RingHom.map_add, RingHom.map_mul, RingHom.map_mul,
    RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, mapHom_C, mapHom_X,
    h12, h2, h11, map_sep]

theorem map_iter (π : RingHom Λ Γ) (G : UPoly (UPoly Λ)) : ∀ k,
    (mapHom π).toFun (iter G k) = iter ((mapHom (mapHom π)).toFun G) k
  | 0 => RingHom.map_zero _
  | k + 1 => by
    show (mapHom π).toFun (phi G (iter G k)) = phi _ (iter _ k)
    rw [map_phi, map_iter π G k]

/-- The numerators commute with base change. -/
theorem map_num (π : RingHom Λ Γ) (G : UPoly (UPoly Λ)) (j : Nat) :
    π.toFun (num G j) = num ((mapHom (mapHom π)).toFun G) j := by
  show π.toFun (coeffAt (iter G j).coeffs j) = coeffAt (iter _ j).coeffs j
  rw [← map_iter, coeffAt_mapHom]

end Map

/-! ## The numerators compute every root series -/

section Field
variable {K : Type} [LawfulField K] [DecidableEq K]

/-- **`[CWYZ26]` Lemma 3.11, numerators.** Let `G ∈ K[W][U]` with `G(0, 0) = 0` and separant
    `s = ∂_U G(0, 0) ≠ 0`. For every `e` with `e(0) = 0` and `G(W, e(W)) ≡ 0 (mod W^(n+1))`,
    the coefficients of `e` are `e_j = N_j / s^(2j-1)`, in the division-free form
    `s·N_j = (s²)^j·e_j`, for all `j ≤ n`. -/
theorem num_spec (G : UPoly (UPoly K)) (e : UPoly K) (n : Nat) (he0 : e.eval zero = zero)
    (hres : res G = zero) (hsep : sep G ≠ zero)
    (hsol : ∀ k, k ≤ n → coeffAt (G.eval e).coeffs k = zero) :
    ∀ j, j ≤ n → mul (sep G) (num G j) =
      mul (CRing.npow (mul (sep G) (sep G)) j) (coeffAt e.coeffs j) := by
  have he : coeffAt e.coeffs 0 = zero := by rw [← eval_zero_eq]; exact he0
  have hss : mul (sep G) (sep G) ≠ zero := fun h =>
    (LawfulField.mul_eq_zero h).elim hsep hsep
  have hunit : ∀ c : K, c ≠ zero → ∀ y : UPoly K, mul (C (LawfulField.inv c)) (mul (C c) y) = y := by
    intro c hc y
    rw [← LawfulCommRing.mul_assoc, ← CHom_apply, ← CHom_apply, ← CHom.map_mul,
      LawfulField.inv_mul_cancel hc, CHom.map_one, LawfulCommRing.one_mul]
  -- the scaled series `n' = s⁻¹·e(s²W)`
  have hsn : mul (C (sep G)) (mul (C (LawfulField.inv (sep G))) ((evW G).toFun e)) =
      (evW G).toFun e := by
    rw [← LawfulCommRing.mul_assoc, ← CHom_apply, ← CHom_apply, ← CHom.map_mul,
      LawfulField.mul_inv_cancel hsep, CHom.map_one, LawfulCommRing.one_mul]
  generalize hn' : mul (C (LawfulField.inv (sep G))) ((evW G).toFun e) = n' at hsn
  have hA : (evG G n').toFun G = (evW G).toFun (G.eval e) := by
    show eval₂ (evW G) (mul (C (sep G)) n') G = (evW G).toFun (eval₂ (RingHom.id _) e G)
    rw [hsn, hom_eval₂]
    exact eval₂_congr _ _ (fun _ => rfl) _ G
  have hB : InPow X (n + 1) (sub n' (phi G n')) := by
    have h1 := evW_mem G (n + 1) _ (inPow_of_coeff_zero (G.eval e) (n + 1)
      (fun k hk => hsol k (Nat.le_of_lt_succ hk)))
    rw [← hA, evG_eq, hres, ← CHom_apply (R := K) zero, CHom.map_zero,
      LawfulCommRing.zero_add] at h1
    have h2 := InPow.mul_mem (C (LawfulField.inv (mul (sep G) (sep G)))) h1
    rwa [hunit _ hss] at h2
  have hmem : InPow X 1 n' := by
    obtain ⟨a, ha⟩ := InPow.of_one (inPow_of_coeff_zero e 1 (fun j hj => by
      obtain rfl : j = 0 := by omega
      exact he))
    rw [← hn', ha, RingHom.map_mul, show (evW G).toFun X = mul (C (mul (sep G) (sep G))) X from
      eval₂_X _ _]
    exact ⟨mul (mul (C (LawfulField.inv (sep G))) (C (mul (sep G) (sep G))))
      ((evW G).toFun a), by
        show _ = mul (mul one X) _
        constructive_ring⟩
  have hE : ∀ k, k ≤ n → InPow X (k + 1) (sub n' (iter G k)) := by
    intro k
    induction k with
    | zero =>
      intro _
      show InPow X 1 (sub n' zero)
      rw [LawfulCommRing.sub_zero]; exact hmem
    | succ k ih =>
      intro hk
      have h1 := InPow.mono (show k + 2 ≤ n + 1 by omega) hB
      have h2 := phi_contract G n' (iter G k) (k + 1) hmem (iter_mem G k) (ih (by omega))
      have e : sub n' (phi G (iter G k)) =
          add (sub n' (phi G n')) (sub (phi G n') (phi G (iter G k))) := by constructive_ring
      show InPow X (k + 2) (sub n' (phi G (iter G k)))
      rw [e]; exact InPow.add_mem h1 h2
  intro j hj
  have h1 := coeff_zero_of_inPow (j + 1) _ (hE j hj) j (Nat.lt_succ_self j)
  rw [coeffAt_sub] at h1
  have h2 : coeffAt n'.coeffs j = num G j := LawfulCommRing.sub_eq_zero_iff.mp h1
  rw [← h2, ← hn', coeffAt_C_mul]
  have h3 : coeffAt ((evW G).toFun e).coeffs j =
      mul (CRing.npow (mul (sep G) (sep G)) j) (coeffAt e.coeffs j) := coeffAt_scale _ e.coeffs j
  rw [h3, ← LawfulCommRing.mul_assoc, LawfulField.mul_inv_cancel hsep, LawfulCommRing.one_mul]

end Field

/-! ## The degree bound -/

section Degree
variable {Λ : Type} [LawfulCommRing Λ] [DecidableEq Λ]

/-- Coefficientwise bound `δ(p_j) ≤ e·j + c`, with an integer offset `c`. -/
def Fil (δ : Λ → Nat) (e : Nat) (c : Int) (p : UPoly Λ) : Prop :=
  ∀ j, coeffAt p.coeffs j ≠ zero → (δ (coeffAt p.coeffs j) : Int) ≤ ((e * j : Nat) : Int) + c

variable {δ : Λ → Nat} {e : Nat}

private theorem int_bnd_add (hδ : DegFn δ) {B : Int} {x y : Λ}
    (hx : x ≠ zero → (δ x : Int) ≤ B) (hy : y ≠ zero → (δ y : Int) ≤ B)
    (h : add x y ≠ zero) : (δ (add x y) : Int) ≤ B := by
  if hx0 : x = zero then
    subst hx0; rw [LawfulCommRing.zero_add] at h ⊢; exact hy h
  else if hy0 : y = zero then
    subst hy0; rw [LawfulCommRing.add_zero] at h ⊢; exact hx h
  else
    have := hδ.add_le x y; have := hx hx0; have := hy hy0; omega

theorem Fil.zero_mem (c : Int) : Fil δ e c zero := fun j h => by
  rw [coeffs_zero, coeffAt_nil] at h; exact absurd rfl h

theorem Fil.mono {c c' : Int} {p : UPoly Λ} (h : c ≤ c') (hp : Fil δ e c p) : Fil δ e c' p :=
  fun j hj => by have := hp j hj; omega

theorem Fil.add_mem (hδ : DegFn δ) {c : Int} {p q : UPoly Λ} (hp : Fil δ e c p) (hq : Fil δ e c q) :
    Fil δ e c (add p q) := fun j hj => by
  rw [coeffAt_add] at hj ⊢
  exact int_bnd_add hδ (hp j) (hq j) hj

theorem Fil.neg_mem (hδ : DegFn δ) {c : Int} {p : UPoly Λ} (hp : Fil δ e c p) :
    Fil δ e c (neg p) := fun j hj => by
  rw [coeffAt_neg] at hj ⊢
  have hne : coeffAt p.coeffs j ≠ zero := fun h => hj (by rw [h, LawfulCommRing.neg_zero])
  have := hp j hne; have := hδ.neg_le (coeffAt p.coeffs j); omega

theorem Fil.mul_mem (hδ : DegFn δ) {c c' : Int} {p q : UPoly Λ} (hp : Fil δ e c p)
    (hq : Fil δ e c' q) : Fil δ e (c + c') (mul p q) := fun k => by
  have e1 : coeffAt (CommRingOps.mul p q).coeffs k = coeffAt (rawMul p.coeffs q.coeffs) k :=
    coeffAt_trimPoly _ k
  rw [e1]
  exact coeffAt_rawMul_graded
    (fun j y => y ≠ zero → (δ y : Int) ≤ ((e * j : Nat) : Int) + c') q.coeffs hq p.coeffs
    (fun k x => x ≠ zero → (δ x : Int) ≤ ((e * k : Nat) : Int) + (c + c'))
    (fun i x => x ≠ zero → (δ x : Int) ≤ ((e * i : Nat) : Int) + c) (fun _ h => absurd rfl h)
    (fun _ _ _ hx hy h => int_bnd_add hδ hx hy h)
    (fun i j x y hx hy h => by
      have hx0 : x ≠ zero := fun h0 => h (by rw [h0, LawfulCommRing.zero_mul])
      have hy0 : y ≠ zero := fun h0 => h (by rw [h0, LawfulCommRing.mul_zero])
      have := hx hx0; have := hy hy0; have := hδ.mul_le x y
      have := Nat.mul_add e i j
      omega)
    hp k

theorem Fil.const {c : Int} {a : Λ} (h : a ≠ zero → (δ a : Int) ≤ c) : Fil δ e c (C a) :=
  fun j hj => by
    cases j with
    | zero =>
      rw [coeffAt_C_zero] at hj ⊢
      have := h hj
      rw [Nat.mul_zero]; omega
    | succ j => exact absurd (coeffAt_C_succ a j) hj

theorem Fil.var (h1 : δ one = 0) : Fil δ e (-(e : Int)) X := fun j hj => by
  have e1 : coeffAt (X : UPoly Λ).coeffs j = coeffAt [zero, one] j := coeffAt_ofList _ j
  rw [e1] at hj ⊢
  cases j with
  | zero => exact absurd rfl hj
  | succ j =>
    cases j with
    | zero => show (δ one : Int) ≤ ((e * 1 : Nat) : Int) + -(e : Int); rw [h1, Nat.mul_one]; omega
    | succ j => exact absurd rfl hj

/-- Horner evaluation at a point of offset `0`. -/
theorem Fil.eval0 (hδ : DegFn δ) {c : Int} {u : UPoly Λ} (hu : Fil δ e 0 u) :
    ∀ l : List (UPoly Λ), (∀ b, Fil δ e c (coeffAt l b)) → Fil δ e c (evalCoeffs l u)
  | [], _ => Fil.zero_mem c
  | x :: xs, h => by
    have ih := Fil.eval0 hδ hu xs (fun b => by
      have := h (b + 1)
      rwa [coeffAt_cons_succ] at this)
    exact Fil.add_mem hδ (h 0) (Fil.mono (by omega) (Fil.mul_mem hδ hu ih))

/-- Horner evaluation at a point of offset `1`: the coefficient of `U^b` may be `b` lower. -/
theorem Fil.eval1 (hδ : DegFn δ) {u : UPoly Λ} (hu : Fil δ e 1 u) :
    ∀ (l : List (UPoly Λ)) (c : Int), (∀ b : Nat, Fil δ e (c - b) (coeffAt l b)) →
      Fil δ e c (evalCoeffs l u)
  | [], c, _ => Fil.zero_mem c
  | x :: xs, c, h => by
    have ih := Fil.eval1 hδ hu xs (c - 1) (fun b => by
      have := h (b + 1)
      rw [coeffAt_cons_succ] at this
      exact Fil.mono (by omega) this)
    have h0 := h 0
    rw [coeffAt_cons_zero] at h0
    exact Fil.add_mem hδ (Fil.mono (by omega) h0) (Fil.mono (by omega) (Fil.mul_mem hδ hu ih))

/-- **Degree bound for the iterates.** If `δ([W^a U^b]G) + b ≤ h' + 1`, every iterate has
    `δ([W^j] iter G k) ≤ 2h'·j + 1 - h'`. -/
theorem fil_iter (hδ : DegFn δ) (h1 : δ one = 0) (h' : Nat) (G : UPoly (UPoly Λ))
    (hG : ∀ a b, coeffAt (coeffAt G.coeffs b).coeffs a ≠ zero →
      δ (coeffAt (coeffAt G.coeffs b).coeffs a) + b ≤ h' + 1) :
    ∀ k, Fil δ (2 * h') (1 - (h' : Int)) (iter G k) := by
  have hS : Fil δ (2 * h') (h' : Int) (C (sep G)) := Fil.const (fun hne => by
    have := hG 0 1 hne
    show (δ (coeffAt (coeffAt G.coeffs 1).coeffs 0) : Int) ≤ h'
    omega)
  have hX : Fil δ (2 * h') (-((2 * h' : Nat) : Int)) X := Fil.var h1
  have hs2 : Fil δ (2 * h') 0 (mul (C (mul (sep G) (sep G))) X) := by
    rw [show C (mul (sep G) (sep G)) = mul (C (sep G)) (C (sep G)) from CHom.map_mul _ _]
    exact Fil.mono (by omega) (Fil.mul_mem hδ (Fil.mul_mem hδ hS hS) hX)
  have hW : ∀ (q : UPoly Λ) (c : Int),
      (∀ a, coeffAt q.coeffs a ≠ zero → (δ (coeffAt q.coeffs a) : Int) ≤ c) →
      Fil δ (2 * h') c ((evW G).toFun q) := by
    intro q c hq
    show Fil δ (2 * h') c (evalCoeffs (q.coeffs.map (CHom (R := Λ)).toFun) _)
    refine Fil.eval0 hδ hs2 _ (fun b => ?_)
    rw [RingHom.coeffAt_map]
    exact Fil.const (hq b)
  have he2 : Fil δ (2 * h') ((h' : Int) + 1) (e2 G) := hW _ _ (fun a hne => by
    rw [coeffAt_shiftDown] at hne ⊢
    have := hG (a + 1) 0 hne
    omega)
  have he12 : Fil δ (2 * h') (h' : Int) (e12 G) := hW _ _ (fun a hne => by
    rw [coeffAt_shiftDown] at hne ⊢
    have := hG (a + 1) 1 hne
    omega)
  have he11 : ∀ N, Fil δ (2 * h') (1 - (h' : Int)) N →
      Fil δ (2 * h') ((h' : Int) - 1) (e11 G N) := by
    intro N hN
    show Fil δ (2 * h') _ (evalCoeffs ((shiftDown (shiftDown G)).coeffs.map (evW G).toFun)
      (mul (C (sep G)) N))
    refine Fil.eval1 hδ (Fil.mono (by omega) (Fil.mul_mem hδ hS hN)) _ _ (fun b => ?_)
    rw [RingHom.coeffAt_map, coeffAt_shiftDown, coeffAt_shiftDown]
    exact hW _ _ (fun a hne => by
      have := hG a (b + 1 + 1) hne
      omega)
  have hstep : ∀ N, Fil δ (2 * h') (1 - (h' : Int)) N →
      Fil δ (2 * h') (1 - (h' : Int)) (phi G N) := fun N hN =>
    Fil.neg_mem hδ (Fil.add_mem hδ (Fil.add_mem hδ
      (Fil.mono (by omega) (Fil.mul_mem hδ (Fil.mul_mem hδ (Fil.mul_mem hδ hS hN) hX) he12))
      (Fil.mono (by omega) (Fil.mul_mem hδ (Fil.mul_mem hδ hN hN) (he11 N hN))))
      (Fil.mono (by omega) (Fil.mul_mem hδ hX he2)))
  intro k
  induction k with
  | zero => exact Fil.zero_mem _
  | succ k ih => exact hstep _ ih

theorem two_mul_pred (j h' : Nat) (hj : 1 ≤ j) : 2 * h' * j = (2 * j - 1) * h' + h' := by
  have e : 2 * j = (2 * j - 1) + 1 := by omega
  calc 2 * h' * j = 2 * j * h' := Nat.mul_right_comm 2 h' j
    _ = ((2 * j - 1) + 1) * h' := by rw [← e]
    _ = _ := by rw [Nat.add_mul, Nat.one_mul]

/-- **`[CWYZ26]` Lemma 3.11, degree bound**: `δ(N_j) ≤ 1 + (2j - 1)·h'` for `j ≥ 1`, where
    `h' + 1` bounds the weighted degree of `G`. -/
theorem delta_num_le (hδ : DegFn δ) (h1 : δ one = 0) (h' : Nat) (G : UPoly (UPoly Λ))
    (hG : ∀ a b, coeffAt (coeffAt G.coeffs b).coeffs a ≠ zero →
      δ (coeffAt (coeffAt G.coeffs b).coeffs a) + b ≤ h' + 1) (j : Nat) (hj : 1 ≤ j) :
    δ (num G j) ≤ 1 + (2 * j - 1) * h' := by
  have he := two_mul_pred j h' hj
  if hz : num G j = zero then
    rw [hz, hδ.zero]; exact Nat.zero_le _
  else
    have := fil_iter hδ h1 h' G hG j j hz
    show δ (coeffAt (iter G j).coeffs j) ≤ _
    omega

end Degree

end Hensel

/-! ## Witnesses -/

end Qsag

end

section
namespace Qsag

set_option autoImplicit false

open CommRingOps RoundPoly

namespace Poly3
variable {F : Type} [LawfulField F] [DecidableEq F]
open UPoly

/-- **Jet injectivity** (`[CWYZ26]` Claim 4.9, uniqueness of the reconstruction). Two roots
    `P, P'` of `R` on the line `Y = α + βX` that agree at `t₀`, where the separant
    `∂_Z R(t₀, α + βt₀, P(t₀))` is nonzero, are equal. -/
theorem root_unique_of_jet (R : Poly3 F) (α β t₀ : F) (P P' : UPoly F)
    (hP : evalAffineLine R α β P = zero) (hP' : evalAffineLine R α β P' = zero)
    (hjet : P.eval t₀ = P'.eval t₀)
    (hsep : ((hasseZ 1 R).evalAffineLine α β (C (P.eval t₀))).eval t₀ ≠ zero) : P = P' := by
  have hr : ∀ Q : UPoly F, evalAffineLine R α β Q = zero →
      eval₂ ((taylorShift t₀).comp (evalHom (line α β))) ((taylorShift t₀).toFun Q) R = zero := by
    intro Q hQ
    rw [← hom_eval₂]
    show (taylorShift t₀).toFun (evalAffineLine R α β Q) = zero
    rw [hQ, RingHom.map_zero]
  have he : ∀ Q : UPoly F, ((taylorShift t₀).toFun Q).eval zero = Q.eval t₀ := fun Q => by
    rw [eval_taylorShift, LawfulCommRing.add_zero]
  have hS : eval₂ ((evalHom (zero : F)).comp ((taylorShift t₀).comp (evalHom (line α β))))
      (P.eval t₀) (hasse 1 R) ≠ zero := by
    intro e
    apply hsep
    show (evalHom t₀).toFun (eval₂ (evalHom (line α β)) (C (P.eval t₀)) (hasse 1 R)) = zero
    rw [hom_eval₂, evalHom_apply, eval_C, ← e]
    show evalCoeffs ((hasse 1 R).coeffs.map _) _ = evalCoeffs ((hasse 1 R).coeffs.map _) _
    congr 1
    apply List.map_congr_left
    intro q _
    exact (he (q.eval (line α β))).symm
  have key := hensel_unique R ((taylorShift t₀).comp (evalHom (line α β)))
    ((taylorShift t₀).toFun P) ((taylorShift t₀).toFun P') (P.eval t₀) (he P)
    ((he P').trans hjet.symm) hS
  have heq : (taylorShift t₀).toFun P = (taylorShift t₀).toFun P' := ext_coeffAt fun k =>
    key (k + 1) (fun j _ => by rw [hr P hP, coeffs_zero, coeffAt_nil])
      (fun j _ => by rw [hr P' hP', coeffs_zero, coeffAt_nil]) k (Nat.lt_succ_self k)
  have := congrArg (taylorShift (neg t₀)).toFun heq
  rwa [taylorShift_neg_cancel, taylorShift_neg_cancel] at this

end Poly3

/-! ## The numerators of `R(t₀ + W, Y + V·W, Z + U)` -/

namespace Poly3
variable {K : Type} [LawfulField K] [DecidableEq K]
open UPoly

/-- A scalar as a constant of `K[X][Y][Z]`. -/
def C3 (x : K) : Poly3 K := C (C (C x))

/-- The embedding of scalars. -/
def c3Hom : RingHom K (Poly3 K) := CHom.comp (CHom.comp CHom)

theorem degFn_degYZ : DegFn (degYZ (F := K)) := degFn_wdeg degFn_natDeg 1

theorem degFn_deg11d (d : Nat) : DegFn (deg11d (F := K) d) :=
  degFn_wdeg (degFn_wdeg degFn_natDeg 1) d

theorem degYZ_C3 (x : K) : degYZ (C3 x) = 0 :=
  Nat.le_zero.mp (Nat.le_trans (wdeg_C_le _ _ _) (Nat.le_of_eq (natDeg_C_eq _)))

theorem deg11d_C3 (d : Nat) (x : K) : deg11d d (C3 x) = 0 :=
  Nat.le_zero.mp (Nat.le_trans (wdeg_C_le _ _ _)
    (Nat.le_trans (wdeg_C_le _ _ _) (Nat.le_of_eq (natDeg_C_eq _))))

theorem deg11d_one (d : Nat) : deg11d d (one : Poly3 K) = 0 := deg11d_C3 d one

/-- Evaluation at a point: innermost variable `x`, then `y`, then `z`. -/
def ptHom (x y z : K) : RingHom (Poly3 K) K := eval₂Hom (eval₂Hom (evalHom x) y) z

/-- `Q(x, y, z)`. -/
def eval3 (Q : Poly3 K) (x y z : K) : K := (ptHom x y z).toFun Q

/-- The jet ring is `K[Y][V][Z]`; these are its variables `Y` and `V` (and `Z = X`). -/
def jetY : Poly3 K := C (C X)
def jetV : Poly3 K := C X

/-- `X ↦ t₀ + W`, into `K[Y][V][Z][W]`. -/
def liftX (t₀ : K) : RingHom (UPoly K) (UPoly (Poly3 K)) :=
  eval₂Hom (CHom.comp c3Hom) (add (C (C3 t₀)) X)

/-- `X ↦ t₀ + W`, `Y ↦ Y + V·W`. -/
def liftXY (t₀ : K) : RingHom (UPoly (UPoly K)) (UPoly (Poly3 K)) :=
  eval₂Hom (liftX t₀) (add (C jetY) (mul (C jetV) X))

/-- `G(W, U) = R(t₀ + W, Y + V·W, Z + U) ∈ K[Y][V][Z][W][U]`. -/
def henselG (R : Poly3 K) (t₀ : K) : UPoly (UPoly (Poly3 K)) :=
  eval₂ (CHom.comp (liftXY t₀)) (add (C (C X)) X) R

/-- **The cleared numerator `N_j(Y, V, Z)`** of `[CWYZ26]` Lemma 3.11. -/
def henselNum (R : Poly3 K) (t₀ : K) (j : Nat) : Poly3 K := Hensel.num (henselG R t₀) j

/-- The separant `S(Y, V, Z) = ∂_Z R(t₀, Y, Z)`. -/
def henselSep (R : Poly3 K) (t₀ : K) : Poly3 K := Hensel.sep (henselG R t₀)

theorem natDeg_X_le : (X : UPoly K).natDeg ≤ 1 := by
  have := trimPoly_length_le [(zero : K), one]
  show (trimPoly [(zero : K), one]).length - 1 ≤ 1
  simp only [List.length_cons, List.length_nil] at this; omega

theorem deg11d_X_le : deg11d 1 (X : Poly3 K) ≤ 1 := by
  have h := wdeg_X_le (R := UPoly (UPoly K)) (fun q => q.wdeg natDeg 1) 1
  have h1 : (one : UPoly (UPoly K)).wdeg natDeg 1 = 0 :=
    Nat.le_zero.mp (Nat.le_trans (wdeg_C_le natDeg 1 (one : UPoly K)) (Nat.le_of_eq natDeg_one))
  show (X : Poly3 K).wdeg (fun q => q.wdeg natDeg 1) 1 ≤ 1
  have h' : (X : Poly3 K).wdeg (fun q => q.wdeg natDeg 1) 1 ≤
      (one : UPoly (UPoly K)).wdeg natDeg 1 + 1 := h
  omega

theorem deg11d_jetY_le : deg11d 1 (jetY (K := K)) ≤ 1 :=
  Nat.le_trans (wdeg_C_le _ _ _) (Nat.le_trans (wdeg_C_le _ _ _) natDeg_X_le)

theorem deg11d_jetV_le : deg11d 1 (jetV (K := K)) ≤ 1 := by
  have h := wdeg_X_le (R := UPoly K) natDeg 1
  rw [natDeg_one] at h
  exact Nat.le_trans (wdeg_C_le _ _ _) h

/-- Coefficient bound for `G`: `deg_{Y,V,Z} [W^a U^b] G + b ≤ deg_{Y,Z} R`. -/
theorem henselG_coeff_le (R : Poly3 K) (t₀ : K) (a b : Nat)
    (hne : coeffAt (coeffAt (henselG R t₀).coeffs b).coeffs a ≠ zero) :
    deg11d 1 (coeffAt (coeffAt (henselG R t₀).coeffs b).coeffs a) + b ≤ R.degYZ := by
  have hδ := degFn_deg11d (K := K) 1
  have hw1 : DegFn (fun q : UPoly (Poly3 K) => q.wdeg (deg11d 1) 0) := degFn_wdeg hδ 0
  have hΩ : DegFn (fun G : UPoly (UPoly (Poly3 K)) => G.wdeg (fun q => q.wdeg (deg11d 1) 0) 1) :=
    degFn_wdeg hw1 1
  have hXw : (X : UPoly (Poly3 K)).wdeg (deg11d 1) 0 ≤ 0 := by
    have := wdeg_X_le (R := Poly3 K) (deg11d 1) 0
    rw [deg11d_one] at this; exact this
  have hx : ∀ x : UPoly K, ((liftX t₀).toFun x).wdeg (deg11d 1) 0 ≤ 0 := by
    intro x
    have hs : (add (C (C3 t₀)) (X : UPoly (Poly3 K))).wdeg (deg11d 1) 0 ≤ 0 := by
      have h1 := hw1.add_le (C (C3 t₀)) X
      have h2 : (C (C3 t₀) : UPoly (Poly3 K)).wdeg (deg11d 1) 0 ≤ deg11d 1 (C3 t₀) :=
        wdeg_C_le _ _ _
      rw [deg11d_C3] at h2
      have h1' : (add (C (C3 t₀)) (X : UPoly (Poly3 K))).wdeg (deg11d 1) 0 ≤
        max ((C (C3 t₀) : UPoly (Poly3 K)).wdeg (deg11d 1) 0)
          ((X : UPoly (Poly3 K)).wdeg (deg11d 1) 0) := h1
      omega
    have h := degFn_eval₂_le hw1 (CHom.comp c3Hom) (fun _ => 0) (fun a => by
      have h2 : (C (C3 a) : UPoly (Poly3 K)).wdeg (deg11d 1) 0 ≤ deg11d 1 (C3 a) :=
        wdeg_C_le _ _ _
      rw [deg11d_C3] at h2; exact h2) (add (C (C3 t₀)) X) 0 hs x
    have h0 : x.wdeg (fun _ => 0) 0 ≤ 0 := wdeg_le _ _ _ 0 (fun k _ => by
      show 0 + 0 * k ≤ 0; omega)
    exact Nat.le_trans h h0
  have hy : ∀ c : UPoly (UPoly K), ((liftXY t₀).toFun c).wdeg (deg11d 1) 0 ≤ c.natDeg := by
    intro c
    have hs : (add (C jetY) (mul (C jetV) (X : UPoly (Poly3 K)))).wdeg (deg11d 1) 0 ≤ 1 := by
      have h1 := hw1.add_le (C (jetY (K := K))) (mul (C jetV) X)
      have h2 := hw1.mul_le (C (jetV (K := K))) X
      have h3 : (C jetY : UPoly (Poly3 K)).wdeg (deg11d 1) 0 ≤ deg11d 1 (jetY (K := K)) :=
        wdeg_C_le _ _ _
      have h4 : (C jetV : UPoly (Poly3 K)).wdeg (deg11d 1) 0 ≤ deg11d 1 (jetV (K := K)) :=
        wdeg_C_le _ _ _
      have h5 := deg11d_jetY_le (K := K)
      have h6 := deg11d_jetV_le (K := K)
      have h1' : (add (C jetY) (mul (C jetV) (X : UPoly (Poly3 K)))).wdeg (deg11d 1) 0 ≤
        max ((C jetY : UPoly (Poly3 K)).wdeg (deg11d 1) 0)
          ((mul (C jetV) (X : UPoly (Poly3 K))).wdeg (deg11d 1) 0) := h1
      have h2' : (mul (C jetV) (X : UPoly (Poly3 K))).wdeg (deg11d 1) 0 ≤
        (C jetV : UPoly (Poly3 K)).wdeg (deg11d 1) 0 + (X : UPoly (Poly3 K)).wdeg (deg11d 1) 0 :=
        h2
      omega
    have h := degFn_eval₂_le hw1 (liftX t₀) (fun _ => 0) hx _ 1 hs c
    have h0 : c.wdeg (fun _ => 0) 1 ≤ c.natDeg := wdeg_le _ _ _ _ (fun k hk => by
      have : k ≤ c.natDeg := Nat.le_of_not_lt (fun hlt => hk (c.coeffAt_eq_zero_of_natDeg_lt hlt))
      show 0 + 1 * k ≤ c.natDeg; omega)
    exact Nat.le_trans h h0
  have hG : (henselG R t₀).wdeg (fun q => q.wdeg (deg11d 1) 0) 1 ≤ R.wdeg natDeg 1 := by
    have hs : (add (C (C (X : Poly3 K))) (X : UPoly (UPoly (Poly3 K)))).wdeg
        (fun q => q.wdeg (deg11d 1) 0) 1 ≤ 1 := by
      have h1 := hΩ.add_le (C (C (X : Poly3 K))) X
      have h2 : (C (C (X : Poly3 K)) : UPoly (UPoly (Poly3 K))).wdeg
          (fun q => q.wdeg (deg11d 1) 0) 1 ≤ (C (X : Poly3 K) : UPoly (Poly3 K)).wdeg (deg11d 1) 0 :=
        wdeg_C_le _ _ _
      have h3 : (C (X : Poly3 K) : UPoly (Poly3 K)).wdeg (deg11d 1) 0 ≤ deg11d 1 (X : Poly3 K) :=
        wdeg_C_le _ _ _
      have h4 := deg11d_X_le (K := K)
      have h5 := wdeg_X_le (R := UPoly (Poly3 K)) (fun q => q.wdeg (deg11d 1) 0) 1
      have h6 : (one : UPoly (Poly3 K)).wdeg (deg11d 1) 0 ≤ deg11d 1 (one : Poly3 K) :=
        wdeg_C_le _ _ _
      rw [deg11d_one] at h6
      have h5' : (X : UPoly (UPoly (Poly3 K))).wdeg (fun q => q.wdeg (deg11d 1) 0) 1 ≤
        (one : UPoly (Poly3 K)).wdeg (deg11d 1) 0 + 1 := h5
      have h1' : (add (C (C (X : Poly3 K))) (X : UPoly (UPoly (Poly3 K)))).wdeg
          (fun q => q.wdeg (deg11d 1) 0) 1 ≤
        max ((C (C (X : Poly3 K)) : UPoly (UPoly (Poly3 K))).wdeg (fun q => q.wdeg (deg11d 1) 0) 1)
          ((X : UPoly (UPoly (Poly3 K))).wdeg (fun q => q.wdeg (deg11d 1) 0) 1) := h1
      omega
    exact degFn_eval₂_le hΩ (CHom.comp (liftXY t₀)) natDeg (fun c =>
      Nat.le_trans (wdeg_C_le _ _ _) (hy c)) _ 1 hs R
  have hq : coeffAt (henselG R t₀).coeffs b ≠ zero := fun e => hne (by
    rw [e, coeffs_zero, coeffAt_nil])
  have h1 := le_wdeg (fun q : UPoly (Poly3 K) => q.wdeg (deg11d 1) 0) 1 (henselG R t₀) b hq
  have h2 := le_wdeg (deg11d (F := K) 1) 0 (coeffAt (henselG R t₀).coeffs b) a hne
  have h1' : (coeffAt (henselG R t₀).coeffs b).wdeg (deg11d 1) 0 + 1 * b ≤
    (henselG R t₀).wdeg (fun q => q.wdeg (deg11d 1) 0) 1 := h1
  have hG' : (henselG R t₀).wdeg (fun q => q.wdeg (deg11d 1) 0) 1 ≤ R.degYZ := hG
  omega

/-- **`[CWYZ26]` Lemma 3.11, degree bound**: `deg_{Y,V,Z} N_j ≤ 1 + (2j - 1)(h - 1)` for
    `j ≥ 1`, where `h ≥ deg_{Y,Z} R`. -/
theorem deg_henselNum_le (R : Poly3 K) (t₀ : K) (h j : Nat) (hR : R.degYZ ≤ h) (hh : 1 ≤ h)
    (hj : 1 ≤ j) : deg11d 1 (henselNum R t₀ j) ≤ 1 + (2 * j - 1) * (h - 1) :=
  Hensel.delta_num_le (degFn_deg11d 1) (deg11d_one 1) (h - 1) _ (fun a b hne => by
    have := henselG_coeff_le R t₀ a b hne; omega) j hj

theorem deg_henselSep_le (R : Poly3 K) (t₀ : K) (h : Nat) (hR : R.degYZ ≤ h) :
    deg11d 1 (henselSep R t₀) ≤ h - 1 := by
  if hz : henselSep R t₀ = zero then
    rw [hz, (degFn_deg11d (K := K) 1).zero]; exact Nat.zero_le _
  else
    have := henselG_coeff_le R t₀ 0 1 hz
    show deg11d 1 (coeffAt (coeffAt (henselG R t₀).coeffs 1).coeffs 0) ≤ h - 1
    omega

/-! ### Specialization at a point of `K³` -/

/-- `X ↦ t₀ + W`, `Y ↦ y + v·W`, into `K[W]`. -/
def jetHom (t₀ y v : K) : RingHom (UPoly (UPoly K)) (UPoly K) :=
  eval₂Hom (taylorShift t₀) (add (C y) (mul (C v) X))

theorem ptHom_C3 (y v z a : K) : (ptHom y v z).toFun (C3 a) = a := by
  show eval₂ (eval₂Hom (evalHom y) v) z (C (C (C a))) = a
  rw [eval₂_C]
  show eval₂ (evalHom y) v (C (C a)) = a
  rw [eval₂_C]; exact eval_C a y

theorem ptHom_jetY (y v z : K) : (ptHom y v z).toFun jetY = y := by
  show eval₂ (eval₂Hom (evalHom y) v) z (C (C X)) = y
  rw [eval₂_C]
  show eval₂ (evalHom y) v (C X) = y
  rw [eval₂_C]; exact eval_X y

theorem ptHom_jetV (y v z : K) : (ptHom y v z).toFun jetV = v := by
  show eval₂ (eval₂Hom (evalHom y) v) z (C X) = v
  rw [eval₂_C]; exact eval₂_X _ _

theorem ptHom_X (y v z : K) : (ptHom y v z).toFun X = z := eval₂_X _ _

theorem map_liftX (t₀ y v z : K) (x : UPoly K) :
    (mapHom (ptHom y v z)).toFun ((liftX t₀).toFun x) = (taylorShift t₀).toFun x := by
  refine hom_ext ((mapHom (ptHom y v z)).comp (liftX t₀)) (taylorShift t₀) (fun a => ?_) ?_ x
  · show (mapHom (ptHom y v z)).toFun (eval₂ (CHom.comp c3Hom) (add (C (C3 t₀)) X) (C a)) =
      (taylorShift t₀).toFun (C a)
    rw [eval₂_C, taylorShift_C]
    show (mapHom (ptHom y v z)).toFun (C (C3 a)) = C a
    rw [mapHom_C, ptHom_C3]
  · show (mapHom (ptHom y v z)).toFun (eval₂ (CHom.comp c3Hom) (add (C (C3 t₀)) X) X) =
      (taylorShift t₀).toFun X
    rw [eval₂_X, taylorShift_X, RingHom.map_add, mapHom_C, mapHom_X, ptHom_C3]

theorem map_liftXY (t₀ y v z : K) (c : UPoly (UPoly K)) :
    (mapHom (ptHom y v z)).toFun ((liftXY t₀).toFun c) = (jetHom t₀ y v).toFun c := by
  refine hom_ext ((mapHom (ptHom y v z)).comp (liftXY t₀)) (jetHom t₀ y v) (fun a => ?_) ?_ c
  · show (mapHom (ptHom y v z)).toFun (eval₂ (liftX t₀) (add (C jetY) (mul (C jetV) X)) (C a)) =
      eval₂ (taylorShift t₀) (add (C y) (mul (C v) X)) (C a)
    rw [eval₂_C, eval₂_C]; exact map_liftX t₀ y v z a
  · show (mapHom (ptHom y v z)).toFun (eval₂ (liftX t₀) (add (C jetY) (mul (C jetV) X)) X) =
      eval₂ (taylorShift t₀) (add (C y) (mul (C v) X)) X
    rw [eval₂_X, eval₂_X, RingHom.map_add, RingHom.map_mul, mapHom_C, mapHom_C, mapHom_X,
      ptHom_jetY, ptHom_jetV]

/-- The specialization of `G` at `(y, v, z)` is `R(t₀ + W, y + v·W, z + U)`. -/
theorem map_henselG (R : Poly3 K) (t₀ y v z : K) :
    (mapHom (mapHom (ptHom y v z))).toFun (henselG R t₀) =
      eval₂ (CHom.comp (jetHom t₀ y v)) (add (C (C z)) X) R := by
  show (mapHom (mapHom (ptHom y v z))).toFun
    (eval₂ (CHom.comp (liftXY t₀)) (add (C (C X)) X) R) = _
  rw [hom_eval₂, RingHom.map_add, mapHom_C, mapHom_C, mapHom_X, ptHom_X]
  exact eval₂_congr _ _ (fun c => by
    show (mapHom (mapHom (ptHom y v z))).toFun (C ((liftXY t₀).toFun c)) =
      C ((jetHom t₀ y v).toFun c)
    rw [mapHom_C, map_liftXY]) _ R

/-- The `U^k` coefficient of the specialized `G` is the `k`-th Hasse derivative of `R`. -/
theorem coeffAt_jet (R : Poly3 K) (t₀ y v z : K) (k : Nat) :
    coeffAt (eval₂ (CHom.comp (jetHom t₀ y v)) (add (C (C z)) X) R).coeffs k =
      eval₂ (jetHom t₀ y v) (C z) (hasseZ k R) := by
  show _ = eval₂ (jetHom t₀ y v) (C z) (hasse k R)
  rw [eval₂_hasse]
  have := coeffAt_shift_list (C z) (R.coeffs.map (jetHom t₀ y v).toFun) k
  rw [List.map_map] at this
  exact this

theorem eval_zero_jet (t₀ y v z : K) (Q : Poly3 K) :
    (eval₂ (jetHom t₀ y v) (C z) Q).eval zero = eval3 Q t₀ y z := by
  show (evalHom zero).toFun (eval₂ (jetHom t₀ y v) (C z) Q) = eval₂ (eval₂Hom (evalHom t₀) y) z Q
  rw [hom_eval₂, evalHom_apply, eval_C]
  refine eval₂_congr _ _ (fun c => ?_) _ Q
  refine hom_ext ((evalHom zero).comp (jetHom t₀ y v)) (eval₂Hom (evalHom t₀) y) (fun a => ?_) ?_ c
  · show (eval₂ (taylorShift t₀) (add (C y) (mul (C v) X)) (C a)).eval zero =
      eval₂ (evalHom t₀) y (C a)
    rw [eval₂_C, eval₂_C, eval_taylorShift, LawfulCommRing.add_zero]; rfl
  · show (eval₂ (taylorShift t₀) (add (C y) (mul (C v) X)) X).eval zero = eval₂ (evalHom t₀) y X
    rw [eval₂_X, eval₂_X]
    show (evalHom zero).toFun (add (C y) (mul (C v) X)) = y
    rw [RingHom.map_add, RingHom.map_mul, evalHom_apply, evalHom_apply, evalHom_apply, eval_C,
      eval_C, eval_X, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

theorem sep_map_henselG (R : Poly3 K) (t₀ y v z : K) :
    Hensel.sep ((mapHom (mapHom (ptHom y v z))).toFun (henselG R t₀)) =
      eval3 (hasseZ 1 R) t₀ y z := by
  show coeffAt (coeffAt ((mapHom (mapHom (ptHom y v z))).toFun (henselG R t₀)).coeffs 1).coeffs 0
    = _
  rw [map_henselG, coeffAt_jet, ← eval_zero_eq, eval_zero_jet]

theorem res_map_henselG (R : Poly3 K) (t₀ y v z : K) :
    Hensel.res ((mapHom (mapHom (ptHom y v z))).toFun (henselG R t₀)) = eval3 R t₀ y z := by
  show coeffAt (coeffAt ((mapHom (mapHom (ptHom y v z))).toFun (henselG R t₀)).coeffs 0).coeffs 0
    = _
  rw [map_henselG, coeffAt_jet, ← eval_zero_eq, eval_zero_jet]
  show eval3 (hasse 0 R) t₀ y z = _
  rw [hasse_zero]

theorem ptHom_henselSep (R : Poly3 K) (t₀ y v z : K) :
    (ptHom y v z).toFun (henselSep R t₀) = eval3 (hasseZ 1 R) t₀ y z :=
  (Hensel.map_sep _ _).trans (sep_map_henselG R t₀ y v z)

theorem eval_jet (R : Poly3 K) (t₀ y v z : K) (e : UPoly K) :
    (eval₂ (CHom.comp (jetHom t₀ y v)) (add (C (C z)) X) R).eval e =
      eval₂ (jetHom t₀ y v) (add (C z) e) R := by
  show (evalHom e).toFun (eval₂ (CHom.comp (jetHom t₀ y v)) (add (C (C z)) X) R) = _
  rw [hom_eval₂, RingHom.map_add, evalHom_apply, evalHom_apply, eval_C, eval_X]
  exact eval₂_congr _ _ (fun c => eval_C ((jetHom t₀ y v).toFun c) e) _ R

/-- **`[CWYZ26]` Lemma 3.11.** Let `(y, v, z) ∈ K³` with `R(t₀, y, z) = 0` and separant
    `s = ∂_Z R(t₀, y, z) ≠ 0`. Every `e` with `e(0) = 0` and
    `R(t₀ + W, y + v·W, z + e(W)) ≡ 0 (mod W^(n+1))` has coefficients
    `e_j = N_j(y, v, z) / s^(2j-1)` for `j ≤ n`, stated as `s·N_j(y, v, z) = (s²)^j·e_j`. -/
theorem henselNum_spec (R : Poly3 K) (t₀ y v z : K) (e : UPoly K) (n : Nat)
    (he0 : e.eval zero = zero) (hroot : eval3 R t₀ y z = zero)
    (hsep : eval3 (hasseZ 1 R) t₀ y z ≠ zero)
    (hsol : ∀ k, k ≤ n → coeffAt (eval₂ (jetHom t₀ y v) (add (C z) e) R).coeffs k = zero) :
    ∀ j, j ≤ n → mul (eval3 (hasseZ 1 R) t₀ y z) ((ptHom y v z).toFun (henselNum R t₀ j)) =
      mul (CRing.npow (mul (eval3 (hasseZ 1 R) t₀ y z) (eval3 (hasseZ 1 R) t₀ y z)) j)
        (coeffAt e.coeffs j) := by
  intro j hj
  have key := Hensel.num_spec ((mapHom (mapHom (ptHom y v z))).toFun (henselG R t₀)) e n he0
    (by rw [res_map_henselG]; exact hroot) (by rw [sep_map_henselG]; exact hsep)
    (fun k hk => by rw [map_henselG, eval_jet]; exact hsol k hk) j hj
  rw [sep_map_henselG, ← Hensel.map_num] at key
  exact key

/-! ### Reconstruction from the jet (`[CWYZ26]` Claim 4.9) -/

/-- Cleared coefficient of `W^j` in the reconstruction of a root from its jet:
    `S^(2d-1)·[W^j] P(t₀ + W)` as a polynomial in `(Y, V, Z)`. -/
def reconCoeff (R : Poly3 K) (t₀ : K) (d : Nat) : Nat → Poly3 K
  | 0 => mul (CRing.npow (henselSep R t₀) (2 * d - 1)) X
  | j + 1 => mul (CRing.npow (henselSep R t₀) (2 * d - 2 * (j + 1))) (henselNum R t₀ (j + 1))

theorem recon_arith (d h m n : Nat) (hd : 1 ≤ d) (hh : 1 ≤ h) (hmn : m + n ≤ 2 * d - 1) :
    m * (h - 1) + (1 + n * (h - 1)) ≤ 2 * d * h := by
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  show m * h' + (1 + n * h') ≤ 2 * d * (h' + 1)
  have e1 : (m + n) * h' = m * h' + n * h' := Nat.add_mul m n h'
  have e2 : (m + n) * h' ≤ 2 * d * h' := Nat.mul_le_mul_right h' (by omega)
  have e3 : 2 * d * (h' + 1) = 2 * d * h' + 2 * d := Nat.mul_succ (2 * d) h'
  omega

/-- **`[CWYZ26]` Claim 4.9, degree of the reconstruction map**: every cleared coefficient has
    `(Y, V, Z)`-degree at most `2·d·h`. -/
theorem deg_reconCoeff_le (R : Poly3 K) (t₀ : K) (d h j : Nat) (hR : R.degYZ ≤ h) (hh : 1 ≤ h)
    (hd : 1 ≤ d) (hj : j ≤ d) : deg11d 1 (reconCoeff R t₀ d j) ≤ 2 * d * h := by
  have hδ := degFn_deg11d (K := K) 1
  have hS := deg_henselSep_le R t₀ h hR
  cases j with
  | zero =>
    have h1 := hδ.mul_le (CRing.npow (henselSep R t₀) (2 * d - 1)) X
    have h2 := degFn_npow_le hδ (deg11d_one 1) _ _ hS (2 * d - 1)
    have h3 := deg11d_X_le (K := K)
    have h4 := recon_arith d h (2 * d - 1) 0 hd hh (by omega)
    show deg11d 1 (mul (CRing.npow (henselSep R t₀) (2 * d - 1)) X) ≤ 2 * d * h
    rw [Nat.zero_mul] at h4
    omega
  | succ j =>
    have h1 := hδ.mul_le (CRing.npow (henselSep R t₀) (2 * d - 2 * (j + 1)))
      (henselNum R t₀ (j + 1))
    have h2 := degFn_npow_le hδ (deg11d_one 1) _ _ hS (2 * d - 2 * (j + 1))
    have h3 := deg_henselNum_le R t₀ h (j + 1) hR hh (by omega)
    have h4 := recon_arith d h (2 * d - 2 * (j + 1)) (2 * (j + 1) - 1) hd hh (by omega)
    show deg11d 1 (mul (CRing.npow (henselSep R t₀) (2 * d - 2 * (j + 1)))
      (henselNum R t₀ (j + 1))) ≤ 2 * d * h
    omega

/-- **`[CWYZ26]` Claim 4.9, reconstruction identity.** Under the hypotheses of
    `henselNum_spec` with `n = d`, the cleared coefficients evaluate to
    `s^(2d-1)·[W^j](z + e(W))` for every `j ≤ d`: the root `z + e(W)` is recovered from the
    jet `(y, v, z)` by polynomials of degree at most `2·d·h` over the common denominator
    `s^(2d-1)`. -/
theorem reconCoeff_spec (R : Poly3 K) (t₀ y v z : K) (e : UPoly K) (d : Nat) (hd : 1 ≤ d)
    (he0 : e.eval zero = zero) (hroot : eval3 R t₀ y z = zero)
    (hsep : eval3 (hasseZ 1 R) t₀ y z ≠ zero)
    (hsol : ∀ k, k ≤ d → coeffAt (eval₂ (jetHom t₀ y v) (add (C z) e) R).coeffs k = zero) :
    ∀ j, j ≤ d → (ptHom y v z).toFun (reconCoeff R t₀ d j) =
      mul (CRing.npow (eval3 (hasseZ 1 R) t₀ y z) (2 * d - 1)) (coeffAt (add (C z) e).coeffs j) := by
  intro j hj
  have hS := ptHom_henselSep R t₀ y v z
  cases j with
  | zero =>
    show (ptHom y v z).toFun (mul (CRing.npow (henselSep R t₀) (2 * d - 1)) X) = _
    rw [RingHom.map_mul, RingHom.map_npow, hS, ptHom_X, coeffAt_add, coeffAt_C_zero,
      ← eval_zero_eq, he0, LawfulCommRing.add_zero]
  | succ j =>
    have key := henselNum_spec R t₀ y v z e d he0 hroot hsep hsol (j + 1) hj
    show (ptHom y v z).toFun (mul (CRing.npow (henselSep R t₀) (2 * d - 2 * (j + 1)))
      (henselNum R t₀ (j + 1))) = _
    rw [RingHom.map_mul, RingHom.map_npow, hS, coeffAt_add, coeffAt_C_succ,
      LawfulCommRing.zero_add]
    generalize eval3 (hasseZ 1 R) t₀ y z = s at hsep key ⊢
    generalize (ptHom y v z).toFun (henselNum R t₀ (j + 1)) = N at key ⊢
    generalize coeffAt e.coeffs (j + 1) = c at key ⊢
    have e1 : 2 * d - 1 + 1 = (2 * d - 2 * (j + 1)) + 2 * (j + 1) := by omega
    have h1 : mul s (mul (CRing.npow s (2 * d - 2 * (j + 1))) N) =
        mul s (mul (CRing.npow s (2 * d - 1)) c) := by
      have h2 : mul s (mul (CRing.npow s (2 * d - 1)) c) = mul (CRing.npow s (2 * d - 1 + 1)) c := by
        show _ = mul (mul (CRing.npow s (2 * d - 1)) s) c
        generalize CRing.npow s (2 * d - 1) = p
        constructive_ring
      rw [h2, e1, CRing.npow_add, ← npow_mul_self, LawfulCommRing.mul_assoc, ← key]
      generalize CRing.npow s (2 * d - 2 * (j + 1)) = p
      constructive_ring
    have h3 := congrArg (mul (LawfulField.inv s)) h1
    rwa [← LawfulCommRing.mul_assoc (LawfulField.inv s) s,
      ← LawfulCommRing.mul_assoc (LawfulField.inv s) s, LawfulField.inv_mul_cancel hsep,
      LawfulCommRing.one_mul, LawfulCommRing.one_mul] at h3

end Poly3

/-! ## Witnesses -/

end Qsag

end

namespace Qsag
theorem gsUniHasseBasis_mul_eq_monomial {F : Type} [LawfulCommRing F]
    (r s : Nat) (a b : F) (i j : Nat) :
    CommRingOps.mul (gsUniHasseBasis s b j) (gsUniHasseBasis r a i) =
      gsHasseMonomial (i,j) (r,s) (a,b) := by
  unfold gsUniHasseBasis gsHasseMonomial
  dsimp only
  rw [gsNat_mul, LawfulCommRing.mul_comm (gsNat (gsChoose i r)) (gsNat (gsChoose j s)),
    LawfulCommRing.mul_comm (gsPow a (i-r)) (gsPow b (j-s))]
  exact gs_mul_mul_mul_comm _ _ _ _
end Qsag

namespace Qsag
open CommRingOps RoundPoly UPoly
/-! ## Triangular index sets -/

/-- `Σ_{j<n} f j`. -/
@[expose] def sumTo (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo f n + f n

theorem sumTo_add (f : Nat → Nat) (n : Nat) :
    ∀ m, sumTo f (n + m) = sumTo f n + sumTo (fun j => f (n + j)) m
  | 0 => rfl
  | m + 1 => by
    show sumTo f (n + m) + f (n + m) = sumTo f n + (sumTo (fun j => f (n + j)) m + f (n + m))
    rw [sumTo_add f n m]; omega

theorem sumTo_le (f g : Nat → Nat) (d : Nat) :
    ∀ n, (∀ j, j < n → f j ≤ g j + d) → sumTo f n ≤ sumTo g n + n * d
  | 0, _ => by show 0 ≤ 0 + 0 * d; omega
  | n + 1, h => by
    have ih := sumTo_le f g d n (fun j hj => h j (by omega))
    have := h n (by omega)
    show sumTo f n + f n ≤ sumTo g n + g n + (n + 1) * d
    rw [Nat.succ_mul]; omega

theorem sumTo_succ (f : Nat → Nat) : ∀ n, sumTo f (n + 1) = f 0 + sumTo (fun j => f (j + 1)) n
  | 0 => by show 0 + f 0 = f 0 + 0; omega
  | n + 1 => by
    show sumTo f (n + 1) + f (n + 1) = f 0 + (sumTo (fun j => f (j + 1)) n + f (n + 1))
    rw [sumTo_succ f n]; omega

/-- Index pairs `(i, j)` with `j < n` and `i < f j`. -/
def rows (f : Nat → Nat) : Nat → List (Nat × Nat)
  | 0 => []
  | n + 1 => rows f n ++ (List.range (f n)).map (fun i => (i, n))

theorem length_rows (f : Nat → Nat) : ∀ n, (rows f n).length = sumTo f n
  | 0 => rfl
  | n + 1 => by
    show (rows f n ++ _).length = sumTo f n + f n
    rw [List.length_append, List.length_map, List.length_range, length_rows f n]

theorem mem_rows (f : Nat → Nat) (i j : Nat) : ∀ n, (i, j) ∈ rows f n ↔ j < n ∧ i < f j
  | 0 => by
    constructor
    · intro h; cases h
    · intro h; omega
  | n + 1 => by
    show (i, j) ∈ rows f n ++ _ ↔ _
    rw [List.mem_append, mem_rows f i j n, List.mem_map]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨i', hi', he⟩)
      · exact ⟨by omega, h2⟩
      · cases he; exact ⟨by omega, List.mem_range.mp hi'⟩
    · rintro ⟨h1, h2⟩
      if h : j < n then exact .inl ⟨h, h2⟩
      else
        have hj : j = n := by omega
        subst hj; exact .inr ⟨i, List.mem_range.mpr h2, rfl⟩

/-- `List.range` has no duplicates (the core lemma is not choice-free). -/
private theorem nodup_range' : ∀ k, (List.range k).Nodup
  | 0 => by rw [List.range_zero]; exact .nil
  | k + 1 => by
    rw [List.range_succ, List.nodup_append]
    exact ⟨nodup_range' k, List.pairwise_singleton _ _, fun a ha b hb e => by
      have := List.mem_range.mp ha
      have := List.mem_singleton.mp hb
      omega⟩

theorem nodup_rows (f : Nat → Nat) : ∀ n, (rows f n).Nodup
  | 0 => .nil
  | n + 1 => by
    show (rows f n ++ _).Nodup
    rw [List.nodup_append]
    refine ⟨nodup_rows f n, ?_, ?_⟩
    · exact List.pairwise_map.mpr
        (List.Pairwise.imp (fun h e => h (congrArg Prod.fst e)) (nodup_range' _))
    · intro p hp q hq e
      subst e
      obtain ⟨i, j⟩ := p
      have h1 := ((mem_rows f i j n).mp hp).1
      obtain ⟨i', _, he⟩ := List.mem_map.mp hq
      cases he
      omega


namespace Poly3
variable {F : Type} [LawfulField F] [DecidableEq F]
/-- Coefficient of `X^i Y^t Z^j`. -/
def coeff3 (Q : Poly3 F) (i t j : Nat) : F :=
  coeffAt (coeffAt (coeffAt Q.coeffs j).coeffs t).coeffs i

/-- `F`-linear functionals on `F[X][Y][Z]`. -/
structure IsLin (ℓ : Poly3 F → F) : Prop where
  map_add : ∀ a b, ℓ (add a b) = add (ℓ a) (ℓ b)
  map_zero : ℓ zero = zero
  map_smul : ∀ x a, ℓ (mul (C3 x) a) = mul x (ℓ a)

theorem isLin_coeff3 (i t j : Nat) : IsLin (fun Q : Poly3 F => coeff3 Q i t j) where
  map_add a b := by
    show coeffAt (coeffAt (coeffAt (add a b).coeffs j).coeffs t).coeffs i = _
    rw [coeffAt_add, coeffAt_add, coeffAt_add]; rfl
  map_zero := by
    show coeffAt (coeffAt (coeffAt (zero : Poly3 F).coeffs j).coeffs t).coeffs i = zero
    rw [coeffs_zero, coeffAt_nil, coeffs_zero, coeffAt_nil, coeffs_zero, coeffAt_nil]
  map_smul x a := by
    show coeffAt (coeffAt (coeffAt (mul (C (C (C x))) a).coeffs j).coeffs t).coeffs i = _
    rw [coeffAt_C_mul, coeffAt_C_mul, coeffAt_C_mul]; rfl

/-- `Σ_k x_k · g_k`. -/
def comb : List F → List (Poly3 F) → Poly3 F
  | x :: xs, g :: gs => add (mul (C3 x) g) (comb xs gs)
  | [], _ => zero
  | _ :: _, [] => zero

theorem lin_comb {ℓ : Poly3 F → F} (h : IsLin ℓ) : ∀ (xs : List F) (gs : List (Poly3 F)),
    ℓ (comb xs gs) = dotVec (gs.map ℓ) xs
  | [], gs => by
    show ℓ zero = _
    rw [h.map_zero]; cases gs <;> rfl
  | _ :: _, [] => h.map_zero
  | x :: xs, g :: gs => by
    show ℓ (add (mul (C3 x) g) (comb xs gs)) = add (mul (ℓ g) x) (dotVec (gs.map ℓ) xs)
    rw [h.map_add, h.map_smul, lin_comb h xs gs, LawfulCommRing.mul_comm]

theorem degFn_comb_le {δ : Poly3 F → Nat} (hδ : DegFn δ) (hC : ∀ x : F, δ (C3 x) = 0)
    (B : Nat) : ∀ (xs : List F) (gs : List (Poly3 F)), (∀ g ∈ gs, δ g ≤ B) →
      δ (comb xs gs) ≤ B
  | [], _, _ => by show δ zero ≤ B; rw [hδ.zero]; exact Nat.zero_le _
  | _ :: _, [], _ => by show δ zero ≤ B; rw [hδ.zero]; exact Nat.zero_le _
  | x :: xs, g :: gs, h => by
    show δ (add (mul (C3 x) g) (comb xs gs)) ≤ B
    have h1 := hδ.add_le (mul (C3 x) g) (comb xs gs)
    have h2 := hδ.mul_le (C3 x) g
    have h3 := h g (.head _)
    have h4 := degFn_comb_le hδ hC B xs gs (fun g' hg' => h g' (.tail _ hg'))
    rw [hC x] at h2
    omega

/-- `b₀ + b₁ Y ∈ F[X][Y]`. -/
def yLine (b₀ b₁ : F) : UPoly (UPoly F) := ofList [C b₀, C b₁]

theorem natDeg_yLine_le (b₀ b₁ : F) : (yLine b₀ b₁).natDeg ≤ 1 := by
  have := trimPoly_length_le [C b₀, C b₁]
  show (trimPoly [C b₀, C b₁]).length - 1 ≤ 1
  simp only [List.length_cons, List.length_nil] at this; omega

/-- `Q(X, Y, Z) ↦ Q(z + X, Y, b₀ + b₁Y + Z)`. -/
def shiftHom (z b₀ b₁ : F) : RingHom (Poly3 F) (Poly3 F) :=
  (taylorShift (yLine b₀ b₁)).comp (mapHom (mapHom (taylorShift z)))

theorem shiftHom_C3 (z b₀ b₁ x : F) : (shiftHom z b₀ b₁).toFun (C3 x) = C3 x := by
  show (taylorShift (yLine b₀ b₁)).toFun
    ((mapHom (mapHom (taylorShift z))).toFun (C (C (C x)))) = C (C (C x))
  rw [mapHom_C, mapHom_C, taylorShift_C, taylorShift_C]

theorem degYZ_shiftHom_le (z b₀ b₁ : F) (Q : Poly3 F) :
    ((shiftHom z b₀ b₁).toFun Q).degYZ ≤ Q.degYZ := by
  have hX : (X : Poly3 F).wdeg natDeg 1 ≤ 1 := by
    have := wdeg_X_le (R := UPoly (UPoly F)) natDeg 1
    rw [natDeg_one] at this; omega
  have hs : (add (C (yLine b₀ b₁)) (X : Poly3 F)).wdeg natDeg 1 ≤ 1 := by
    have h1 := (degFn_degYZ (K := F)).add_le (C (yLine b₀ b₁)) X
    have h2 : (C (yLine b₀ b₁) : Poly3 F).wdeg natDeg 1 ≤ (yLine b₀ b₁).natDeg :=
      wdeg_C_le natDeg 1 _
    have h3 := natDeg_yLine_le b₀ b₁
    have h1' : (add (C (yLine b₀ b₁)) (X : Poly3 F)).wdeg natDeg 1 ≤
        max ((C (yLine b₀ b₁) : Poly3 F).wdeg natDeg 1) ((X : Poly3 F).wdeg natDeg 1) := h1
    omega
  have hb := degFn_eval₂_le (degFn_degYZ (K := F)) CHom natDeg (fun c => wdeg_C_le natDeg 1 c)
    (add (C (yLine b₀ b₁)) X) 1 hs ((mapHom (mapHom (taylorShift z))).toFun Q)
  exact Nat.le_trans hb (wdeg_mapHom_mapHom_le (taylorShift z) Q)

/-- The constraint functional: the coefficient of `X^r Y^t Z^s` in the shifted polynomial. -/
def cons (z b₀ b₁ : F) (r t s : Nat) (Q : Poly3 F) : F :=
  coeff3 ((shiftHom z b₀ b₁).toFun Q) r t s

theorem isLin_cons (z b₀ b₁ : F) (r t s : Nat) : IsLin (cons z b₀ b₁ r t s) where
  map_add a b := by
    show coeff3 ((shiftHom z b₀ b₁).toFun (add a b)) r t s = _
    rw [RingHom.map_add]; exact (isLin_coeff3 r t s).map_add _ _
  map_zero := by
    show coeff3 ((shiftHom z b₀ b₁).toFun zero) r t s = _
    rw [RingHom.map_zero]; exact (isLin_coeff3 r t s).map_zero
  map_smul x a := by
    show coeff3 ((shiftHom z b₀ b₁).toFun (mul (C3 x) a)) r t s = _
    rw [RingHom.map_mul, shiftHom_C3]; exact (isLin_coeff3 r t s).map_smul _ _

/-- `Q(X, Y, Z) ↦ Q(X - z, α + βX, Zv)`. -/
def unshiftHom (z α β : F) (Zv : UPoly F) : RingHom (Poly3 F) (UPoly F) :=
  eval₂Hom (eval₂Hom (taylorShift (neg z)) (line α β)) Zv

/-- Undoing the shift along the line: `Q(z + (X - z), α + βX, b₀ + b₁(α + βX) + Zv)` with
    `Zv = P - b₀ - b₁(α + βX)` is `Q(X, α + βX, P)`. -/
theorem unshift_shift (z b₀ b₁ α β : F) (P : UPoly F) (Q : Poly3 F) :
    (unshiftHom z α β (sub P (add (C b₀) (mul (line α β) (C b₁))))).toFun
      ((shiftHom z b₀ b₁).toFun Q) = evalAffineLine Q α β P := by
  let Zv : UPoly F := sub P (add (C b₀) (mul (line α β) (C b₁)))
  let mid : RingHom (UPoly (UPoly F)) (UPoly F) := eval₂Hom (taylorShift (neg z)) (line α β)
  have hmid : ∀ c : UPoly (UPoly F),
      mid.toFun ((mapHom (taylorShift z)).toFun c) = (evalHom (line α β)).toFun c := by
    intro c
    refine hom_ext (mid.comp (mapHom (taylorShift z))) (evalHom (line α β)) (fun a => ?_) ?_ c
    · show mid.toFun ((mapHom (taylorShift z)).toFun (C a)) = (C a).eval (line α β)
      rw [mapHom_C, eval_C]
      show eval₂ (taylorShift (neg z)) (line α β) (C ((taylorShift z).toFun a)) = a
      rw [eval₂_C, taylorShift_neg_cancel]
    · show mid.toFun ((mapHom (taylorShift z)).toFun X) = (X : UPoly (UPoly F)).eval (line α β)
      rw [mapHom_X, eval_X]
      exact eval₂_X _ _
  refine hom_ext ((unshiftHom z α β Zv).comp (shiftHom z b₀ b₁)) (affineLineHom α β P)
    (fun c => ?_) ?_ Q
  · show eval₂ mid Zv ((taylorShift (yLine b₀ b₁)).toFun
      ((mapHom (mapHom (taylorShift z))).toFun (C c))) = eval₂ (evalHom (line α β)) P (C c)
    rw [mapHom_C, taylorShift_C, eval₂_C, eval₂_C]
    exact hmid c
  · show eval₂ mid Zv ((taylorShift (yLine b₀ b₁)).toFun
      ((mapHom (mapHom (taylorShift z))).toFun X)) = eval₂ (evalHom (line α β)) P X
    rw [mapHom_X, taylorShift_X, eval₂_X]
    show (eval₂Hom mid Zv).toFun (add (C (yLine b₀ b₁)) X) = P
    rw [RingHom.map_add]
    show add (eval₂ mid Zv (C (yLine b₀ b₁))) (eval₂ mid Zv X) = P
    rw [eval₂_C, eval₂_X]
    have hy : mid.toFun (yLine b₀ b₁) =
        add (C b₀) (mul (line α β) (add (C b₁) (mul (line α β) zero))) := by
      show eval₂ (taylorShift (neg z)) (line α β) (ofList [C b₀, C b₁]) = _
      rw [eval₂_ofList]
      show add ((taylorShift (neg z)).toFun (C b₀)) (mul (line α β)
        (add ((taylorShift (neg z)).toFun (C b₁)) (mul (line α β) zero))) = _
      rw [taylorShift_C, taylorShift_C]
    rw [hy]
    show add _ (sub P (add (C b₀) (mul (line α β) (C b₁)))) = P
    constructive_ring

theorem eval_line (α β z : F) : (line α β).eval z = add α (mul β z) := by
  rw [eval_eq]
  show evalCoeffs (trimPoly [α, β]) z = _
  rw [evalCoeffs_trimPoly]
  show add α (mul z (add β (mul z zero))) = _
  constructive_ring

/-- A polynomial vanishing at `z` is a multiple of `X - z`. -/
theorem exists_mul_of_eval_eq_zero (p : UPoly F) (z : F) (h : p.eval z = zero) :
    ∃ w, p = mul (add (C (neg z)) X) w := by
  have h0 : coeffAt ((taylorShift z).toFun p).coeffs 0 = zero := by
    rw [← eval_zero_eq, eval_taylorShift, LawfulCommRing.add_zero, h]
  have hsplit := eq_C_add_X_mul ((taylorShift z).toFun p)
  rw [h0] at hsplit
  refine ⟨(taylorShift (neg z)).toFun (shiftDown ((taylorShift z).toFun p)), ?_⟩
  have := congrArg (taylorShift (neg z)).toFun hsplit
  rw [taylorShift_neg_cancel, RingHom.map_add, RingHom.map_mul, taylorShift_C, taylorShift_X,
    ← CHom_apply, CHom.map_zero, LawfulCommRing.zero_add] at this
  exact this

/-- **Multiplicity gives divisibility** (the substitution step of `[CWYZ26]` Lemma 4.2).
    If `Q` satisfies the order-`m` constraints at `z` for the values `b₀ = f z`, `b₁ = g z`,
    and `P(z) = b₀ + (α + βz)·b₁`, then `(X - z)^m` divides `Q(X, α + βX, P(X))`. -/
theorem inPow_affine_of_cons (Q : Poly3 F) (z b₀ b₁ α β : F) (P : UPoly F) (m : Nat)
    (hcons : ∀ r t s, r + s < m → cons z b₀ b₁ r t s Q = zero)
    (hagree : P.eval z = add b₀ (mul (add α (mul β z)) b₁)) :
    InPow (add (C (neg z)) X) m (evalAffineLine Q α β P) := by
  have hZ : (sub P (add (C b₀) (mul (line α β) (C b₁)))).eval z = zero := by
    show (evalHom z).toFun (sub P (add (C b₀) (mul (line α β) (C b₁)))) = zero
    rw [RingHom.map_sub, RingHom.map_add, RingHom.map_mul, evalHom_apply, evalHom_apply,
      evalHom_apply, evalHom_apply, eval_C, eval_C, eval_line, hagree]
    constructive_ring
  obtain ⟨w, hw⟩ := exists_mul_of_eval_eq_zero _ z hZ
  rw [← unshift_shift z b₀ b₁ α β P Q, hw]
  show InPow _ m (evalCoeffs (((shiftHom z b₀ b₁).toFun Q).coeffs.map
    (eval₂Hom (taylorShift (neg z)) (line α β)).toFun) (mul (add (C (neg z)) X) w))
  apply InPow.evalCoeffs_graded
  intro s
  rw [RingHom.coeffAt_map]
  show InPow _ (m - s) (evalCoeffs ((coeffAt ((shiftHom z b₀ b₁).toFun Q).coeffs s).coeffs.map
    (taylorShift (neg z)).toFun) (line α β))
  apply InPow.evalCoeffs_all
  intro t
  rw [RingHom.coeffAt_map]
  show InPow _ (m - s) (evalCoeffs
    ((coeffAt (coeffAt ((shiftHom z b₀ b₁).toFun Q).coeffs s).coeffs t).coeffs.map
      (CHom (R := F)).toFun) (add (C (neg z)) X))
  apply InPow.evalCoeffs_low
  intro r hr
  exact hcons r t s (by omega)

/-! ## Enough agreement forces the specialization to vanish -/

/-- The same polynomial in the subtype presentation used by the bivariate decoder. -/
def toGs (p : UPoly F) : GsUniPoly F := ⟨p.coeffs, p.trimmed⟩

theorem toGs_mul (a b : UPoly F) : toGs (mul a b) = mul (toGs a) (toGs b) := by rfl

theorem toGs_npow (u : UPoly F) : ∀ k : Nat, toGs (CRing.npow u k) = gsPow (toGs u) k
  | 0 => rfl
  | k + 1 => by
    show toGs (mul (CRing.npow u k) u) = mul (toGs u) (gsPow (toGs u) k)
    rw [toGs_mul, toGs_npow u k, LawfulCommRing.mul_comm]

theorem toGs_linear (z : F) : toGs (add (C (neg z)) X) = gsLinear z := by
  have e : add (C (neg z)) X = (⟨[neg z, one], gsLinear_trimmed z⟩ : UPoly F) := by
    apply ext_coeffAt
    intro k
    rw [coeffAt_add]
    have eX : coeffAt (X : UPoly F).coeffs k = coeffAt [zero, one] k := coeffAt_ofList _ k
    rw [eX]
    cases k with
    | zero => rw [coeffAt_C_zero]; exact LawfulCommRing.add_zero _
    | succ k =>
      rw [coeffAt_C_succ, LawfulCommRing.zero_add]
      cases k <;> rfl
  rw [e]; rfl

/-- Triples `(i, t, j)` with `j < n`, `t + j ≤ Dy` and `i + d·j < Wx`. -/
def triples (d Wx Dy : Nat) : Nat → List (Nat × Nat × Nat)
  | 0 => []
  | n + 1 => triples d Wx Dy n ++
      (rows (fun _ => Wx - d * n) (Dy + 1 - n)).map (fun p => (p.1, p.2, n))

/-- `Σ_{j<n} (Dy + 1 - j)·(Wx - d·j)`, as an iterated sum. -/
def triCount (d Wx Dy n : Nat) : Nat :=
  sumTo (fun j => sumTo (fun _ => Wx - d * j) (Dy + 1 - j)) n

theorem sumTo_const (c : Nat) : ∀ n, sumTo (fun _ => c) n = n * c
  | 0 => (Nat.zero_mul c).symm
  | n + 1 => by
    show sumTo (fun _ => c) n + c = (n + 1) * c
    rw [sumTo_const c n, Nat.succ_mul]

theorem sumTo_congr (f g : Nat → Nat) : ∀ n, (∀ j, j < n → f j = g j) → sumTo f n = sumTo g n
  | 0, _ => rfl
  | n + 1, h => by
    show sumTo f n + f n = sumTo g n + g n
    rw [sumTo_congr f g n (fun j hj => h j (Nat.lt_succ_of_lt hj)), h n (Nat.lt_succ_self n)]

/-- The count in closed form: `Σ_{j<n} (Dy + 1 - j)·(Wx - d·j)`. -/
theorem triCount_eq (d Wx Dy n : Nat) :
    triCount d Wx Dy n = sumTo (fun j => (Dy + 1 - j) * (Wx - d * j)) n :=
  sumTo_congr _ _ n (fun _ _ => sumTo_const _ _)

theorem triCount_zero_width (d Dy : Nat) : ∀ n, triCount d 0 Dy n = 0
  | 0 => rfl
  | n + 1 => by
    show triCount d 0 Dy n + sumTo (fun _ => 0 - d * n) (Dy + 1 - n) = 0
    rw [triCount_zero_width d Dy n, sumTo_const, Nat.zero_sub, Nat.mul_zero]

theorem length_triples (d Wx Dy : Nat) : ∀ n, (triples d Wx Dy n).length = triCount d Wx Dy n
  | 0 => rfl
  | n + 1 => by
    show (triples d Wx Dy n ++ _).length =
      triCount d Wx Dy n + sumTo (fun _ => Wx - d * n) (Dy + 1 - n)
    rw [List.length_append, List.length_map, length_rows, length_triples d Wx Dy n]

theorem mem_triples (d Wx Dy i t j : Nat) : ∀ n,
    (i, t, j) ∈ triples d Wx Dy n ↔ j < n ∧ t < Dy + 1 - j ∧ i < Wx - d * j
  | 0 => by
    constructor
    · intro h; cases h
    · intro h; exact absurd h.1 (Nat.not_lt_zero j)
  | n + 1 => by
    show (i, t, j) ∈ triples d Wx Dy n ++ _ ↔ _
    rw [List.mem_append, mem_triples d Wx Dy i t j n, List.mem_map]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨p, hp, he⟩)
      · exact ⟨Nat.lt_succ_of_lt h1, h2⟩
      · obtain ⟨i', t'⟩ := p
        cases he
        exact ⟨Nat.lt_succ_self _, (mem_rows _ _ _ _).mp hp⟩
    · rintro ⟨h1, h2⟩
      if h : j < n then exact .inl ⟨h, h2⟩
      else
        have hj : j = n := by omega
        subst hj
        exact .inr ⟨(i, t), (mem_rows _ _ _ _).mpr h2, rfl⟩

theorem nodup_triples (d Wx Dy : Nat) : ∀ n, (triples d Wx Dy n).Nodup
  | 0 => .nil
  | n + 1 => by
    show (triples d Wx Dy n ++ _).Nodup
    rw [List.nodup_append]
    refine ⟨nodup_triples d Wx Dy n, ?_, ?_⟩
    · exact List.pairwise_map.mpr (List.Pairwise.imp (fun h e => h (by
        obtain ⟨e1, e2⟩ := Prod.mk.inj e
        exact Prod.ext e1 (Prod.mk.inj e2).1)) (nodup_rows _ _))
    · intro p hp q hq e
      subst e
      obtain ⟨i, t, j⟩ := p
      have h1 := ((mem_triples d Wx Dy i t j n).mp hp).1
      obtain ⟨p', _, he⟩ := List.mem_map.mp hq
      cases he
      omega


end Poly3
end Qsag

namespace Qsag
@[simp] theorem rows_zero (f : Nat → Nat) : rows f 0 = [] := by rfl
namespace UPoly
theorem inPow_iff {R : Type} [LawfulCommRing R] [DecidableEq R] (x : UPoly R) (n : Nat) (p : UPoly R) :
    InPow x n p ↔ ∃ q, p = CommRingOps.mul (CRing.npow x n) q := by rfl
end UPoly
namespace Poly3
theorem toGs_eq {F : Type} [LawfulField F] [DecidableEq F] (p : UPoly F) : toGs p = p := by rfl
end Poly3
end Qsag

namespace Qsag.Poly3
variable {F : Type} [LawfulField F] [DecidableEq F]
theorem coeff3_eq (Q : Poly3 F) (i t j : Nat) : coeff3 Q i t j =
    coeffAt (coeffAt (coeffAt Q.coeffs j).coeffs t).coeffs i := by unfold coeff3; rfl
theorem cons_eq (z b₀ b₁ : F) (r t s : Nat) (Q : Poly3 F) :
    cons z b₀ b₁ r t s Q = coeff3 ((shiftHom z b₀ b₁).toFun Q) r t s := by unfold cons; rfl
end Qsag.Poly3

namespace Qsag
open CommRingOps
/-- Nonvanishing of a natural number is reflected by ring homomorphisms. -/
theorem natCast_ne_zero_of_hom {R S : Type} [LawfulCommRing R] [LawfulCommRing S]
    (φ : RingHom R S) (k : Nat) (h : (CRing.natCast k : S) ≠ zero) :
    (CRing.natCast k : R) ≠ zero := fun e => h (by
  rw [← RingHom.map_natCast φ k, e, φ.map_zero])

/-- Nonvanishing of a natural number is preserved by injective ring homomorphisms. -/
theorem natCast_ne_zero_of_injective_hom {R S : Type} [LawfulCommRing R] [LawfulCommRing S]
    (φ : RingHom R S) (hinj : ∀ x, φ.toFun x = zero → x = zero) (k : Nat)
    (h : (CRing.natCast k : R) ≠ zero) : (CRing.natCast k : S) ≠ zero := fun e =>
  h (hinj _ ((RingHom.map_natCast φ k).trans e))


end Qsag

namespace Qsag
open CommRingOps RoundPoly UPoly
/-! ## The jet of a root at the generic point (`[CWYZ26]` Claim 4.9, covering part) -/

namespace UPoly

theorem mapHom_shift2 {R S : Type} [LawfulCommRing R] [DecidableEq R] [LawfulCommRing S]
    [DecidableEq S] (φ : RingHom R S) (p : UPoly R) :
    (mapHom (mapHom φ)).toFun ((shift2 (R := R)).toFun p) =
      (shift2 (R := S)).toFun ((mapHom φ).toFun p) := by
  refine hom_ext ((mapHom (mapHom φ)).comp shift2) (shift2.comp (mapHom φ)) (fun c => ?_) ?_ p
  · show (mapHom (mapHom φ)).toFun (eval₂ (CHom.comp CHom) (add (C X) X) (C c)) =
      eval₂ (CHom.comp CHom) (add (C X) X) ((mapHom φ).toFun (C c))
    rw [eval₂_C, mapHom_C, eval₂_C]
    show (mapHom (mapHom φ)).toFun (C (C c)) = C (C (φ.toFun c))
    rw [mapHom_C, mapHom_C]
  · show (mapHom (mapHom φ)).toFun (eval₂ (CHom.comp CHom) (add (C X) X) X) =
      eval₂ (CHom.comp CHom) (add (C X) X) ((mapHom φ).toFun X)
    rw [eval₂_X, mapHom_X, eval₂_X, RingHom.map_add, mapHom_C, mapHom_X, mapHom_X]

/-- Hasse derivatives commute with base change of the coefficients. -/
theorem mapHom_hasse {R S : Type} [LawfulCommRing R] [DecidableEq R] [LawfulCommRing S]
    [DecidableEq S] (φ : RingHom R S) (k : Nat) (p : UPoly R) :
    (mapHom φ).toFun (hasse k p) = hasse k ((mapHom φ).toFun p) := by
  rw [hasse_eq_coeff, hasse_eq_coeff, ← mapHom_shift2, coeffAt_mapHom]

end UPoly

namespace Poly3
section Generic
variable {F : Type} [LawfulField F] [DecidableEq F]
open UPoly

/-- Scalars into `F(T₀)`. -/
def scalK : RingHom F (RatFunc F) := (Frac.of (D := UPoly F)).comp CHom

/-- The generic point `T₀ ∈ F(T₀)`. -/
def genPt : RatFunc F := (Frac.of (D := UPoly F)).toFun X

/-- Base change `F[X][Y][Z] → F(T₀)[X][Y][Z]`. -/
def baseK : RingHom (Poly3 F) (Poly3 (RatFunc F)) := mapHom (mapHom (mapHom scalK))

/-- The root series of `P` at the generic point: `P(T₀ + W) - P(T₀)`. -/
def genSeries (P : UPoly F) : UPoly (RatFunc F) :=
  sub ((taylorShift genPt).toFun ((mapHom scalK).toFun P)) (C ((Frac.of (D := UPoly F)).toFun P))

/-- Evaluating a polynomial at the generic point is the embedding `F[X] → F(T₀)`. -/
theorem eval_gen (c : UPoly F) :
    ((mapHom (scalK (F := F))).toFun c).eval genPt = (Frac.of (D := UPoly F)).toFun c := by
  show eval₂ (RingHom.id _) genPt ((mapHom scalK).toFun c) = _
  rw [eval₂_mapHom]
  have h := hom_eval₂ (Frac.of (D := UPoly F)) CHom X c
  have e : eval₂ (CHom (R := F)) X c = c := evalCoeffs_C_X c
  rw [e] at h
  exact (eval₂_congr _ _ (fun _ => rfl) _ c).trans h.symm

theorem eval₂_gen (y₀ : UPoly F) (q : UPoly (UPoly F)) :
    eval₂ (evalHom genPt) ((Frac.of (D := UPoly F)).toFun y₀) ((mapHom (mapHom scalK)).toFun q) =
      (Frac.of (D := UPoly F)).toFun (q.eval y₀) := by
  rw [eval₂_mapHom]
  show _ = (Frac.of (D := UPoly F)).toFun (eval₂ (RingHom.id _) y₀ q)
  rw [hom_eval₂]
  exact eval₂_congr _ _ (fun c => eval_gen c) _ q

theorem eval3_gen (R : Poly3 F) (y₀ P : UPoly F) :
    eval3 (baseK.toFun R) genPt ((Frac.of (D := UPoly F)).toFun y₀)
      ((Frac.of (D := UPoly F)).toFun P) =
      (Frac.of (D := UPoly F)).toFun (eval₂ (evalHom y₀) P R) := by
  show eval₂ (eval₂Hom (evalHom genPt) ((Frac.of (D := UPoly F)).toFun y₀))
    ((Frac.of (D := UPoly F)).toFun P) ((mapHom (mapHom (mapHom scalK))).toFun R) = _
  rw [eval₂_mapHom, hom_eval₂]
  exact eval₂_congr _ _ (fun q => eval₂_gen y₀ q) _ R

theorem jet_gen (α β : F) (q : UPoly (UPoly F)) :
    (jetHom genPt ((Frac.of (D := UPoly F)).toFun (line α β)) (scalK.toFun β)).toFun
      ((mapHom (mapHom scalK)).toFun q) =
      (taylorShift genPt).toFun ((mapHom scalK).toFun (q.eval (line α β))) := by
  have e1 : line α β = add (C α) (mul X (C β)) := ofList_cons α [β]
  have hL : (taylorShift genPt).toFun ((mapHom (scalK (F := F))).toFun (line α β)) =
      add (C (scalK.toFun α)) (mul (add (C genPt) X) (C (scalK.toFun β))) := by
    rw [e1, RingHom.map_add, RingHom.map_mul, mapHom_C, mapHom_C, mapHom_X, RingHom.map_add,
      RingHom.map_mul, taylorShift_C, taylorShift_C, taylorShift_X]
  have hR : (C ((Frac.of (D := UPoly F)).toFun (line α β)) : UPoly (RatFunc F)) =
      add (C (scalK.toFun α)) (mul (C genPt) (C (scalK.toFun β))) := by
    rw [e1, RingHom.map_add, RingHom.map_mul]
    exact ((CHom (R := RatFunc F)).map_add _ _).trans
      (congrArg (add _) ((CHom (R := RatFunc F)).map_mul _ _))
  have hline : (taylorShift genPt).toFun ((mapHom (scalK (F := F))).toFun (line α β)) =
      add (C ((Frac.of (D := UPoly F)).toFun (line α β))) (mul (C (scalK.toFun β)) X) := by
    rw [hL, hR]; constructive_ring
  show eval₂ (taylorShift genPt) _ ((mapHom (mapHom scalK)).toFun q) =
    (taylorShift genPt).toFun ((mapHom scalK).toFun (eval₂ (RingHom.id _) (line α β) q))
  rw [eval₂_mapHom, hom_eval₂, hom_eval₂, hline]
  exact eval₂_congr _ _ (fun _ => rfl) _ q

/-- The hypotheses of `henselNum_spec` hold for every simple root on a line, at the generic
    point of `F(T₀)`: the jet is `(y, v, z) = (α + βT₀, β, P(T₀))` and the series is
    `P(T₀ + W) - P(T₀)`, to every order. -/
theorem jet_hyps (R : Poly3 F) (α β : F) (P : UPoly F) (hroot : evalAffineLine R α β P = zero)
    (hsep : evalAffineLine (hasseZ 1 R) α β P ≠ zero) :
    (genSeries P).eval zero = zero ∧
    eval3 (baseK.toFun R) genPt ((Frac.of (D := UPoly F)).toFun (line α β))
      ((Frac.of (D := UPoly F)).toFun P) = zero ∧
    eval3 (hasseZ 1 (baseK.toFun R)) genPt ((Frac.of (D := UPoly F)).toFun (line α β))
      ((Frac.of (D := UPoly F)).toFun P) =
        (Frac.of (D := UPoly F)).toFun (evalAffineLine (hasseZ 1 R) α β P) ∧
    (Frac.of (D := UPoly F)).toFun (evalAffineLine (hasseZ 1 R) α β P) ≠ zero ∧
    eval₂ (jetHom genPt ((Frac.of (D := UPoly F)).toFun (line α β)) (scalK.toFun β))
      (add (C ((Frac.of (D := UPoly F)).toFun P)) (genSeries P)) (baseK.toFun R) = zero := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show (evalHom zero).toFun (sub ((taylorShift genPt).toFun ((mapHom scalK).toFun P))
      (C ((Frac.of (D := UPoly F)).toFun P))) = zero
    rw [RingHom.map_sub, evalHom_apply, evalHom_apply, eval_taylorShift, LawfulCommRing.add_zero,
      eval_gen, eval_C, LawfulCommRing.sub_self]
  · rw [eval3_gen]
    show (Frac.of (D := UPoly F)).toFun (evalAffineLine R α β P) = zero
    rw [hroot, RingHom.map_zero]
  · have e : hasseZ 1 (baseK.toFun R) = baseK.toFun (hasseZ 1 R) :=
      (mapHom_hasse (mapHom (mapHom (scalK (F := F)))) 1 R).symm
    rw [e, eval3_gen]; rfl
  · exact fun e => hsep (Frac.of_injective (e.trans (Frac.of (D := UPoly F)).map_zero.symm))
  · have hadd : add (C ((Frac.of (D := UPoly F)).toFun P)) (genSeries P) =
        (taylorShift genPt).toFun ((mapHom scalK).toFun P) := by
      show add _ (sub _ _) = _
      constructive_ring
    rw [hadd]
    show eval₂ _ _ ((mapHom (mapHom (mapHom scalK))).toFun R) = zero
    rw [eval₂_mapHom]
    have h := hom_eval₂ ((taylorShift genPt).comp (mapHom (scalK (F := F))))
      (evalHom (line α β)) P R
    have h0 : eval₂ (evalHom (line α β)) P R = zero := hroot
    rw [h0, RingHom.map_zero] at h
    exact (eval₂_congr _ _ (fun q => jet_gen α β q) _ R).trans h.symm

/-- **`[CWYZ26]` Claim 4.9, covering part.** Let `P` be a simple root of `R` on the line
    `Y = α + βX`. At the jet `(y, v, z) = (α + βT₀, β, P(T₀)) ∈ F(T₀)³`, the cleared
    reconstruction coefficients evaluate to `s^(2d-1)` times the Taylor coefficients of `P` at
    `T₀`, for `j ≤ d`, where `s = ∂_Z R(T₀, y, z) ≠ 0`. So the triple `(α, β, P)` is the image
    of its jet under a map with numerators of degree at most `2·d·h` (`deg_reconCoeff_le`) on
    the surface `R(T₀, Y, Z) = 0`. -/
theorem jet_cover (R : Poly3 F) (α β : F) (P : UPoly F) (d : Nat) (hd : 1 ≤ d)
    (hroot : evalAffineLine R α β P = zero)
    (hsep : evalAffineLine (hasseZ 1 R) α β P ≠ zero) (j : Nat) (hj : j ≤ d) :
    (ptHom ((Frac.of (D := UPoly F)).toFun (line α β)) (scalK.toFun β)
      ((Frac.of (D := UPoly F)).toFun P)).toFun (reconCoeff (baseK.toFun R) genPt d j) =
      mul (CRing.npow ((Frac.of (D := UPoly F)).toFun (evalAffineLine (hasseZ 1 R) α β P))
        (2 * d - 1))
        (coeffAt ((taylorShift genPt).toFun ((mapHom scalK).toFun P)).coeffs j) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := jet_hyps R α β P hroot hsep
  have key := reconCoeff_spec (baseK.toFun R) genPt _ (scalK.toFun β) _ (genSeries P) d hd h1 h2
    (by rw [h3]; exact h4) (fun k _ => by rw [h5, coeffs_zero, coeffAt_nil]) j hj
  have hadd : add (C ((Frac.of (D := UPoly F)).toFun P)) (genSeries P) =
      (taylorShift genPt).toFun ((mapHom scalK).toFun P) := by
    show add _ (sub _ _) = _
    constructive_ring
  rw [h3, hadd] at key
  exact key

end Generic
end Poly3


section
variable {F : Type} [LawfulField F] [DecidableEq F]
theorem eval_ofList (l : List F) (z : F) : (ofList l).eval z = evalCoeffs l z := by
  rw [eval_eq]
  show evalCoeffs (trimPoly l) z = _
  rw [evalCoeffs_trimPoly]

theorem natDeg_ofList_le (l : List F) : (ofList l).natDeg ≤ l.length - 1 := by
  have := trimPoly_length_le l
  show (trimPoly l).length - 1 ≤ l.length - 1
  omega

end
end Qsag

namespace Qsag
open CommRingOps
namespace Poly3
variable {F : Type} [LawfulField F] [DecidableEq F]
theorem scalK_apply (x : F) : (scalK (F := F)).toFun x = (Frac.of (D := UPoly F)).toFun (UPoly.C x) := by unfold scalK; rfl
theorem baseK_apply (q : Poly3 F) : (baseK (F := F)).toFun q = (UPoly.mapHom (UPoly.mapHom (UPoly.mapHom scalK))).toFun q := by unfold baseK; rfl
theorem genPt_eq : (genPt : RatFunc F) = (Frac.of (D := UPoly F)).toFun UPoly.X := by unfold genPt; rfl
theorem ptHom_apply (x y z : F) (q : Poly3 F) : (ptHom x y z).toFun q = UPoly.eval₂ (UPoly.eval₂Hom (UPoly.evalHom x) y) z q := by unfold ptHom; rfl
theorem evalAffineLine_zero (α β : F) (p : UPoly F) : evalAffineLine zero α β p = zero := (affineLineHom α β p).map_zero
end Poly3
end Qsag

-- Owning-module audit certificates for theorems audited and paired in `Tests/MathAndCoding`.
#verify_constructive
  Qsag.Hensel.map_num
  Qsag.Hensel.num_spec
  Qsag.Poly3.deg_evalAffineLine_le
  Qsag.Poly3.henselNum_spec
  Qsag.Poly3.jet_cover
  Qsag.Poly3.root_unique_of_jet
  Qsag.UPoly.hasse_one_hasse
  Qsag.UPoly.trunc_cancel
  Qsag.Hensel.delta_num_le
  Qsag.Poly3.deg_henselNum_le
  Qsag.Poly3.inPow_affine_of_cons
  Qsag.Poly3.jet_hyps
  Qsag.UPoly.coeffAt_taylorShift
  Qsag.UPoly.hensel_unique
  Qsag.Hensel.evG_eq
  Qsag.Hensel.phi_contract
  Qsag.UPoly.eval_hasse
  Qsag.UPoly.eval_taylorShift
  Qsag.UPoly.mapHom_hasse
  Qsag.UPoly.taylorShift_neg_cancel
  Qsag.Poly3.deg_reconCoeff_le
  Qsag.Poly3.reconCoeff_spec
  Qsag.Poly3.unshift_shift

-- Kernel-checked defining equations for the executed controls in `Tests/MathAndCoding` (no body is exposed).
#export_eqns Qsag.Hensel.num
#export_eqns Qsag.Hensel.iter
#export_eqns Qsag.Hensel.phi
#export_eqns Qsag.Hensel.sep
#export_eqns Qsag.Hensel.e12
#export_eqns Qsag.Hensel.evW
#export_eqns Qsag.UPoly.shiftDown
#export_eqns Qsag.Hensel.e2
#export_eqns Qsag.Hensel.e11
#export_eqns Qsag.Hensel.evG
#export_eqns Qsag.Poly3.henselNum
#export_eqns Qsag.Poly3.henselG
#export_eqns Qsag.Poly3.liftXY
#export_eqns Qsag.Poly3.jetV
#export_eqns Qsag.Poly3.liftX
#export_eqns Qsag.Poly3.C3
#export_eqns Qsag.Poly3.c3Hom
#export_eqns Qsag.Poly3.jetY
#export_eqns Qsag.Poly3.shiftHom
#export_eqns Qsag.Poly3.yLine
#export_eqns Qsag.UPoly.taylorShift
#export_eqns Qsag.Poly3.triples
#export_eqns Qsag.rows
#export_eqns Qsag.Poly3.cons
#export_eqns Qsag.Poly3.coeff3
#export_eqns Qsag.Poly3.comb
#export_eqns Qsag.Poly3.hasseZ
#export_eqns Qsag.UPoly.hasse
#export_eqns Qsag.Poly3.eval3
#export_eqns Qsag.Poly3.ptHom
#export_eqns Qsag.Poly3.triCount
#export_eqns Qsag.Poly3.jetHom
#export_eqns Qsag.Poly3.evalAffineLine
#export_eqns Qsag.Poly3.affineLineHom
#export_eqns Qsag.Poly3.degZ
#export_eqns Qsag.Poly3.henselSep
#export_eqns Qsag.Hensel.res
