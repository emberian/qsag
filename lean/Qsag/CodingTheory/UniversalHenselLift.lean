module
/-
# Qsag.CodingTheory.UniversalHenselLift — uniqueness of Hensel lifts at simple roots

The uniqueness half of `[CWYZ26]` Lemma 3.11, and the injectivity it gives in Claim 4.9.

* `UPoly.trunc_cancel`: in `K[W]`, a factor with nonzero constant term can be cancelled
  modulo `W^n`.
* `UPoly.hensel_unique`: two truncated power series with the same constant term `z₀` that
  both solve `G(W, E(W)) ≡ 0 (mod W^n)` agree modulo `W^n`, provided `z₀` is a simple root of
  `G(0, U)`.
* `Poly3.root_unique_of_jet`: if `R(X, α + βX, P(X)) = 0 = R(X, α + βX, P'(X))`,
  `P(t₀) = P'(t₀) = z` and the separant `∂_Z R(t₀, α + βt₀, z)` is nonzero, then `P = P'`.
  So a root on a line is determined by the jet `(α + βt₀, β, P(t₀))`.

* `Poly3.henselNum`, `Poly3.deg_henselNum_le`, `Poly3.henselNum_spec`: the cleared numerators
  `N_j(Y, V, Z)` of `[CWYZ26]` Lemma 3.11 for `G = R(t₀ + W, Y + V·W, Z + U)`, with
  `deg N_j ≤ 1 + (2j - 1)(h - 1)` and `s·N_j(y, v, z) = (s²)^j·e_j` at every simple root.
* `Poly3.reconCoeff`, `Poly3.deg_reconCoeff_le`, `Poly3.reconCoeff_spec`: the reconstruction
  map of Claim 4.9, coefficientwise in the basis `(X - t₀)^j`, of degree at most `2·d·h` over
  the common denominator `s^(2d-1)`.
-/

public import Qsag.CodingTheory.HenselNumerators
import all Qsag.CodingTheory.PolyMv3
import all Qsag.CodingTheory.DynamicGcdSplit
import all Qsag.CodingTheory.HenselNumerators
import all Qsag.AffineProximityGaps
import all Qsag.Goldilocks

public section
namespace Qsag

set_option autoImplicit false

open CommRingOps RoundPoly

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

theorem hasse_zero {R : Type} [LawfulCommRing R] [DecidableEq R] (p : UPoly R) :
    hasse 0 p = p := by
  show gsUniHasse (p.coeffs.map C) 0 X = p
  rw [gsUniHasse_zero_eq_evalCoeffs]
  exact evalCoeffs_C_X p

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

namespace Poly3.HenselTests
open UPoly Poly3

def g (n : Nat) : Goldilocks := Goldilocks.ofNat n

/-- `R = Z² - Y`: on the line `Y = 1` the root `P = 1` has separant `2 ≠ 0`. -/
def rPar : Poly3 Goldilocks := ofList [ofList [zero, neg one], zero, one]

/-- `R = Z² - X²`, with the two roots `±X` crossing at `X = 0`. -/
def rCross : Poly3 Goldilocks := ofList [ofList [ofList [g 0, g 0, neg (g 1)]], zero, one]

/-- The hypotheses of `root_unique_of_jet` are jointly satisfiable. -/
theorem inhabited_root_unique_of_jet :
    ∃ (R : Poly3 Goldilocks) (α β t₀ : Goldilocks) (P P' : UPoly Goldilocks),
      evalAffineLine R α β P = zero ∧ evalAffineLine R α β P' = zero ∧
      P.eval t₀ = P'.eval t₀ ∧
      ((hasseZ 1 R).evalAffineLine α β (C (P.eval t₀))).eval t₀ ≠ zero :=
  ⟨rPar, g 1, g 0, g 0, one, one, (by decide +kernel), (by decide +kernel), rfl,
    (by decide +kernel)⟩

/-- The separant condition is needed: `X` and `-X` are distinct roots of `Z² - X²` with the
    same value at `t₀ = 0`, where the separant `2Z` vanishes. -/
theorem tooth_root_unique_needs_separant :
    ∃ (R : Poly3 Goldilocks) (α β t₀ : Goldilocks) (P P' : UPoly Goldilocks),
      evalAffineLine R α β P = zero ∧ evalAffineLine R α β P' = zero ∧
      P.eval t₀ = P'.eval t₀ ∧ P ≠ P' :=
  ⟨rCross, g 0, g 0, g 0, ofList [g 0, g 1], ofList [g 0, neg (g 1)], (by decide +kernel),
    (by decide +kernel), (by decide +kernel), (by decide +kernel)⟩

/-- For `R = Z² - Y` the first numerator is `N₁ = V` and the separant is `2Z`:
    `c₁ = V / (2Z)`, the derivative of `√Y` along `Y + V·W`. -/
theorem henselNum_parabola :
    henselNum rPar (g 0) 1 = jetV ∧ henselSep rPar (g 0) = mul (C3 (g 2)) X := by
  decide +kernel

/-- The hypotheses of `henselNum_spec` hold together: `R = Z² - Y` at the jet
    `(y, v, z) = (1, 1, 1)` with the first-order root `e = W/2` of `(1 + e)² = 1 + W`. -/
theorem inhabited_henselNum_spec :
    ∃ (R : Poly3 Goldilocks) (t₀ y v z : Goldilocks) (e : UPoly Goldilocks) (n : Nat),
      e.eval zero = zero ∧ eval3 R t₀ y z = zero ∧ eval3 (hasseZ 1 R) t₀ y z ≠ zero ∧
      (∀ k, k ≤ n → coeffAt (eval₂ (jetHom t₀ y v) (add (C z) e) R).coeffs k = zero) :=
  ⟨rPar, g 0, g 1, g 1, g 1, ofList [g 0, LawfulField.inv (g 2)], 1, by decide +kernel,
    by decide +kernel, by decide +kernel, fun k hk => by
      have hk' : k = 0 ∨ k = 1 := by omega
      rcases hk' with rfl | rfl <;> decide +kernel⟩

/-- The separant hypothesis of `henselNum_spec` is needed: `R = Z² - X²` at the origin has
    the root `e = W` with vanishing separant, and its first numerator `0` does not see it. -/
theorem tooth_henselNum_needs_separant :
    ∃ (R : Poly3 Goldilocks) (t₀ y v z : Goldilocks) (e : UPoly Goldilocks),
      e.eval zero = zero ∧ eval3 R t₀ y z = zero ∧
      eval₂ (jetHom t₀ y v) (add (C z) e) R = zero ∧
      (ptHom y v z).toFun (henselNum R t₀ 1) ≠ coeffAt e.coeffs 1 :=
  ⟨rCross, g 0, g 0, g 0, g 0, X, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

#verify_constructive henselNum_spec deg_henselNum_le reconCoeff_spec deg_reconCoeff_le
#verify_constructive henselNum_parabola tooth_henselNum_needs_separant
#tooth_pair henselNum_spec vs tooth_henselNum_needs_separant
#verify_inhabited henselNum_spec inhabited_henselNum_spec
#verify_constructive UPoly.trunc_cancel UPoly.hensel_unique UPoly.taylorShift_neg_cancel
#verify_constructive root_unique_of_jet
#tooth_pair root_unique_of_jet vs tooth_root_unique_needs_separant
#verify_inhabited root_unique_of_jet inhabited_root_unique_of_jet

end Poly3.HenselTests

end Qsag
end
