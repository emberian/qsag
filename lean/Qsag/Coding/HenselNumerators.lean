module
/-
# Qsag.Coding.HenselNumerators — cleared numerators of a Hensel lift, without division

Let `G ∈ Λ[W][U]` with `S := [W⁰U¹] G` (the separant). A root series `E(W) = Σ_{j≥1} c_j W^j`
of `G(W, E) = 0` has `c_j = N_j / S^(2j-1)` (`[CWYZ26]` Lemma 3.11). Substituting `W = S²·W'`
and `E = S·N(W')` turns the equation into the polynomial fixed-point equation `N = Φ(N)`:

  `G(S²W', S·N) = [W⁰U⁰]G + S²·(N - Φ(N))`            (`evG_eq`)

with `Φ` built from the tails of `G` and no division. `Φ` is a contraction for the `W'`-adic
filtration (`phi_contract`), so the iterates `iter G k = Φ^k(0)` stabilize and
`num G j := [W'^j] iter G j` is the numerator `N_j`.

* `num_spec`: over a field, for any `e` with `e(0) = 0` and `G(W, e(W)) ≡ 0 (mod W^(n+1))`,
  `S·N_j = S^(2j)·e_j` for `j ≤ n`.
* `delta_num_le`: if `δ([W^a U^b]G) + b ≤ h' + 1` for a degree function `δ`, then
  `δ(N_j) + h' ≤ 2·h'·j + 1`, which is the bound `1 + (2j - 1)(h - 1)` with `h = h' + 1`.
* `map_iter`: the construction commutes with base change of the coefficients.

The file also holds the small polynomial and ideal-power lemmas the Hensel files share.
-/

public import Qsag.Coding.DynamicGcdSplit
import all Qsag.Coding.PolyMv3
import all Qsag.Coding.DynamicGcdSplit
import all Qsag.Coding.AffineProximityGaps
import all Qsag.Math.Goldilocks

public section
namespace Qsag

set_option autoImplicit false

open CommRingOps RoundPoly

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

theorem mapHom_X {S : Type} [LawfulCommRing S] [DecidableEq S] (φ : RingHom R S) :
    (mapHom φ).toFun X = X := eval₂_X _ _

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
  have hC : ∀ q, (evG G N).toFun (C q) = (evW G).toFun q := fun q => eval₂_C _ _ _
  have hX : (evG G N).toFun X = mul (C (sep G)) N := eval₂_X _ _
  have hWC : ∀ a, (evW G).toFun (C a) = C a := fun a => eval₂_C _ _ _
  have hWX : (evW G).toFun X = mul (C (mul (sep G) (sep G))) X := eval₂_X _ _
  have h1 : coeffAt (shiftDown G).coeffs 0 = coeffAt G.coeffs 1 := coeffAt_shiftDown G 0
  have hSS : C (mul (sep G) (sep G)) = mul (C (sep G)) (C (sep G)) := CHom.map_mul _ _
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
        eval₂_X _ _]
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
  show (mapHom π).toFun (eval₂ CHom (mul (C (mul (sep G) (sep G))) X) q) =
    eval₂ CHom (mul (C (mul (sep ((mapHom (mapHom π)).toFun G))
      (sep ((mapHom (mapHom π)).toFun G)))) X) ((mapHom π).toFun q)
  rw [hom_eval₂, eval₂_mapHom, RingHom.map_mul, mapHom_C, mapHom_X, π.map_mul, map_sep]
  exact eval₂_congr _ _ (fun c => mapHom_C π c) _ q

theorem map_evG (π : RingHom Λ Γ) (G : UPoly (UPoly Λ)) (N : UPoly Λ) (p : UPoly (UPoly Λ)) :
    (mapHom π).toFun ((evG G N).toFun p) =
      (evG ((mapHom (mapHom π)).toFun G) ((mapHom π).toFun N)).toFun
        ((mapHom (mapHom π)).toFun p) := by
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

namespace Hensel.Tests
open UPoly Hensel

def g (n : Nat) : Goldilocks := Goldilocks.ofNat n

/-- `G(W, U) = (1 + U)² - (1 + W)`: the root series is `√(1 + W) - 1 = W/2 - W²/8 + …`. -/
def gSqrt : UPoly (UPoly Goldilocks) :=
  ofList [ofList [g 0, neg (g 1)], ofList [g 2], ofList [g 1]]

/-- The numerators of `√(1 + W) - 1`: `N₁ = 1`, `N₂ = -1`, with separant `2`, so
    `c₁ = 1/2` and `c₂ = -1/2³`. -/
theorem num_sqrt : sep gSqrt = g 2 ∧ num gSqrt 1 = g 1 ∧ num gSqrt 2 = neg (g 1) := by
  decide +kernel

/-- The hypotheses of `num_spec` hold for `G = (1 + U)² - (1 + W)` and the truncation
    `e = W/2` of its root, to first order. -/
theorem inhabited_num_spec :
    ∃ (G : UPoly (UPoly Goldilocks)) (e : UPoly Goldilocks) (n : Nat), e.eval zero = zero ∧
      res G = zero ∧ sep G ≠ zero ∧
      (∀ k, k ≤ n → coeffAt (G.eval e).coeffs k = zero) :=
  ⟨gSqrt, ofList [g 0, LawfulField.inv (g 2)], 1, by decide +kernel, by decide +kernel,
    by decide +kernel, fun k hk => by
      have hk' : k = 0 ∨ k = 1 := by omega
      rcases hk' with rfl | rfl <;> decide +kernel⟩

/-- The separant hypothesis is needed: `G = U² - W²` has the root `e = W` with residue and
    separant both zero, and the conclusion `s·N₁ = s²·e₁` degenerates to `0 = 0` while the
    numerator carries no information: `N₁ = 0 ≠ e₁`. -/
theorem tooth_num_needs_separant :
    ∃ (G : UPoly (UPoly Goldilocks)) (e : UPoly Goldilocks), res G = zero ∧
      coeffAt e.coeffs 0 = zero ∧ G.eval e = zero ∧ num G 1 ≠ coeffAt e.coeffs 1 :=
  ⟨ofList [ofList [g 0, g 0, neg (g 1)], zero, one], X, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

#verify_constructive Hensel.num_spec Hensel.delta_num_le Hensel.phi_contract Hensel.evG_eq
#verify_constructive Hensel.map_num num_sqrt tooth_num_needs_separant
#tooth_pair Hensel.num_spec vs tooth_num_needs_separant
#verify_inhabited Hensel.num_spec inhabited_num_spec

end Hensel.Tests

end Qsag
end
