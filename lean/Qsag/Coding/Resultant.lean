module
public import Qsag.Math.Algebra
public import Qsag.Math.Goldilocks
public import Qsag.Tactic.Prelude

public section

section
namespace Qsag

set_option autoImplicit false

open CommRingOps RoundPoly UPoly

/-! ## Linear combinations in `K[Y][Z]` -/

/-- Bivariate polynomials `K[Y][Z]`. -/
abbrev Poly2 (K : Type) [LawfulCommRing K] [DecidableEq K] := UPoly (UPoly K)

namespace Poly2
variable {K : Type} [LawfulField K] [DecidableEq K]

/-- Coefficient of `Y^i Z^k`. -/
def coeff2 (P : Poly2 K) (i k : Nat) : K := coeffAt (coeffAt P.coeffs k).coeffs i

/-- Total degree in `(Y, Z)`. -/
@[expose] def tdeg (P : Poly2 K) : Nat := P.wdeg UPoly.natDeg 1

/-- Evaluation at a point `(y, z)`. -/
@[expose] def eval2 (P : Poly2 K) (y z : K) : K := UPoly.eval₂ (UPoly.evalHom y) z P

theorem coeff2_add (P Q : Poly2 K) (i k : Nat) :
    coeff2 (add P Q) i k = add (coeff2 P i k) (coeff2 Q i k) := by
  show coeffAt (coeffAt (add P Q).coeffs k).coeffs i = _
  rw [coeffAt_add, coeffAt_add]; rfl

theorem coeff2_scale (x : K) (P : Poly2 K) (i k : Nat) :
    coeff2 (mul (C (C x)) P) i k = mul x (coeff2 P i k) := by
  show coeffAt (coeffAt (mul (C (C x)) P).coeffs k).coeffs i = _
  rw [coeffAt_C_mul, coeffAt_C_mul]; rfl

theorem coeff2_zero (i k : Nat) : coeff2 (zero : Poly2 K) i k = zero := by
  show coeffAt (coeffAt (zero : Poly2 K).coeffs k).coeffs i = zero
  rw [coeffs_zero, coeffAt_nil, coeffs_zero, coeffAt_nil]

/-- `Σ_t x_t · g_t`. -/
def lincomb : List K → List (Poly2 K) → Poly2 K
  | x :: xs, g :: gs => add (mul (C (C x)) g) (lincomb xs gs)
  | [], _ => zero
  | _ :: _, [] => zero

theorem coeff2_lincomb (i k : Nat) : ∀ (xs : List K) (gs : List (Poly2 K)),
    coeff2 (lincomb xs gs) i k = dotVec (gs.map (fun g => coeff2 g i k)) xs
  | [], gs => by
    show coeff2 zero i k = _
    rw [coeff2_zero, dotVec_nil_right]
  | _ :: _, [] => by simpa only [lincomb, List.map_nil, dotVec_nil_left] using coeff2_zero (K := K) i k
  | x :: xs, g :: gs => by
    simp only [List.map_cons, dotVec_cons]
    show coeff2 (add (mul (C (C x)) g) (lincomb xs gs)) i k =
      add (mul (coeff2 g i k) x) (dotVec (gs.map (fun g => coeff2 g i k)) xs)
    rw [coeff2_add, coeff2_scale, coeff2_lincomb i k xs gs, LawfulCommRing.mul_comm]

theorem lincomb_map_mul {α : Type} (f : α → Poly2 K) (A : Poly2 K) :
    ∀ (ps : List α) (xs : List K),
      lincomb xs (ps.map (fun p => mul (f p) A)) = mul (lincomb xs (ps.map f)) A
  | _, [] => (LawfulCommRing.zero_mul A).symm
  | [], _ :: _ => (LawfulCommRing.zero_mul A).symm
  | p :: ps, x :: xs => by
    show add (mul (C (C x)) (mul (f p) A)) (lincomb xs (ps.map (fun p => mul (f p) A))) =
      mul (add (mul (C (C x)) (f p)) (lincomb xs (ps.map f))) A
    rw [lincomb_map_mul f A ps xs]
    constructive_ring

theorem lincomb_append : ∀ (xs ys : List K) (gs hs : List (Poly2 K)), xs.length = gs.length →
    lincomb (xs ++ ys) (gs ++ hs) = add (lincomb xs gs) (lincomb ys hs)
  | [], ys, [], hs, _ => (LawfulCommRing.zero_add _).symm
  | x :: xs, ys, g :: gs, hs, h => by
    show add (mul (C (C x)) g) (lincomb (xs ++ ys) (gs ++ hs)) =
      add (add (mul (C (C x)) g) (lincomb xs gs)) (lincomb ys hs)
    rw [lincomb_append xs ys gs hs (by simpa using h), LawfulCommRing.add_assoc]

theorem degFn_lincomb_le {δ : Poly2 K → Nat} (hδ : DegFn δ) (hC : ∀ x : K, δ (C (C x)) = 0)
    (B : Nat) : ∀ (xs : List K) (gs : List (Poly2 K)), (∀ g ∈ gs, δ g ≤ B) →
      δ (lincomb xs gs) ≤ B
  | [], _, _ => by show δ zero ≤ B; rw [hδ.zero]; exact Nat.zero_le _
  | _ :: _, [], _ => by show δ zero ≤ B; rw [hδ.zero]; exact Nat.zero_le _
  | x :: xs, g :: gs, h => by
    show δ (add (mul (C (C x)) g) (lincomb xs gs)) ≤ B
    have h1 := hδ.add_le (mul (C (C x)) g) (lincomb xs gs)
    have h2 := hδ.mul_le (C (C x)) g
    have h3 := h g (.head _)
    have h4 := degFn_lincomb_le hδ hC B xs gs (fun g' hg' => h g' (.tail _ hg'))
    rw [hC x] at h2
    omega

/-- A nonzero coefficient vector whose combination vanishes at the index pairs `J`. -/
def nullVec (gs : List (Poly2 K)) (J : List (Nat × Nat)) : List K :=
  solveHomogeneous gs.length (J.map (fun p => gs.map (fun g => coeff2 g p.1 p.2)))

theorem nullVec_spec (gs : List (Poly2 K)) (J : List (Nat × Nat)) (h : J.length < gs.length) :
    (nullVec gs J).length = gs.length ∧ (∃ c ∈ nullVec gs J, c ≠ zero) ∧
      ∀ p ∈ J, coeff2 (lincomb (nullVec gs J) gs) p.1 p.2 = zero := by
  obtain ⟨h1, h2, h3⟩ := gauss_nullspace_witness gs.length
    (J.map (fun p => gs.map (fun g => coeff2 g p.1 p.2))) (by rw [List.length_map]; exact h)
    (fun row hrow => by
      obtain ⟨p, _, rfl⟩ := List.mem_map.mp hrow
      exact List.length_map _)
  refine ⟨h1, ?_, fun p hp => ?_⟩
  · obtain ⟨c, hc, hne⟩ := List.any_eq_true.mp h2
    exact ⟨c, hc, fun e => by simp [e] at hne⟩
  · rw [coeff2_lincomb]
    exact h3 _ (List.mem_map.mpr ⟨p, hp, rfl⟩)

/-! ## Monomials -/

/-- `Y^i Z^j`. -/
def mono (i j : Nat) : Poly2 K := ofList (monomial j (ofList (monomial i one)))

theorem coeffAt_mono (i j k : Nat) :
    coeffAt (mono (K := K) i j).coeffs k = if k = j then ofList (monomial i one) else zero := by
  show coeffAt (ofList _).coeffs k = _
  rw [coeffAt_ofList, coeffAt_monomial]

private theorem natDeg_xpow_le (i : Nat) : (ofList (monomial i (one : K))).natDeg ≤ i :=
  natDeg_le_of_coeffAt _ i (fun k hk => by
    have hne : ¬ k = i := by omega
    rw [coeffAt_ofList, coeffAt_monomial]; simp only [hne, ↓reduceIte])

theorem natDeg_mono_le (i j : Nat) : (mono (K := K) i j).natDeg ≤ j :=
  natDeg_le_of_coeffAt _ j (fun k hk => by
    have hne : ¬ k = j := by omega
    rw [coeffAt_mono]; simp only [hne, ↓reduceIte])

theorem tdeg_mono_le (i j : Nat) : tdeg (mono (K := K) i j) ≤ i + j := by
  apply wdeg_le
  intro k hk
  rw [coeffAt_mono] at hk ⊢
  if hkj : k = j then
    subst hkj
    simp only [↓reduceIte] at hk ⊢
    have := natDeg_xpow_le (K := K) i
    omega
  else
    simp only [hkj, ↓reduceIte] at hk
    exact absurd rfl hk

theorem coeff2_mono_self (i j : Nat) : coeff2 (mono (K := K) i j) i j = one := by
  show coeffAt (coeffAt (mono (K := K) i j).coeffs j).coeffs i = one
  rw [coeffAt_mono]; simp only [↓reduceIte]
  rw [coeffAt_ofList, coeffAt_monomial]; simp only [↓reduceIte]

theorem coeff2_mono_ne (i j i' j' : Nat) (h : (i', j') ≠ (i, j)) :
    coeff2 (mono (K := K) i j) i' j' = zero := by
  show coeffAt (coeffAt (mono (K := K) i j).coeffs j').coeffs i' = zero
  rw [coeffAt_mono]
  if hj : j' = j then
    subst hj
    have hi : ¬ i' = i := fun e => h (by rw [e])
    simp only [↓reduceIte]
    rw [coeffAt_ofList, coeffAt_monomial]; simp only [hi, ↓reduceIte]
  else
    simp only [hj, ↓reduceIte]
    rw [coeffs_zero, coeffAt_nil]

omit [DecidableEq K] in
theorem dotVec_zero_left : ∀ (row xs : List K), (∀ r ∈ row, r = zero) →
    dotVec row xs = zero
  | [], _, _ => dotVec_nil_left _
  | _ :: _, [], _ => dotVec_nil_right _
  | r :: row, x :: xs, h => by
    rw [dotVec_cons]
    show add (mul r x) (dotVec row xs) = zero
    rw [h r (.head _), dotVec_zero_left row xs (fun r' hr' => h r' (.tail _ hr')),
      LawfulCommRing.zero_mul, LawfulCommRing.add_zero]

/-- Distinct monomials are linearly independent. -/
theorem eq_zero_of_lincomb_mono : ∀ (ps : List (Nat × Nat)) (xs : List K), ps.Nodup →
    xs.length = ps.length →
    (∀ i j, dotVec ((ps.map (fun p => mono (K := K) p.1 p.2)).map (fun g => coeff2 g i j)) xs
      = zero) → ∀ c ∈ xs, c = zero
  | [], [], _, _, _, c, hc => by cases hc
  | [], _ :: _, _, hl, _, _, _ => by cases hl
  | _ :: _, [], _, hl, _, _, _ => by cases hl
  | p :: ps, x :: xs, hnd, hl, h, c, hc => by
    have hp := List.pairwise_cons.mp hnd
    have hx : x = zero := by
      have h0 := h p.1 p.2
      have hz : dotVec ((ps.map (fun q => mono (K := K) q.1 q.2)).map
          (fun g => coeff2 g p.1 p.2)) xs = zero := by
        apply dotVec_zero_left
        intro r hr
        obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hr
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
        exact coeff2_mono_ne q.1 q.2 p.1 p.2 (fun e => hp.1 q hq e)
      have h1 : add (mul (coeff2 (mono (K := K) p.1 p.2) p.1 p.2) x)
          (dotVec ((ps.map (fun q => mono (K := K) q.1 q.2)).map
            (fun g => coeff2 g p.1 p.2)) xs) = zero := by simpa only [List.map_cons, dotVec_cons] using h0
      rw [hz, coeff2_mono_self, LawfulCommRing.one_mul, LawfulCommRing.add_zero] at h1
      exact h1
    cases hc with
    | head => exact hx
    | tail _ hc' =>
      refine eq_zero_of_lincomb_mono ps xs hp.2 (by simpa using hl) (fun i j => ?_) c hc'
      have h1 : add (mul (coeff2 (mono (K := K) p.1 p.2) i j) x)
          (dotVec ((ps.map (fun q => mono (K := K) q.1 q.2)).map (fun g => coeff2 g i j)) xs)
          = zero := by simpa only [List.map_cons, dotVec_cons] using h i j
      rwa [hx, LawfulCommRing.mul_zero, LawfulCommRing.zero_add] at h1

theorem natDeg_C (c : UPoly K) : (C c).natDeg = 0 := by
  have := trimPoly_length_le [c]
  show (ofList [c]).coeffs.length - 1 = 0
  rw [coeffs_ofList]
  simp only [List.length_cons, List.length_nil] at this; omega

theorem tdeg_CC (x : K) : tdeg (C (C x) : Poly2 K) = 0 := by
  apply Nat.le_zero.mp
  apply wdeg_le
  intro k hk
  cases k with
  | zero =>
    rw [coeffAt_C_zero]
    have := trimPoly_length_le [x]
    show (ofList [x]).coeffs.length - 1 + 1 * 0 ≤ 0
    rw [coeffs_ofList]
    simp only [List.length_cons, List.length_nil] at this; omega
  | succ k => exact absurd (coeffAt_C_succ _ k) hk

theorem degFn_tdeg : DegFn (tdeg (K := K)) := UPoly.degFn_wdeg UPoly.degFn_natDeg 1

theorem natDeg_le_tdeg (P : Poly2 K) : P.natDeg ≤ tdeg P := by
  if h : P = zero then
    show P.coeffs.length - 1 ≤ _
    rw [h, coeffs_zero]; exact Nat.zero_le _
  else
    have := le_wdeg UPoly.natDeg 1 P P.natDeg (by simpa only [lead_eq] using (lead_ne_zero h))
    show P.natDeg ≤ P.wdeg UPoly.natDeg 1
    omega

theorem lincomb_nil (xs : List K) : lincomb xs ([] : List (Poly2 K)) = zero := by
  cases xs <;> rfl

/-! ## The eliminant -/

/-- One more unknown than equations: the dimension count behind the Sylvester matrix. -/
theorem elim_count (m n a b T : Nat) (hm : 1 ≤ m) (hnb : n ≤ b) (hT : T = n * a + m * (b - n)) :
    sumTo (fun j => T - j) (m + n - 1) <
      sumTo (fun j => T + 1 - a - j) n + sumTo (fun j => T + 1 - b - j) m := by
  have e : n + m = (m + n - 1) + 1 := by omega
  have hf : (fun j => T + 1 - (j + 1)) = (fun j => T - j) := funext (fun j => by omega)
  have h1 : sumTo (fun j => T + 1 - j) (n + m) = (T + 1) + sumTo (fun j => T - j) (m + n - 1) := by
    rw [e, sumTo_succ]
    show T + 1 - 0 + sumTo (fun j => T + 1 - (j + 1)) (m + n - 1) = _
    rw [hf]; omega
  have h2 : sumTo (fun j => T + 1 - j) (n + m) =
      sumTo (fun j => T + 1 - j) n + sumTo (fun j => T + 1 - (n + j)) m := sumTo_add _ n m
  have h3 := sumTo_le (fun j => T + 1 - j) (fun j => T + 1 - a - j) a n (fun j _ => by omega)
  have h4 := sumTo_le (fun j => T + 1 - (n + j)) (fun j => T + 1 - b - j) (b - n) m
    (fun j _ => by omega)
  omega

/-- Admissible cofactor monomials `Y^i Z^j`: `j < N` and `i + j + c ≤ T`. -/
def elimIdx (T c N : Nat) : List (Nat × Nat) := rows (fun j => T + 1 - c - j) N

/-- Constrained coefficients `Y^i Z^k`: `1 ≤ k ≤ N` and `i + k ≤ T`. -/
def elimCons (T N : Nat) : List (Nat × Nat) :=
  (rows (fun j => T - j) N).map (fun p => (p.1, p.2 + 1))

section Core
variable (A B : Poly2 K) (T m n a b : Nat)

/-- The monomial multiples of `A` and `B` spanning the search space. -/
def elimGens : List (Poly2 K) :=
  (elimIdx T a n).map (fun p => mul (mono p.1 p.2) A) ++
    (elimIdx T b m).map (fun p => mul (mono p.1 p.2) B)

/-- The solved coefficient vector. -/
def elimVec : List K := nullVec (elimGens A B T m n a b) (elimCons T (m + n - 1))

/-- The cofactor of `A`. -/
def elimU : Poly2 K :=
  lincomb ((elimVec A B T m n a b).take (elimIdx T a n).length)
    ((elimIdx T a n).map (fun p => mono p.1 p.2))

/-- The cofactor of `B`. -/
def elimV : Poly2 K :=
  lincomb ((elimVec A B T m n a b).drop (elimIdx T a n).length)
    ((elimIdx T b m).map (fun p => mono p.1 p.2))

theorem elim_spec (hT : T = n * a + m * (b - n)) (hmA : A.natDeg ≤ m) (hnB : B.natDeg ≤ n)
    (haA : tdeg A ≤ a) (hbB : tdeg B ≤ b) (hm : 1 ≤ m) (hnb : n ≤ b) :
    (∃ r : UPoly K, add (mul (elimU A B T m n a b) A) (mul (elimV A B T m n a b) B) = C r ∧
      r.natDeg ≤ T) ∧
    (elimU A B T m n a b ≠ zero → (elimU A B T m n a b).natDeg < n) ∧
    ¬ (elimU A B T m n a b = zero ∧ elimV A B T m n a b = zero) := by
  have hIdx : ∀ (c N : Nat) (p : Nat × Nat), p ∈ elimIdx T c N →
      p.2 < N ∧ p.1 + p.2 + c ≤ T := by
    intro c N p hp
    obtain ⟨i, j⟩ := p
    have h := (mem_rows (fun j => T + 1 - c - j) i j N).mp hp
    have h2 : i < T + 1 - c - j := h.2
    exact ⟨h.1, by omega⟩
  have hgens : ∀ g ∈ elimGens A B T m n a b, g.natDeg ≤ m + n - 1 ∧ tdeg g ≤ T := by
    intro g hg
    rcases List.mem_append.mp hg with h | h
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
      have h1 := hIdx a n p hp
      have h2 := natDeg_mul_le (mono (K := K) p.1 p.2) A
      have h3 := natDeg_mono_le (K := K) p.1 p.2
      have h4 := degFn_tdeg.mul_le (mono (K := K) p.1 p.2) A
      have h5 := tdeg_mono_le (K := K) p.1 p.2
      exact ⟨by omega, by omega⟩
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
      have h1 := hIdx b m p hp
      have h2 := natDeg_mul_le (mono (K := K) p.1 p.2) B
      have h3 := natDeg_mono_le (K := K) p.1 p.2
      have h4 := degFn_tdeg.mul_le (mono (K := K) p.1 p.2) B
      have h5 := tdeg_mono_le (K := K) p.1 p.2
      exact ⟨by omega, by omega⟩
  have hglen : (elimGens A B T m n a b).length =
      (elimIdx T a n).length + (elimIdx T b m).length := by
    unfold elimGens
    rw [List.length_append, List.length_map, List.length_map]
  have hcount : (elimCons T (m + n - 1)).length < (elimGens A B T m n a b).length := by
    rw [hglen]
    unfold elimCons elimIdx
    rw [List.length_map, length_rows, length_rows, length_rows]
    exact elim_count m n a b T hm hnb hT
  obtain ⟨hlen, hnz, hJ⟩ := nullVec_spec (elimGens A B T m n a b) (elimCons T (m + n - 1)) hcount
  have hlen' : (elimVec A B T m n a b).length =
      (elimIdx T a n).length + (elimIdx T b m).length := hlen.trans hglen
  have hsplit : lincomb (elimVec A B T m n a b) (elimGens A B T m n a b) =
      add (mul (elimU A B T m n a b) A) (mul (elimV A B T m n a b) B) := by
    unfold elimU elimV
    rw [← lincomb_map_mul, ← lincomb_map_mul,
      ← lincomb_append _ _ _ _ (by rw [List.length_take, List.length_map]; omega),
      List.take_append_drop]
    rfl
  have hWZ := degFn_lincomb_le UPoly.degFn_natDeg (fun c : K => natDeg_C (C c)) (m + n - 1)
    (elimVec A B T m n a b) _ (fun g hg => (hgens g hg).1)
  have hWT := degFn_lincomb_le degFn_tdeg tdeg_CC T (elimVec A B T m n a b) _
    (fun g hg => (hgens g hg).2)
  have hJ' : ∀ p ∈ elimCons T (m + n - 1),
      coeff2 (lincomb (elimVec A B T m n a b) (elimGens A B T m n a b)) p.1 p.2 = zero := hJ
  rw [hsplit] at hWZ hWT hJ'
  refine ⟨?_, ?_, ?_⟩
  · generalize add (mul (elimU A B T m n a b) A) (mul (elimV A B T m n a b) B) = W
      at hWZ hWT hJ' ⊢
    have hWT' : W.wdeg UPoly.natDeg 1 ≤ T := hWT
    have hvan : ∀ i k, coeffAt (coeffAt W.coeffs (k + 1)).coeffs i = zero := by
      intro i k
      if hk : k + 1 ≤ m + n - 1 then
        if hik : i + (k + 1) ≤ T then
          exact hJ' (i, k + 1) (List.mem_map.mpr
            ⟨(i, k), (mem_rows _ i k _).mpr ⟨by omega, by show i < T - k; omega⟩, rfl⟩)
        else
          if hq : coeffAt W.coeffs (k + 1) = zero then rw [hq, coeffs_zero, coeffAt_nil]
          else
            have := le_wdeg UPoly.natDeg 1 W (k + 1) hq
            exact coeffAt_eq_zero_of_natDeg_lt _ (by omega)
      else
        rw [W.coeffAt_eq_zero_of_natDeg_lt (by omega), coeffs_zero, coeffAt_nil]
    refine ⟨coeffAt W.coeffs 0, ?_, ?_⟩
    · apply ext_coeffAt; intro k
      cases k with
      | zero => rw [coeffAt_C_zero]
      | succ k =>
        rw [coeffAt_C_succ]
        exact ext_coeffAt (fun i => by rw [hvan i k, coeffs_zero, coeffAt_nil])
    · if hr : coeffAt W.coeffs 0 = zero then
        rw [hr]; show (zero : UPoly K).coeffs.length - 1 ≤ T
        rw [coeffs_zero]; exact Nat.zero_le _
      else
        have := le_wdeg UPoly.natDeg 1 W 0 hr
        omega
  · intro hu
    if hn : n = 0 then
      subst hn
      exfalso
      apply hu
      simp only [elimU, elimIdx, rows_zero, List.map_nil, lincomb_nil]
    else
      have h : (elimU A B T m n a b).natDeg ≤ n - 1 :=
        degFn_lincomb_le UPoly.degFn_natDeg (fun c : K => natDeg_C (C c)) (n - 1) _ _
          (fun g hg => by
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
            have := (hIdx a n p hp).1
            have := natDeg_mono_le (K := K) p.1 p.2
            omega)
      omega
  · rintro ⟨hu0, hv0⟩
    have hUz := eq_zero_of_lincomb_mono (elimIdx T a n)
      ((elimVec A B T m n a b).take (elimIdx T a n).length) (nodup_rows _ _)
      (by rw [List.length_take]; omega)
      (fun i j => by
        rw [← coeff2_lincomb]
        show coeff2 (elimU A B T m n a b) i j = zero
        rw [hu0, coeff2_zero])
    have hVz := eq_zero_of_lincomb_mono (elimIdx T b m)
      ((elimVec A B T m n a b).drop (elimIdx T a n).length) (nodup_rows _ _)
      (by rw [List.length_drop]; omega)
      (fun i j => by
        rw [← coeff2_lincomb]
        show coeff2 (elimV A B T m n a b) i j = zero
        rw [hv0, coeff2_zero])
    obtain ⟨c, hc, hne⟩ := hnz
    have hc' : c ∈ (elimVec A B T m n a b).take (elimIdx T a n).length ++
        (elimVec A B T m n a b).drop (elimIdx T a n).length := by
      rw [List.take_append_drop]; exact hc
    rcases List.mem_append.mp hc' with h | h
    · exact hne (hUz c h)
    · exact hne (hVz c h)

end Core

local instance : NoZeroDivisors K := LawfulField.toNoZeroDivisors K

/-- The degree budget of the eliminant; at most `tdeg A * tdeg B`. -/
def elimDeg (A B : Poly2 K) : Nat := B.natDeg * tdeg A + A.natDeg * (tdeg B - B.natDeg)

/-- `eliminant A B = (u, v, r)` with `u·A + v·B = r ∈ K[Y]`. -/
def eliminant (A B : Poly2 K) : Poly2 K × Poly2 K × UPoly K :=
  let u := elimU A B (elimDeg A B) A.natDeg B.natDeg (tdeg A) (tdeg B)
  let v := elimV A B (elimDeg A B) A.natDeg B.natDeg (tdeg A) (tdeg B)
  (u, v, coeffAt (add (mul u A) (mul v B)).coeffs 0)

/-- The eliminant of `Z`: a polynomial in `Y` lying in the ideal `(A, B)`. -/
def resZ (A B : Poly2 K) : UPoly K := (eliminant A B).2.2

theorem elimDeg_le (A B : Poly2 K) : elimDeg A B ≤ tdeg A * tdeg B := by
  have hm := natDeg_le_tdeg A
  have hn := natDeg_le_tdeg B
  calc B.natDeg * tdeg A + A.natDeg * (tdeg B - B.natDeg)
      ≤ B.natDeg * tdeg A + tdeg A * (tdeg B - B.natDeg) :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ hm) _
    _ = tdeg A * (B.natDeg + (tdeg B - B.natDeg)) := by rw [Nat.mul_add, Nat.mul_comm B.natDeg]
    _ = tdeg A * tdeg B := by rw [Nat.add_sub_cancel' hn]

private theorem eliminant_core (A B : Poly2 K) (hA : 1 ≤ A.natDeg) :
    add (mul (eliminant A B).1 A) (mul (eliminant A B).2.1 B) = C (resZ A B) ∧
      (resZ A B).natDeg ≤ elimDeg A B ∧
      ((eliminant A B).1 ≠ zero → (eliminant A B).1.natDeg < B.natDeg) ∧
      ¬ ((eliminant A B).1 = zero ∧ (eliminant A B).2.1 = zero) := by
  obtain ⟨⟨r, hr, hdeg⟩, h2, h3⟩ := elim_spec A B (elimDeg A B) A.natDeg B.natDeg (tdeg A)
    (tdeg B) rfl (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) hA
    (natDeg_le_tdeg B)
  have hres : resZ A B = r := by
    show coeffAt (add (mul (elimU A B _ _ _ _ _) A) (mul (elimV A B _ _ _ _ _) B)).coeffs 0 = r
    rw [hr, coeffAt_C_zero]
  exact ⟨by rw [hres]; exact hr, by rw [hres]; exact hdeg, h2, h3⟩

/-- **Bézout cofactor identity**: `u·A + v·B = resZ A B`, a polynomial free of `Z`. -/
theorem eliminant_bezout (A B : Poly2 K) (hA : 1 ≤ A.natDeg) :
    add (mul (eliminant A B).1 A) (mul (eliminant A B).2.1 B) = C (resZ A B) :=
  (eliminant_core A B hA).1

/-- **Degree bound**: `deg_Y (resZ A B) ≤ deg_{Y,Z} A · deg_{Y,Z} B`. -/
theorem natDeg_resZ_le (A B : Poly2 K) (hA : 1 ≤ A.natDeg) :
    (resZ A B).natDeg ≤ tdeg A * tdeg B :=
  Nat.le_trans (eliminant_core A B hA).2.1 (elimDeg_le A B)

theorem C_ne_zero {c : UPoly K} (h : c ≠ zero) : (C c : Poly2 K) ≠ zero := fun e => h (by
  have := congrArg (fun P : Poly2 K => coeffAt P.coeffs 0) e
  simp only [coeffAt_C_zero, coeffs_zero, coeffAt_nil] at this
  exact this)

/-- Coprimality over `K(Y)` with denominators cleared: some combination `u₀·A + v₀·B` is a
    nonzero polynomial in `Y` alone. -/
@[expose] def CoprimeZ (A B : Poly2 K) : Prop :=
  ∃ (u₀ v₀ : Poly2 K) (c : UPoly K), c ≠ zero ∧ add (mul u₀ A) (mul v₀ B) = C c

/-- **Nonvanishing**: the eliminant is nonzero exactly when `A` and `B` are coprime over
    `K(Y)`. -/
theorem resZ_ne_zero_iff (A B : Poly2 K) (hA : 1 ≤ A.natDeg) (hB : B ≠ zero) :
    resZ A B ≠ zero ↔ CoprimeZ A B := by
  obtain ⟨hbez, _, hdegU, hnontriv⟩ := eliminant_core A B hA
  refine ⟨fun h => ⟨_, _, _, h, hbez⟩, ?_⟩
  rintro ⟨u₀, v₀, c, hc, hcert⟩ hr
  generalize (eliminant A B).1 = u at hbez hdegU hnontriv
  generalize (eliminant A B).2.1 = v at hbez hnontriv
  have hC0 : (C (zero : UPoly K) : Poly2 K) = zero := by
    rw [← CHom_apply]; exact CHom.map_zero
  rw [hr, hC0] at hbez
  have hid : sub (mul (add (mul u₀ A) (mul v₀ B)) u) (mul B (sub (mul v₀ u) (mul u₀ v))) =
      mul u₀ (add (mul u A) (mul v B)) := by constructive_ring
  rw [hcert, hbez, LawfulCommRing.mul_zero] at hid
  have hdiv : mul (C c) u = mul B (sub (mul v₀ u) (mul u₀ v)) :=
    LawfulCommRing.sub_eq_zero_iff.mp hid
  have hu : u = zero := by
    apply Decidable.byContradiction
    intro hu
    have hCu : mul (C c) u ≠ zero := fun e =>
      (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero e).elim (C_ne_zero hc) hu
    have hw : sub (mul v₀ u) (mul u₀ v) ≠ zero := fun e => hCu (by
      rw [hdiv, e, LawfulCommRing.mul_zero])
    have h1 := natDeg_mul (C_ne_zero hc) hu
    have h2 := natDeg_mul hB hw
    rw [natDeg_C] at h1
    rw [hdiv] at h1
    have := hdegU hu
    omega
  rw [hu, LawfulCommRing.zero_mul, LawfulCommRing.zero_add] at hbez
  rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hbez with hv | hB0
  · exact hnontriv ⟨hu, hv⟩
  · exact hB hB0

/-- **Root projection**: a common zero `(y, z)` of `A` and `B` gives a root `y` of the
    eliminant. -/
theorem eval_resZ_eq_zero (A B : Poly2 K) (hA : 1 ≤ A.natDeg) (y z : K)
    (hAy : A.eval2 y z = zero) (hBy : B.eval2 y z = zero) : (resZ A B).eval y = zero := by
  have h := congrArg (UPoly.eval₂Hom (UPoly.evalHom y) z).toFun (eliminant_bezout A B hA)
  rw [RingHom.map_add, RingHom.map_mul, RingHom.map_mul] at h
  have e : ∀ P : Poly2 K, (UPoly.eval₂Hom (UPoly.evalHom y) z).toFun P = P.eval2 y z :=
    fun P => UPoly.eval₂Hom_apply _ _ P
  rw [e A, e B, hAy, hBy, LawfulCommRing.mul_zero, LawfulCommRing.mul_zero,
    LawfulCommRing.add_zero] at h
  have h' := h.symm
  rw [UPoly.eval₂Hom_apply, UPoly.eval₂_C, UPoly.evalHom_apply] at h'
  exact h'

theorem exists_ne_zero_of_ne_zero {p : UPoly K} (h : p ≠ zero) :
    ∃ c ∈ p.coeffs, c ≠ zero := by
  have hl := lead_ne_zero h
  have hlen : p.natDeg < p.coeffs.length := by
    have : p.coeffs ≠ [] := fun e => h ((eq_zero_iff p).mpr e)
    have := List.length_pos_iff.mpr this
    show p.coeffs.length - 1 < _; omega
  refine ⟨p.coeffs[p.natDeg], List.getElem_mem hlen, ?_⟩
  have : coeffAt p.coeffs p.natDeg = p.coeffs[p.natDeg] := by
    rw [coeffAt_eq_getD]
    simp [List.getD, hlen]
  rw [← this]; exact (by simpa only [lead_eq] using hl)

/-- **Bivariate Bézout bound, projected**: coprime `A, B` have at most
    `deg A · deg B` common zeros with pairwise distinct `Y`-coordinates. -/
theorem common_roots_card_le_mul_deg (A B : Poly2 K) (hA : 1 ≤ A.natDeg) (hB : B ≠ zero)
    (hcop : CoprimeZ A B) (pts : List (K × K)) (hnd : (pts.map Prod.fst).Nodup)
    (hroots : ∀ p ∈ pts, A.eval2 p.1 p.2 = zero ∧ B.eval2 p.1 p.2 = zero) :
    pts.length ≤ tdeg A * tdeg B := by
  have hr := (resZ_ne_zero_iff A B hA hB).mpr hcop
  have hdeg := natDeg_resZ_le A B hA
  have := gs_formal_root_bound (tdeg A * tdeg B) (resZ A B).coeffs (pts.map Prod.fst)
    (by have : (resZ A B).coeffs.length - 1 ≤ tdeg A * tdeg B := hdeg; omega)
    (exists_ne_zero_of_ne_zero hr) hnd
    (fun y hy => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
      rw [← UPoly.eval_eq]
      exact eval_resZ_eq_zero A B hA p.1 p.2 (hroots p hp).1 (hroots p hp).2)
  rwa [List.length_map] at this

end Poly2

/-! ## Witnesses -/

end Qsag

end

section
namespace Qsag

set_option autoImplicit false
open CommRingOps RoundPoly

namespace SylElim

/-! ## `natRangeSum` & `rangeSum` splitting helpers -/

/-! ## Sylvester Matrix and Resultant -/

section SylRes
variable {R : Type} [LawfulCommRing R] [DecidableEq R]
open UPoly

private theorem C_zero : (C zero : UPoly R) = zero := by
  rw [← CHom_apply]; exact CHom.map_zero

private theorem C_add (a b : R) : C (add a b) = add (C a) (C b) := UPoly.C_add_eq a b
private theorem C_mul (a b : R) : C (mul a b) = mul (C a) (C b) := UPoly.C_mul_eq a b

/-- `(m + N) × (m + N)` Sylvester matrix of `(A, B)` with `m` shifted `B`-rows followed by
    `N` shifted `A`-rows. -/
@[expose] def sylMat (m : Nat) (_N : Nat) (A B : UPoly R) (i j : Nat) : R :=
  if i < m then
    if i ≤ j then coeffAt B.coeffs (j - i) else zero
  else
    if i - m ≤ j then coeffAt A.coeffs (j - (i - m)) else zero

/-- Constructive `(m, N)`-Sylvester resultant `det (m + N) (sylMat m N A B)`. -/
@[expose] def sylRes (m N : Nat) (A B : UPoly R) : R :=
  Mat.det (m + N) (sylMat m N A B)

theorem map_sylRes {S : Type} [LawfulCommRing S] [DecidableEq S]
    (φ : RingHom R S) (m N : Nat) (A B : UPoly R) :
    φ.toFun (sylRes m N A B) = sylRes m N ((mapHom φ).toFun A) ((mapHom φ).toFun B) := by
  unfold sylRes
  rw [Mat.map_det]
  refine Mat.det_congr (m + N) fun i _ j _ => ?_
  unfold sylMat
  if hi : i < m then
    rw [ite_pos hi, ite_pos hi]
    if hij : i ≤ j then rw [ite_pos hij, ite_pos hij, coeffAt_mapHom]
    else rw [ite_neg hij, ite_neg hij, φ.map_zero]
  else
    rw [ite_neg hi, ite_neg hi]
    if hij : i - m ≤ j then rw [ite_pos hij, ite_pos hij, coeffAt_mapHom]
    else rw [ite_neg hij, ite_neg hij, φ.map_zero]

/-- Tight row/column-weighted degree bound on `sylRes m N A B`:
    `w (sylRes m N A B) ≤ m * h_B + N * h_A - m * N`. -/
theorem degFn_sylRes_tight {w : R → Nat} (hw : DegFn w) (hw1 : w one = 0)
    (m N h_A h_B : Nat) (A B : UPoly R)
    (hA : A.wdeg w 1 ≤ h_A) (hB : B.wdeg w 1 ≤ h_B) :
    w (sylRes m N A B) ≤ m * h_B + N * h_A - m * N := by
  if hNe : sylRes m N A B = zero then
    rw [hNe, hw.zero]; exact Nat.zero_le _
  else
    let rowWt (i : Nat) : Nat := if i < m then h_B + i else h_A + (i - m)
    let colWt (j : Nat) : Nat := j
    have hEntry : ∀ i, i < m + N → ∀ j, j < m + N → sylMat m N A B i j ≠ zero →
        w (sylMat m N A B i j) + colWt j ≤ rowWt i := by
      intro i _ j _ hnij
      dsimp only [colWt, rowWt]
      if hi : i < m then
        rw [ite_pos hi]
        unfold sylMat at hnij ⊢
        rw [ite_pos hi] at hnij ⊢
        if hij : i ≤ j then
          rw [ite_pos hij] at hnij ⊢
          have hle := le_wdeg w 1 B (j - i) hnij
          have := hB; omega
        else rw [ite_neg hij] at hnij; exact absurd rfl hnij
      else
        rw [ite_neg hi]
        unfold sylMat at hnij ⊢
        rw [ite_neg hi] at hnij ⊢
        if hij : i - m ≤ j then
          rw [ite_pos hij] at hnij ⊢
          have hle := le_wdeg w 1 A (j - (i - m)) hnij
          have := hA; omega
        else rw [ite_neg hij] at hnij; exact absurd rfl hnij
    have hDet := Mat.degFn_det_weighted_le hw hw1 (m + N) (sylMat m N A B) rowWt colWt hEntry hNe
    have hCol : Mat.natRangeSum (m + N) colWt =
        Mat.natRangeSum m (fun i => i) + Mat.natRangeSum N (fun i => i) + m * N :=
      natRangeSum_split_id m N
    have hRow1 : Mat.natRangeSum m rowWt = m * h_B + Mat.natRangeSum m (fun i => i) := by
      have hEq : ∀ k, k ≤ m → Mat.natRangeSum k rowWt = Mat.natRangeSum k (fun i => h_B + i) := by
        intro k; induction k with
        | zero => intro _; simp only [Mat.natRangeSum_zero]
        | succ k ihk =>
          intro hk; simp only [Mat.natRangeSum_succ]; show Mat.natRangeSum k rowWt + rowWt k = Mat.natRangeSum k _ + (h_B + k)
          rw [ihk (by omega)]; dsimp only [rowWt]; rw [ite_pos (show k < m by omega)]
      rw [hEq m (Nat.le_refl m), natRangeSum_const_add]
    have hRow2 : Mat.natRangeSum N (fun r => rowWt (m + r)) = N * h_A + Mat.natRangeSum N (fun i => i) := by
      have hEq : ∀ k, Mat.natRangeSum k (fun r => rowWt (m + r)) = Mat.natRangeSum k (fun r => h_A + r) := by
        intro k; induction k with
        | zero => simp only [Mat.natRangeSum_zero]
        | succ k ihk =>
          simp only [Mat.natRangeSum_succ]
          show Mat.natRangeSum k _ + rowWt (m + k) = Mat.natRangeSum k _ + (h_A + k)
          rw [ihk]; dsimp only [rowWt]; rw [ite_neg (by omega), show m + k - m = k by omega]
      rw [hEq N, natRangeSum_const_add]
    have hRow := natRangeSum_split m N rowWt
    rw [hRow1, hRow2] at hRow
    show w (Mat.det (m + N) (sylMat m N A B)) ≤ _
    omega

theorem degFn_sylRes_le {w : R → Nat} (hw : DegFn w) (hw1 : w one = 0)
    (m N h_A h_B : Nat) (A B : UPoly R)
    (hA : A.wdeg w 1 ≤ h_A) (hB : B.wdeg w 1 ≤ h_B)
    (hm : m ≤ h_A) (hN : N ≤ h_B) :
    w (sylRes m N A B) ≤ h_A * h_B := by
  have h1 := degFn_sylRes_tight hw hw1 m N h_A h_B A B hA hB
  obtain ⟨dA, rfl⟩ : ∃ dA, h_A = m + dA := ⟨h_A - m, by omega⟩
  obtain ⟨dB, rfl⟩ : ∃ dB, h_B = N + dB := ⟨h_B - N, by omega⟩
  have hExp : (m + dA) * (N + dB) = m * N + m * dB + dA * N + dA * dB := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
  have hSub : m * (N + dB) + N * (m + dA) - m * N = m * N + m * dB + dA * N := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_comm N m, Nat.mul_comm N dA]; omega
  omega

/-! ## Constructive division by `X - C ζ` -/

/-- **Master Linear-Factor Identity**: over any `[LawfulCommRing R] [DecidableEq R]`, if
    `Q.natDeg ≤ m'` and `F.natDeg ≤ N`, then
    `sylRes (m' + 1) N ((X - C ζ) * Q) F = F.eval ζ * sylRes m' N Q F`. -/
theorem sylRes_mul_X_sub (m' N : Nat) (ζ : R) (Q F : UPoly R)
    (hQ : Q.natDeg ≤ m') (hF : F.natDeg ≤ N) :
    sylRes (m' + 1) N (mul (sub X (C ζ)) Q) F = mul (F.eval ζ) (sylRes m' N Q F) := by
  let K := m' + 1 + N
  let A := mul (sub X (C ζ)) Q
  let Lmat (i l : Nat) : R :=
    if i = l then one
    else if 1 ≤ i ∧ i ≤ m' ∧ l + 1 = i then neg ζ
    else zero
  let Pmat (j c : Nat) : R := if c ≤ j then CRing.npow ζ (j - c) else zero
  have hDetL : Mat.det K Lmat = one :=
    Mat.det_lower_tri_one K Lmat
      (fun i l hil _ => by
        dsimp only [Lmat]; rw [ite_neg (Nat.ne_of_lt hil), ite_neg (by omega)])
      (fun i _ => by dsimp only [Lmat]; rw [ite_pos rfl])
  have hDetP : Mat.det K Pmat = one :=
    Mat.det_lower_tri_one K Pmat
      (fun j c hjc _ => by dsimp only [Pmat]; rw [ite_neg (by omega)])
      (fun j _ => by dsimp only [Pmat]; rw [ite_pos (Nat.le_refl j), Nat.sub_self]; rfl)
  let M1 := Mat.matMul K Lmat (sylMat (m' + 1) N A F)
  let M2 := Mat.matMul K M1 Pmat
  have hM1_row0 : ∀ j, j < K → M1 0 j = coeffAt F.coeffs j := by
    intro j hj
    dsimp only [M1]; simp only [Mat.matMul_apply]
    rw [Mat.rangeSum_single (Nat.zero_lt_of_lt hj) _ fun l _ hne => by
      dsimp only [Lmat]; rw [ite_neg (Ne.symm hne), ite_neg (by omega), LawfulCommRing.zero_mul]]
    dsimp only [Lmat]; rw [ite_pos rfl, LawfulCommRing.one_mul]
    unfold sylMat; rw [ite_pos (Nat.zero_lt_succ m'), ite_pos (Nat.zero_le j), Nat.sub_zero]
  let rowPoly (i' : Nat) : UPoly R :=
    if i' < m' then mul (monom i') F else mul (monom (i' - m')) Q
  have hRowPoly_top : ∀ i', i' < m' + N → coeffAt (rowPoly i').coeffs (m' + N) = zero := by
    intro i' hi'
    dsimp only [rowPoly]
    if hlt : i' < m' then
      rw [ite_pos hlt, coeffAt_monom_mul, ite_pos (by omega)]
      exact F.coeffAt_eq_zero_of_natDeg_lt (by omega)
    else
      rw [ite_neg hlt, coeffAt_monom_mul, ite_pos (by omega)]
      exact Q.coeffAt_eq_zero_of_natDeg_lt (by omega)
  have hM1_succ : ∀ i', i' < m' + N → ∀ j, j < K →
      M1 (i' + 1) j = coeffAt (mul (sub X (C ζ)) (rowPoly i')).coeffs j := by
    intro i' hi' j hj
    dsimp only [M1]; simp only [Mat.matMul_apply]
    if hlt : i' < m' then
      have hTwo : Mat.rangeSum K (fun l => mul (Lmat (i' + 1) l) (sylMat (m' + 1) N A F l j)) =
          add (mul (neg ζ) (sylMat (m' + 1) N A F i' j)) (sylMat (m' + 1) N A F (i' + 1) j) := by
        let f0 (l : Nat) : R := if l = i' then mul (neg ζ) (sylMat (m' + 1) N A F i' j) else zero
        let f1 (l : Nat) : R := if l = i' + 1 then sylMat (m' + 1) N A F (i' + 1) j else zero
        have hSplit : Mat.rangeSum K (fun l => mul (Lmat (i' + 1) l) (sylMat (m' + 1) N A F l j)) =
            Mat.rangeSum K (fun l => add (f0 l) (f1 l)) :=
          Mat.rangeSum_congr fun l _ => by
            dsimp only [Lmat, f0, f1]
            if h1 : l = i' + 1 then
              subst h1; rw [ite_pos rfl, ite_neg (by omega), ite_pos rfl, LawfulCommRing.zero_add, LawfulCommRing.one_mul]
            else if h0 : l = i' then
              subst h0; rw [ite_neg (by omega), ite_pos ⟨by omega, by omega, rfl⟩, ite_pos rfl, ite_neg (by omega), LawfulCommRing.add_zero]
            else
              rw [ite_neg (Ne.symm h1), ite_neg (by omega), ite_neg h0, ite_neg h1, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
        rw [hSplit, Mat.rangeSum_add,
          Mat.rangeSum_single (j₀ := i') (by omega) f0 (fun l _ hne => by dsimp only [f0]; rw [ite_neg hne]),
          Mat.rangeSum_single (j₀ := i' + 1) (by omega) f1 (fun l _ hne => by dsimp only [f1]; rw [ite_neg hne])]
        dsimp only [f0, f1]; rw [ite_pos rfl, ite_pos rfl]
      rw [hTwo]; dsimp only [rowPoly]; rw [ite_pos hlt]
      unfold sylMat
      rw [ite_pos (Nat.lt_succ_of_lt hlt), ite_pos (Nat.succ_lt_succ hlt)]
      cases j with
      | zero =>
        rw [(coeffAt_sub_X_C_mul ζ _).1, coeffAt_monom_mul]
        if hi0 : i' = 0 then
          subst hi0
          rw [ite_pos (Nat.le_refl 0), ite_neg (Nat.not_succ_le_zero 0)]
          constructive_ring
        else
          rw [ite_neg (show ¬ (i' ≤ 0) by omega), ite_neg (show ¬ (i' + 1 ≤ 0) by omega)]
          constructive_ring
      | succ s =>
        rw [(coeffAt_sub_X_C_mul ζ _).2 s, coeffAt_monom_mul, coeffAt_monom_mul]
        if h1 : i' ≤ s then
          rw [ite_pos (show i' ≤ s + 1 by omega), ite_pos (Nat.succ_le_succ h1), ite_pos h1,
            Nat.succ_sub_succ]; constructive_ring
        else if h2 : i' = s + 1 then
          subst h2
          rw [ite_pos (Nat.le_refl (s + 1)), ite_neg (show ¬ (s + 1 + 1 ≤ s + 1) by omega),
            ite_neg (show ¬ (s + 1 ≤ s) by omega)]; constructive_ring
        else
          rw [ite_neg (show ¬ (i' ≤ s + 1) by omega), ite_neg (show ¬ (i' + 1 ≤ s + 1) by omega),
            ite_neg h1]; constructive_ring
    else
      rw [Mat.rangeSum_single (j₀ := i' + 1) (by omega) _ fun l _ hne => by
        dsimp only [Lmat]; rw [ite_neg (Ne.symm hne), ite_neg (by omega), LawfulCommRing.zero_mul]]
      dsimp only [Lmat, rowPoly]; rw [ite_pos rfl, LawfulCommRing.one_mul, ite_neg hlt]
      unfold sylMat
      rw [ite_neg (by omega), show i' + 1 - (m' + 1) = i' - m' by omega]
      have hComm : mul (sub X (C ζ)) (mul (monom (i' - m')) Q) = mul (monom (i' - m')) A := by
        dsimp only [A]; constructive_ring
      rw [hComm, coeffAt_monom_mul]
  have hM2_00 : M2 0 0 = F.eval ζ := by
    dsimp only [M2]; simp only [Mat.matMul_apply]
    have hCongr : Mat.rangeSum K (fun j => mul (M1 0 j) (Pmat j 0)) =
        Mat.rangeSum K (fun j => mul (coeffAt F.coeffs j) (CRing.npow ζ j)) :=
      Mat.rangeSum_congr fun j hj => by
        rw [hM1_row0 j hj]; dsimp only [Pmat]; rw [ite_pos (Nat.zero_le j), Nat.sub_zero]
    have hLen : F.coeffs.length ≤ K := by unfold natDeg at hF; dsimp only [K]; omega
    rw [hCongr, rangeSum_eval_eq ζ F.coeffs K hLen, eval_eq]
  have hM2_col0 : ∀ i', i' < m' + N → M2 (i' + 1) 0 = zero := by
    intro i' hi'
    dsimp only [M2]; simp only [Mat.matMul_apply]
    have hCongr : Mat.rangeSum K (fun j => mul (M1 (i' + 1) j) (Pmat j 0)) =
        Mat.rangeSum ((m' + N) + 1)
          (fun j => mul (coeffAt (mul (sub X (C ζ)) (rowPoly i')).coeffs j) (CRing.npow ζ j)) := by
      have hKEq : K = (m' + N) + 1 := by dsimp only [K]; omega
      rw [hKEq]
      refine Mat.rangeSum_congr fun j hj => ?_
      rw [hM1_succ i' hi' j (by dsimp only [K]; omega)]
      dsimp only [Pmat]; rw [ite_pos (Nat.zero_le j), Nat.sub_zero]
    rw [hCongr, telescope_col0, hRowPoly_top i' hi', LawfulCommRing.zero_mul, LawfulCommRing.neg_zero]
  have hM2_minor : ∀ i', i' < m' + N → ∀ c, c < m' + N →
      Mat.minor M2 0 0 i' c = sylMat m' N Q F i' c := by
    intro i' hi' c hc
    rw [Mat.minor_zero_zero]
    dsimp only [M2]; simp only [Mat.matMul_apply]
    have hKEq : K = c + 1 + ((m' + N - c - 1) + 1) := by dsimp only [K]; omega
    have hCongr : Mat.rangeSum K (fun j => mul (M1 (i' + 1) j) (Pmat j (c + 1))) =
        Mat.rangeSum (c + 1 + ((m' + N - c - 1) + 1))
          (fun j => mul (coeffAt (mul (sub X (C ζ)) (rowPoly i')).coeffs j)
            (if c + 1 ≤ j then CRing.npow ζ (j - (c + 1)) else zero)) := by
      rw [hKEq]
      refine Mat.rangeSum_congr fun j hj => ?_
      rw [hM1_succ i' hi' j (by dsimp only [K]; omega)]
    rw [hCongr, telescope_col_succ, show c + 1 + (m' + N - c - 1) = m' + N by omega,
      hRowPoly_top i' hi', LawfulCommRing.zero_mul, LawfulCommRing.sub_zero]
    dsimp only [rowPoly]; unfold sylMat
    if hlt : i' < m' then rw [ite_pos hlt, ite_pos hlt, coeffAt_monom_mul]
    else rw [ite_neg hlt, ite_neg hlt, coeffAt_monom_mul]
  have hDetM2 : Mat.det K M2 = sylRes (m' + 1) N A F := by
    dsimp only [M2, M1]
    rw [Mat.det_matMul, Mat.det_matMul, hDetL, hDetP, LawfulCommRing.one_mul, LawfulCommRing.mul_one]
    rfl
  have hKEq : K = (m' + N) + 1 := by dsimp only [K]; omega
  rw [← hDetM2, hKEq, Mat.det_col0_unit (m' + N) M2 hM2_col0, hM2_00,
    Mat.det_congr (m' + N) hM2_minor]
  rfl

/-- Common root `ζ` of `(A, B)` forces `sylRes m N A B = 0` (`1 ≤ m`). -/
theorem sylRes_eq_zero_of_common_root {m N : Nat} {A B : UPoly R} {ζ : R}
    (hm : 1 ≤ m) (hA : A.natDeg ≤ m) (hB : B.natDeg ≤ N)
    (hAz : A.eval ζ = zero) (hBz : B.eval ζ = zero) :
    sylRes m N A B = zero := by
  obtain ⟨hDiv, hDeg⟩ := divXSub_spec A ζ
  rw [hAz, C_zero, LawfulCommRing.zero_add] at hDiv
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [hDiv, sylRes_mul_X_sub m' N ζ (divXSub A ζ) B (by omega) hB, hBz, LawfulCommRing.zero_mul]

/-! ## Unit-Leading Division `divModLead` & Bézout Invertibility `isUnit_sylRes_of_bezout` -/

def divModLeadAux (A : UPoly R) (m : Nat) (c_inv : R) : Nat → UPoly R → UPoly R × UPoly R
  | 0, P => (zero, P)
  | fuel + 1, P =>
    if P.natDeg < m then (zero, P)
    else
      let qTop := mul (C (mul (coeffAt P.coeffs P.natDeg) c_inv)) (monom (P.natDeg - m))
      let P' := sub P (mul qTop A)
      let qr := divModLeadAux A m c_inv fuel P'
      (add qTop qr.1, qr.2)

/-- Polynomial division by `A` (`1 ≤ m`, `A.natDeg ≤ m`) with invertible `m`-th coefficient. -/
def divModLead (A : UPoly R) (m : Nat) (c_inv : R) (P : UPoly R) : UPoly R × UPoly R :=
  divModLeadAux A m c_inv (P.natDeg + 1) P

theorem divModLead_spec (A : UPoly R) (m : Nat) (c_inv : R)
    (hm : 1 ≤ m) (hA : A.natDeg ≤ m) (hInv : mul c_inv (coeffAt A.coeffs m) = one) (P : UPoly R) :
    P = add (mul (divModLead A m c_inv P).1 A) (divModLead A m c_inv P).2 ∧
      (divModLead A m c_inv P).2.natDeg < m := by
  have aux : ∀ (fuel : Nat) (P : UPoly R), P.natDeg < fuel →
      P = add (mul (divModLeadAux A m c_inv fuel P).1 A) (divModLeadAux A m c_inv fuel P).2 ∧
        (divModLeadAux A m c_inv fuel P).2.natDeg < m := by
    intro fuel; induction fuel with
    | zero => intros _ h; exfalso; omega
    | succ fuel ih =>
      intro P hFuel
      unfold divModLeadAux
      if hlt : P.natDeg < m then
        rw [ite_pos hlt]
        exact ⟨by show P = add (mul zero A) P; constructive_ring, hlt⟩
      else
        rw [ite_neg hlt]
        let qTop := mul (C (mul (coeffAt P.coeffs P.natDeg) c_inv)) (monom (P.natDeg - m))
        let P' := sub P (mul qTop A)
        have hCancel : ∀ k, P.natDeg ≤ k → coeffAt P'.coeffs k = zero := by
          intro k hk
          dsimp only [P', qTop]
          have hqA : mul (mul (C (mul (coeffAt P.coeffs P.natDeg) c_inv)) (monom (P.natDeg - m))) A =
              mul (C (mul (coeffAt P.coeffs P.natDeg) c_inv)) (mul (monom (P.natDeg - m)) A) := by
            constructive_ring
          rw [coeffAt_sub, hqA, coeffAt_C_mul, coeffAt_monom_mul, ite_pos (by omega)]
          if hEq : k = P.natDeg then
            subst hEq
            rw [show P.natDeg - (P.natDeg - m) = m by omega]
            have h1 : mul (mul (coeffAt P.coeffs P.natDeg) c_inv) (coeffAt A.coeffs m) =
                mul (coeffAt P.coeffs P.natDeg) (mul c_inv (coeffAt A.coeffs m)) := by constructive_ring
            rw [h1, hInv, LawfulCommRing.mul_one, LawfulCommRing.sub_self]
          else
            rw [P.coeffAt_eq_zero_of_natDeg_lt (by omega),
              A.coeffAt_eq_zero_of_natDeg_lt (by omega), LawfulCommRing.mul_zero, LawfulCommRing.sub_self]
        have hDegP' : P'.natDeg < fuel := by
          have hle : P'.natDeg ≤ P.natDeg - 1 :=
            natDeg_le_of_coeffAt P' (P.natDeg - 1) fun k hk => hCancel k (by omega)
          omega
        obtain ⟨hEq', hRem⟩ := ih P' hDegP'
        refine ⟨?_, hRem⟩
        show P = add (mul (add qTop (divModLeadAux A m c_inv fuel P').1) A)
          (divModLeadAux A m c_inv fuel P').2
        have hP : P = add (mul qTop A) P' := by dsimp only [P']; constructive_ring
        conv => lhs; rw [hP, hEq']
        constructive_ring
  exact aux (P.natDeg + 1) P (Nat.lt_succ_self _)

/-- **Bézout Invertibility**: if `A.natDeg ≤ m`, `coeffAt A.coeffs m` is a unit, `B.natDeg ≤ N`,
    and `U0 * A + V0 * B = 1`, then `sylRes m N A B` is a unit in `R`! -/
theorem isUnit_sylRes_of_bezout {m N : Nat} {A B U0 V0 : UPoly R} {c_inv : R}
    (hA : A.natDeg ≤ m) (hInv : mul c_inv (coeffAt A.coeffs m) = one)
    (hB : B.natDeg ≤ N) (hBez : add (mul U0 A) (mul V0 B) = one) :
    ∃ r_inv : R, mul r_inv (sylRes m N A B) = one := by
  if hm0 : m = 0 then
    subst hm0
    have hDiag : sylRes 0 N A B = CRing.npow (coeffAt A.coeffs 0) N := by
      unfold sylRes; rw [Nat.zero_add]
      refine Mat.det_lower_tri_const (coeffAt A.coeffs 0) N (sylMat 0 N A B) (fun i j hij _ => ?_) (fun i _ => ?_)
      · unfold sylMat; rw [ite_neg (Nat.not_lt_zero i), Nat.sub_zero, ite_pos (Nat.le_of_lt hij)]
        exact A.coeffAt_eq_zero_of_natDeg_lt (by omega)
      · unfold sylMat; rw [ite_neg (Nat.not_lt_zero i), Nat.sub_zero, ite_pos (Nat.le_refl i), Nat.sub_self]
    have hPowInv : ∀ n : Nat, mul (CRing.npow c_inv n) (CRing.npow (coeffAt A.coeffs 0) n) = one := by
      intro n; induction n with
      | zero => exact LawfulCommRing.one_mul one
      | succ n ihn =>
        show mul (mul (CRing.npow c_inv n) c_inv) (mul (CRing.npow (coeffAt A.coeffs 0) n) (coeffAt A.coeffs 0)) = one
        have hAssoc : mul (mul (CRing.npow c_inv n) c_inv) (mul (CRing.npow (coeffAt A.coeffs 0) n) (coeffAt A.coeffs 0)) =
            mul (mul (CRing.npow c_inv n) (CRing.npow (coeffAt A.coeffs 0) n)) (mul c_inv (coeffAt A.coeffs 0)) := by
          constructive_ring
        rw [hAssoc, ihn, hInv, LawfulCommRing.mul_one]
    exact ⟨CRing.npow c_inv N, by rw [hDiag]; exact hPowInv N⟩
  else
    have hm : 1 ≤ m := by omega
    let qr (k : Nat) := divModLead A m c_inv (mul (monom k) V0)
    let Vk (k : Nat) : UPoly R := (qr k).2
    let Uk (k : Nat) : UPoly R := add (mul (monom k) U0) (mul (qr k).1 B)
    have hUkVk : ∀ k, add (mul (Uk k) A) (mul (Vk k) B) = monom k := fun k =>
      bezout_step (monom k) U0 A V0 B (qr k).1 (qr k).2
        (by rw [hBez, LawfulCommRing.mul_one])
        (divModLead_spec A m c_inv hm hA hInv (mul (monom k) V0)).1
    have hVk_high : ∀ k i, m ≤ i → coeffAt (Vk k).coeffs i = zero := fun k i hi =>
      (Vk k).coeffAt_eq_zero_of_natDeg_lt
        (Nat.lt_of_lt_of_le (divModLead_spec A m c_inv hm hA hInv _).2 hi)
    have hUk_high : ∀ k, k < m + N → ∀ r, N ≤ r → coeffAt (Uk k).coeffs r = zero := by
      intro k hk r hr
      have hProdHigh : ∀ t, m + N ≤ t → coeffAt (mul (Uk k) A).coeffs t = zero := by
        intro t ht
        have hEq : mul (Uk k) A = sub (monom k) (mul (Vk k) B) := by
          rw [← hUkVk k]; constructive_ring
        have hVB_deg : (mul (Vk k) B).natDeg < m + N := by
          have h1 := natDeg_mul_le (Vk k) B
          have h2 : (Vk k).natDeg < m := (divModLead_spec A m c_inv hm hA hInv (mul (monom k) V0)).2
          have := hB; omega
        rw [hEq, coeffAt_sub, coeffAt_monom, ite_neg (by omega),
          (mul (Vk k) B).coeffAt_eq_zero_of_natDeg_lt (by omega), LawfulCommRing.sub_self]
      if hU0 : Uk k = zero then
        rw [hU0, coeffs_zero, coeffAt_nil]
      else
        if hLt : (Uk k).natDeg < N then
          exact (Uk k).coeffAt_eq_zero_of_natDeg_lt (by omega)
        else
          exfalso
          let u := (Uk k).natDeg
          have hTop0 : coeffAt (mul (Uk k) A).coeffs (u + m) = zero := hProdHigh (u + m) (by omega)
          have hAm : A.natDeg = m := by
            apply Nat.le_antisymm hA
            apply Decidable.byContradiction; intro hNot
            have hz := A.coeffAt_eq_zero_of_natDeg_lt (Nat.lt_of_not_le hNot)
            rw [hz, LawfulCommRing.mul_zero] at hInv
            have hLeadZero : (Uk k).lead = zero := by
              have hMul := congrArg (mul (Uk k).lead) hInv
              rw [LawfulCommRing.mul_zero, LawfulCommRing.mul_one] at hMul
              exact hMul.symm
            exact lead_ne_zero hU0 hLeadZero
          have hTopEq := (coeffAt_mul_top (Uk k) A).2
          simp only [lead_eq] at hTopEq
          rw [hAm] at hTopEq
          rw [hTopEq] at hTop0
          have hLead0 : coeffAt (Uk k).coeffs u = zero := by
            have h1 : coeffAt (Uk k).coeffs u = mul (coeffAt (Uk k).coeffs u) (mul c_inv (coeffAt A.coeffs m)) := by
              rw [hInv, LawfulCommRing.mul_one]
            have h2 : mul (coeffAt (Uk k).coeffs u) (mul c_inv (coeffAt A.coeffs m)) =
                mul c_inv (mul (coeffAt (Uk k).coeffs u) (coeffAt A.coeffs m)) := by constructive_ring
            rw [h1, h2, hTop0, LawfulCommRing.mul_zero]
          exact lead_ne_zero hU0 (by simpa only [lead_eq] using hLead0)
    let W (k l : Nat) : R :=
      if l < m then coeffAt (Vk k).coeffs l else coeffAt (Uk k).coeffs (l - m)
    have hMulId : Mat.det (m + N) (Mat.matMul (m + N) W (sylMat m N A B)) = one := by
      rw [Mat.det_congr (m + N) (N := Mat.idMat) fun k hk j _ => ?_, Mat.det_idMat]
      simp only [Mat.matMul_apply]
      rw [rangeSum_split m N]
      have hLeft : Mat.rangeSum m (fun l => mul (W k l) (sylMat m N A B l j)) =
          coeffAt (mul (Vk k) B).coeffs j := by
        have hVpoly : Vk k = polyOfRange m (fun l => coeffAt (Vk k).coeffs l) := by
          apply ext_coeffAt; intro i
          rw [coeffAt_polyOfRange]
          if hi : i < m then rw [ite_pos hi] else rw [ite_neg hi, hVk_high k i (by omega)]
        conv => rhs; rw [hVpoly, coeffAt_mul_polyOfRange]
        refine Mat.rangeSum_congr fun l hl => ?_
        dsimp only [W]; unfold sylMat; rw [ite_pos hl, ite_pos hl]
      have hRight : Mat.rangeSum N (fun r => mul (W k (m + r)) (sylMat m N A B (m + r) j)) =
          coeffAt (mul (Uk k) A).coeffs j := by
        have hUpoly : Uk k = polyOfRange N (fun r => coeffAt (Uk k).coeffs r) := by
          apply ext_coeffAt; intro r
          rw [coeffAt_polyOfRange]
          if hr : r < N then rw [ite_pos hr] else rw [ite_neg hr, hUk_high k hk r (by omega)]
        conv => rhs; rw [hUpoly, coeffAt_mul_polyOfRange]
        refine Mat.rangeSum_congr fun r _ => ?_
        dsimp only [W]; unfold sylMat
        rw [ite_neg (by omega), ite_neg (by omega), show m + r - m = r by omega]
      rw [hLeft, hRight, LawfulCommRing.add_comm, ← coeffAt_add, hUkVk k, coeffAt_monom]
      rw [Mat.idMat_eq]
      if hkj : k = j then subst hkj; rw [ite_pos rfl]
      else rw [ite_neg (Ne.symm hkj), ite_neg hkj]
    rw [Mat.det_matMul] at hMulId
    exact ⟨Mat.det (m + N) W, hMulId⟩

end SylRes
end SylElim

end Qsag

end

section
namespace Qsag

set_option autoImplicit false
open CommRingOps RoundPoly

namespace SylElim

@[ext]
structure Dual (R : Type) where
  fst : R
  snd : R
  deriving DecidableEq

namespace Dual
section Ring
variable {R S : Type} [LawfulCommRing R] [LawfulCommRing S]

instance : LawfulCommRing (Dual R) where
  zero := ⟨zero, zero⟩
  one := ⟨one, zero⟩
  add x y := ⟨add x.fst y.fst, add x.snd y.snd⟩
  mul x y := ⟨mul x.fst y.fst, add (mul x.fst y.snd) (mul x.snd y.fst)⟩
  neg x := ⟨neg x.fst, neg x.snd⟩
  sub x y := ⟨sub x.fst y.fst, sub x.snd y.snd⟩
  add_assoc a b c := by apply Dual.ext <;> dsimp <;> exact LawfulCommRing.add_assoc _ _ _
  add_comm a b := by apply Dual.ext <;> dsimp <;> exact LawfulCommRing.add_comm _ _
  zero_add a := by apply Dual.ext <;> dsimp <;> exact LawfulCommRing.zero_add _
  add_zero a := by apply Dual.ext <;> dsimp <;> exact LawfulCommRing.add_zero _
  add_left_neg a := by apply Dual.ext <;> dsimp <;> exact LawfulCommRing.add_left_neg _
  sub_eq_add_neg a b := by apply Dual.ext <;> dsimp <;> exact LawfulCommRing.sub_eq_add_neg _ _
  mul_assoc a b c := by apply Dual.ext <;> dsimp <;> constructive_ring
  mul_comm a b := by apply Dual.ext <;> dsimp <;> constructive_ring
  one_mul a := by apply Dual.ext <;> dsimp <;> constructive_ring
  mul_one a := by apply Dual.ext <;> dsimp <;> constructive_ring
  left_distrib a b c := by apply Dual.ext <;> dsimp <;> constructive_ring
  right_distrib a b c := by apply Dual.ext <;> dsimp <;> constructive_ring

def inl : RingHom R (Dual R) where
  toFun a := ⟨a, zero⟩
  map_zero := rfl
  map_one := rfl
  map_add a b := by
    apply Dual.ext
    · rfl
    · show zero = add zero zero; rw [LawfulCommRing.add_zero]
  map_mul a b := by
    apply Dual.ext
    · rfl
    · show zero = add (mul a zero) (mul zero b); constructive_ring

def fstHom : RingHom (Dual R) R where
  toFun x := x.fst
  map_zero := rfl
  map_one := rfl
  map_add _ _ := rfl
  map_mul _ _ := rfl

def map (φ : RingHom R S) : RingHom (Dual R) (Dual S) where
  toFun x := ⟨φ.toFun x.fst, φ.toFun x.snd⟩
  map_zero := by apply Dual.ext <;> exact φ.map_zero
  map_one := by
    apply Dual.ext
    · exact φ.map_one
    · exact φ.map_zero
  map_add a b := by apply Dual.ext <;> exact φ.map_add _ _
  map_mul a b := by
    apply Dual.ext
    · exact φ.map_mul _ _
    · show φ.toFun (add (mul a.fst b.snd) (mul a.snd b.fst)) =
        add (mul (φ.toFun a.fst) (φ.toFun b.snd)) (mul (φ.toFun a.snd) (φ.toFun b.fst))
      rw [φ.map_add, φ.map_mul, φ.map_mul]

@[expose] def eps : Dual R := ⟨zero, one⟩

end Ring
end Dual

section Deriv
variable {R : Type} [LawfulCommRing R] [DecidableEq R]
open UPoly

private theorem C_zero_deriv : (C zero : UPoly R) = zero := by
  rw [← CHom_apply]; exact CHom.map_zero

def dualPerturb (P0 B : UPoly R) : UPoly (Dual R) :=
  add ((mapHom Dual.inl).toFun P0) (mul (C Dual.eps) ((mapHom Dual.inl).toFun B))

/-- Formal directional resultant derivative `[ε¹] sylRes m N C1 (P0 + ε · B)`. -/
@[expose] def sylResDeriv (m N : Nat) (C1 P0 B : UPoly R) : R :=
  (sylRes m N ((mapHom Dual.inl).toFun C1) (dualPerturb P0 B)).snd

private theorem mapHom_comp {A B C' : Type}
    [LawfulCommRing A] [DecidableEq A] [LawfulCommRing B] [DecidableEq B] [LawfulCommRing C'] [DecidableEq C']
    (ψ : RingHom B C') (φ : RingHom A B) (p : UPoly A) :
    (mapHom ψ).toFun ((mapHom φ).toFun p) = (mapHom (ψ.comp φ)).toFun p := by
  apply ext_coeffAt; intro k
  rw [coeffAt_mapHom, coeffAt_mapHom, coeffAt_mapHom, RingHom.comp_apply]

private theorem mapHom_eq_of_toFun {A B : Type}
    [LawfulCommRing A] [DecidableEq A] [LawfulCommRing B] [DecidableEq B]
    (φ ψ : RingHom A B) (h : ∀ a, φ.toFun a = ψ.toFun a) (p : UPoly A) :
    (mapHom φ).toFun p = (mapHom ψ).toFun p := by
  apply ext_coeffAt; intro k
  rw [coeffAt_mapHom, coeffAt_mapHom, h]

private theorem mapHom_id (p : UPoly R) : (mapHom (RingHom.id R)).toFun p = p := by
  apply ext_coeffAt; intro k
  rw [coeffAt_mapHom, RingHom.id_apply]

theorem map_sylResDeriv {S : Type} [LawfulCommRing S] [DecidableEq S]
    (φ : RingHom R S) (m N : Nat) (C1 P0 B : UPoly R) :
    φ.toFun (sylResDeriv m N C1 P0 B) =
      sylResDeriv m N ((mapHom φ).toFun C1) ((mapHom φ).toFun P0) ((mapHom φ).toFun B) := by
  unfold sylResDeriv
  have h1 : (Dual.map φ).toFun (sylRes m N ((mapHom Dual.inl).toFun C1) (dualPerturb P0 B)) =
      sylRes m N ((mapHom (Dual.map φ)).toFun ((mapHom Dual.inl).toFun C1))
        ((mapHom (Dual.map φ)).toFun (dualPerturb P0 B)) :=
    map_sylRes (Dual.map φ) m N _ _
  have hComm : ∀ q : UPoly R,
      (mapHom (Dual.map φ)).toFun ((mapHom Dual.inl).toFun q) =
        (mapHom Dual.inl).toFun ((mapHom φ).toFun q) := fun q => by
    rw [mapHom_comp, mapHom_comp]
    refine mapHom_eq_of_toFun _ _ (fun a => ?_) q
    simp only [RingHom.comp_apply]
    show (⟨φ.toFun a, φ.toFun zero⟩ : Dual S) = ⟨φ.toFun a, zero⟩
    rw [φ.map_zero]
  have hP : (mapHom (Dual.map φ)).toFun (dualPerturb P0 B) =
      dualPerturb ((mapHom φ).toFun P0) ((mapHom φ).toFun B) := by
    unfold dualPerturb
    rw [RingHom.map_add, RingHom.map_mul, mapHom_C, hComm P0, hComm B]
    have hEps : (Dual.map φ).toFun Dual.eps = Dual.eps := by
      show (⟨φ.toFun zero, φ.toFun one⟩ : Dual S) = ⟨zero, one⟩
      rw [φ.map_zero, φ.map_one]
    rw [hEps]
  rw [hComm C1, hP] at h1
  exact congrArg Dual.snd h1

/-- **Key Derivative-Factor Identity**: if `C1 = (X - C ζ) * Q`, `Q.natDeg ≤ m'`, `P0.natDeg ≤ N`,
    `B.natDeg ≤ N`, and `P0.eval ζ = 0`, then
    `sylResDeriv (m' + 1) N C1 P0 B = B.eval ζ * sylRes m' N Q P0`! -/
theorem sylResDeriv_of_factor (m' N : Nat) (ζ : R) (Q P0 B : UPoly R)
    (hQ : Q.natDeg ≤ m') (hP0 : P0.natDeg ≤ N) (hB : B.natDeg ≤ N) (hP0z : P0.eval ζ = zero) :
    sylResDeriv (m' + 1) N (mul (sub X (C ζ)) Q) P0 B = mul (B.eval ζ) (sylRes m' N Q P0) := by
  unfold sylResDeriv
  have hMapC1 : (mapHom (Dual.inl (R := R))).toFun (mul (sub X (C ζ)) Q) =
      mul (sub X (C (Dual.inl.toFun ζ))) ((mapHom Dual.inl).toFun Q) := by
    rw [RingHom.map_mul, RingHom.map_sub, mapHom_C]
    have hX : (mapHom (Dual.inl (R := R))).toFun X = X := mapHom_X _
    rw [hX]
  have hDegQ : ((mapHom (Dual.inl (R := R))).toFun Q).natDeg ≤ m' :=
    Nat.le_trans (natDeg_mapHom_le _ Q) hQ
  have hDegPert : (dualPerturb P0 B).natDeg ≤ N := by
    unfold dualPerturb
    apply natDeg_le_of_coeffAt; intro k hk
    rw [coeffAt_add, coeffAt_C_mul, coeffAt_mapHom, coeffAt_mapHom,
      P0.coeffAt_eq_zero_of_natDeg_lt (by omega), B.coeffAt_eq_zero_of_natDeg_lt (by omega),
      Dual.inl.map_zero, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  rw [hMapC1, sylRes_mul_X_sub m' N (Dual.inl.toFun ζ) _ _ hDegQ hDegPert]
  have hEvalPert : (dualPerturb P0 B).eval (Dual.inl.toFun ζ) = (⟨zero, B.eval ζ⟩ : Dual R) := by
    unfold dualPerturb
    rw [← evalHom_apply]
    rw [RingHom.map_add, RingHom.map_mul, evalHom_apply, evalHom_apply, evalHom_apply,
      eval_C, eval_mapHom, eval_mapHom, hP0z]
    apply Dual.ext
    · show add zero (mul zero (B.eval ζ)) = zero; constructive_ring
    · show add zero (add (mul zero zero) (mul one (B.eval ζ))) = B.eval ζ; constructive_ring
  have hFstInl : ∀ q : UPoly R, (mapHom Dual.fstHom).toFun ((mapHom Dual.inl).toFun q) = q := fun q => by
    rw [mapHom_comp, mapHom_eq_of_toFun (Dual.fstHom.comp Dual.inl) (RingHom.id R) (fun a => by simp only [RingHom.comp_apply, RingHom.id_apply]; rfl) q, mapHom_id]
  have hFstRes : (sylRes m' N ((mapHom Dual.inl).toFun Q) (dualPerturb P0 B)).fst =
      sylRes m' N Q P0 := by
    change Dual.fstHom.toFun (sylRes m' N ((mapHom Dual.inl).toFun Q) (dualPerturb P0 B)) = _
    rw [map_sylRes Dual.fstHom, hFstInl Q]
    have hP1 : (mapHom Dual.fstHom).toFun (dualPerturb P0 B) = P0 := by
      unfold dualPerturb
      rw [RingHom.map_add, RingHom.map_mul, mapHom_C, hFstInl P0, hFstInl B]
      have hEps0 : Dual.fstHom.toFun (Dual.eps (R := R)) = zero := rfl
      have hC0 : (C zero : UPoly R) = zero := C_zero_deriv
      rw [hEps0, hC0, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
    rw [hP1]
  rw [hEvalPert]
  generalize sylRes m' N ((mapHom Dual.inl).toFun Q) (dualPerturb P0 B) = R_dual at hFstRes ⊢
  obtain ⟨r0, r1⟩ := R_dual
  dsimp at hFstRes
  subst hFstRes
  show add (mul zero r1) (mul (B.eval ζ) (sylRes m' N Q P0)) = _
  rw [LawfulCommRing.zero_mul, LawfulCommRing.zero_add]

/-- At ANY common root `ζ` of `(C1, P0)` (`1 ≤ m`), `sylResDeriv m N C1 P0 B = B.eval ζ * sylResDeriv m N C1 P0 1`! -/
theorem sylResDeriv_common_root {m N : Nat} {C1 P0 B : UPoly R} {ζ : R}
    (hm : 1 ≤ m) (hC1 : C1.natDeg ≤ m) (hP0 : P0.natDeg ≤ N) (hB : B.natDeg ≤ N)
    (hC1z : C1.eval ζ = zero) (hP0z : P0.eval ζ = zero) :
    sylResDeriv m N C1 P0 B = mul (B.eval ζ) (sylResDeriv m N C1 P0 one) := by
  obtain ⟨hDiv, hDeg⟩ := divXSub_spec C1 ζ
  rw [hC1z, C_zero_deriv, LawfulCommRing.zero_add] at hDiv
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have h1 : (one : UPoly R).natDeg ≤ N := by rw [natDeg_one]; exact Nat.zero_le N
  have hEval1 : (one : UPoly R).eval ζ = one := by rw [one_eq_C, eval_C]
  rw [hDiv,
    sylResDeriv_of_factor m' N ζ (divXSub C1 ζ) P0 B (by omega) hP0 hB hP0z,
    sylResDeriv_of_factor m' N ζ (divXSub C1 ζ) P0 one (by omega) hP0 h1 hP0z,
    hEval1, LawfulCommRing.one_mul]

private theorem max_le_of_le {a b c : Nat} (ha : a ≤ c) (hb : b ≤ c) : max a b ≤ c := by
  if h : a ≤ b then rw [Nat.max_eq_right h]; exact hb
  else rw [Nat.max_eq_left (by omega)]; exact ha

/-- Weighted `DegFn` bound on `sylResDeriv m N C1 P0 B`. -/
theorem degFn_sylResDeriv_le {w : R → Nat} (hw : DegFn w) (hw1 : w one = 0)
    (m N h_A h_B : Nat) (C1 P0 B : UPoly R)
    (hC1 : C1.wdeg w 1 ≤ h_A) (hP0 : P0.wdeg w 1 ≤ h_B) (hB : B.wdeg w 1 ≤ h_B)
    (hm : m ≤ h_A) (hN : N ≤ h_B) :
    w (sylResDeriv m N C1 P0 B) ≤ h_A * h_B := by
  let wD (x : Dual R) : Nat := max (w x.fst) (w x.snd)
  have hwD : DegFn wD := {
    zero := by
      show max (w zero) (w zero) = 0
      rw [hw.zero, Nat.max_self]
    add_le := fun x y =>
      max_le_of_le
        (Nat.le_trans (hw.add_le x.fst y.fst)
          (max_le_of_le
            (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
            (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))))
        (Nat.le_trans (hw.add_le x.snd y.snd)
          (max_le_of_le
            (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
            (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))))
    mul_le := fun x y => by
      have h1 : w (mul x.fst y.fst) ≤ wD x + wD y :=
        Nat.le_trans (hw.mul_le x.fst y.fst)
          (Nat.add_le_add (Nat.le_max_left _ _) (Nat.le_max_left _ _))
      have h2a : w (mul x.fst y.snd) ≤ wD x + wD y :=
        Nat.le_trans (hw.mul_le x.fst y.snd)
          (Nat.add_le_add (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      have h2b : w (mul x.snd y.fst) ≤ wD x + wD y :=
        Nat.le_trans (hw.mul_le x.snd y.fst)
          (Nat.add_le_add (Nat.le_max_right _ _) (Nat.le_max_left _ _))
      exact max_le_of_le h1
        (Nat.le_trans (hw.add_le _ _) (max_le_of_le h2a h2b))
    neg_le := fun x =>
      max_le_of_le
        (Nat.le_trans (hw.neg_le x.fst) (Nat.le_max_left _ _))
        (Nat.le_trans (hw.neg_le x.snd) (Nat.le_max_right _ _))
  }
  have hwD1 : wD (one : Dual R) = 0 := by
    show max (w one) (w zero) = 0
    rw [hw1, hw.zero]; rfl
  have hC1D : ((mapHom Dual.inl).toFun C1).wdeg wD 1 ≤ h_A := by
    apply wdeg_le; intro k hk
    rw [coeffAt_mapHom] at hk ⊢
    have hcNe : coeffAt C1.coeffs k ≠ zero := fun e => hk (by rw [e]; rfl)
    have hle := Nat.le_trans (le_wdeg w 1 C1 k hcNe) hC1
    show max (w (coeffAt C1.coeffs k)) (w zero) + 1 * k ≤ h_A
    rw [hw.zero, Nat.max_zero]; exact hle
  have hPD : (dualPerturb P0 B).wdeg wD 1 ≤ h_B := by
    apply wdeg_le; intro k hk
    unfold dualPerturb at hk ⊢
    rw [coeffAt_add, coeffAt_C_mul, coeffAt_mapHom, coeffAt_mapHom] at hk ⊢
    have hCoeff : add (Dual.inl.toFun (coeffAt P0.coeffs k))
        (mul Dual.eps (Dual.inl.toFun (coeffAt B.coeffs k))) =
        (⟨coeffAt P0.coeffs k, coeffAt B.coeffs k⟩ : Dual R) := by
      apply Dual.ext
      · show add (coeffAt P0.coeffs k) (mul zero (coeffAt B.coeffs k)) = coeffAt P0.coeffs k
        constructive_ring
      · show add zero (add (mul zero zero) (mul one (coeffAt B.coeffs k))) = coeffAt B.coeffs k
        constructive_ring
    rw [hCoeff] at hk ⊢
    if hkB : k ≤ h_B then
      have hP0k : w (coeffAt P0.coeffs k) ≤ h_B - k := by
        if hz : coeffAt P0.coeffs k = zero then rw [hz, hw.zero]; omega
        else have := Nat.le_trans (le_wdeg w 1 P0 k hz) hP0; omega
      have hBk : w (coeffAt B.coeffs k) ≤ h_B - k := by
        if hz : coeffAt B.coeffs k = zero then rw [hz, hw.zero]; omega
        else have := Nat.le_trans (le_wdeg w 1 B k hz) hB; omega
      have hMax : max (w (coeffAt P0.coeffs k)) (w (coeffAt B.coeffs k)) ≤ h_B - k :=
        max_le_of_le hP0k hBk
      show max (w (coeffAt P0.coeffs k)) (w (coeffAt B.coeffs k)) + 1 * k ≤ h_B
      omega
    else
      exfalso
      have hzP : coeffAt P0.coeffs k = zero := by
        apply Decidable.byContradiction; intro hz
        have := Nat.le_trans (le_wdeg w 1 P0 k hz) hP0; omega
      have hzB : coeffAt B.coeffs k = zero := by
        apply Decidable.byContradiction; intro hz
        have := Nat.le_trans (le_wdeg w 1 B k hz) hB; omega
      rw [hzP, hzB] at hk; exact hk rfl
  have hMain := degFn_sylRes_le hwD hwD1 m N h_A h_B _ _ hC1D hPD hm hN
  exact Nat.le_trans (Nat.le_max_right _ _) hMain

end Deriv
end SylElim

end Qsag

end

section
namespace Qsag

set_option autoImplicit false
open CommRingOps RoundPoly

namespace SylElim

section WdegDiv
variable {R : Type} [LawfulCommRing R] [DecidableEq R]
open UPoly

theorem wdeg_divModLead_rem_le {w : R → Nat} (hw : DegFn w)
    (A : UPoly R) (m T : Nat) (c_inv : R)
    (hm : 1 ≤ m) (hAdeg : A.natDeg ≤ m) (hInv : mul c_inv (coeffAt A.coeffs m) = one)
    (hcinv : w c_inv = 0) (hAw : A.wdeg w 1 ≤ m)
    (P : UPoly R) (hPw : P.wdeg w 1 ≤ T) :
    (divModLead A m c_inv P).2.wdeg w 1 ≤ T := by
  have hwSub : ∀ X Y : UPoly R, X.wdeg w 1 ≤ T → Y.wdeg w 1 ≤ T → (sub X Y).wdeg w 1 ≤ T := by
    intro X Y hX hY
    have hD := UPoly.degFn_wdeg hw 1
    rw [LawfulCommRing.sub_eq_add_neg]
    have h1 := hD.add_le X (neg Y)
    have h2 := Nat.le_trans (hD.neg_le Y) hY
    if hmxy : X.wdeg w 1 ≤ (neg Y).wdeg w 1 then
      rw [Nat.max_eq_right hmxy] at h1; exact Nat.le_trans h1 h2
    else
      rw [Nat.max_eq_left (by omega)] at h1; exact Nat.le_trans h1 hX
  have aux : ∀ (fuel : Nat) (P : UPoly R), P.natDeg < fuel → P.wdeg w 1 ≤ T →
      (divModLeadAux A m c_inv fuel P).2.wdeg w 1 ≤ T := by
    intro fuel; induction fuel with
    | zero => intros _ h _; exfalso; omega
    | succ fuel ih =>
      intro P hFuel hPT
      unfold divModLeadAux
      if hlt : P.natDeg < m then
        rw [ite_pos hlt]; exact hPT
      else
        rw [ite_neg hlt]
        have hP0 : P ≠ zero := fun e => by
          rw [e] at hlt; have : (zero : UPoly R).natDeg = 0 := UPoly.natDeg_zero
          omega
        have hLeadW : w P.lead + 1 * P.natDeg ≤ T :=
          by simpa only [lead_eq] using (Nat.le_trans (le_wdeg w 1 P P.natDeg (by simpa only [lead_eq] using (lead_ne_zero hP0))) hPT)
        let qTop := mul (C (mul (coeffAt P.coeffs P.natDeg) c_inv)) (monom (P.natDeg - m))
        let P' := sub P (mul qTop A)
        have hqTopW : qTop.wdeg w 1 ≤ T - m := by
          apply wdeg_le; intro k hk
          dsimp only [qTop] at hk ⊢
          rw [coeffAt_C_mul, coeffAt_monom] at hk ⊢
          if hEq : k = P.natDeg - m then
            subst hEq; rw [ite_pos rfl, LawfulCommRing.mul_one] at hk ⊢
            have hwMul := hw.mul_le P.lead c_inv
            simp only [lead_eq] at hwMul hLeadW
            rw [hcinv] at hwMul; omega
          else
            rw [ite_neg hEq, LawfulCommRing.mul_zero] at hk; exact absurd rfl hk
        have hMulW : (mul qTop A).wdeg w 1 ≤ T := by
          have h1 := (UPoly.degFn_wdeg hw 1).mul_le qTop A
          omega
        have hCancel : ∀ k, P.natDeg ≤ k → coeffAt P'.coeffs k = zero := by
          intro k hk
          dsimp only [P', qTop]
          have hqA : mul (mul (C (mul (coeffAt P.coeffs P.natDeg) c_inv)) (monom (P.natDeg - m))) A =
              mul (C (mul (coeffAt P.coeffs P.natDeg) c_inv)) (mul (monom (P.natDeg - m)) A) := by
            constructive_ring
          rw [coeffAt_sub, hqA, coeffAt_C_mul, coeffAt_monom_mul, ite_pos (by omega)]
          if hEq : k = P.natDeg then
            subst hEq; rw [show P.natDeg - (P.natDeg - m) = m by omega]
            have h1 : mul (mul (coeffAt P.coeffs P.natDeg) c_inv) (coeffAt A.coeffs m) =
                mul (coeffAt P.coeffs P.natDeg) (mul c_inv (coeffAt A.coeffs m)) := by constructive_ring
            rw [h1, hInv, LawfulCommRing.mul_one, LawfulCommRing.sub_self]
          else
            rw [P.coeffAt_eq_zero_of_natDeg_lt (by omega),
              A.coeffAt_eq_zero_of_natDeg_lt (by omega), LawfulCommRing.mul_zero, LawfulCommRing.sub_self]
        have hDegP' : P'.natDeg < fuel := by
          have hle := natDeg_le_of_coeffAt P' (P.natDeg - 1) fun k hk => hCancel k (by omega)
          omega
        exact ih P' hDegP' (hwSub P (mul qTop A) hPT hMulW)
  exact aux (P.natDeg + 1) P (Nat.lt_succ_self _) hPw

end WdegDiv

/-! ## Monic Quotient Algebra `ModMonic M = R[W]/(M)` -/

structure MonicPoly (R : Type) [LawfulCommRing R] [DecidableEq R] where
  poly : UPoly R
  deg : Nat
  deg_pos : 1 ≤ deg
  natDeg_le : poly.natDeg ≤ deg
  coeff_deg : coeffAt poly.coeffs deg = one

section ModMonicRing
variable {R : Type} [LawfulCommRing R] [DecidableEq R]
open UPoly

def remM (M : MonicPoly R) (P : UPoly R) : UPoly R :=
  (divModLead M.poly M.deg one P).2

def quotM (M : MonicPoly R) (P : UPoly R) : UPoly R :=
  (divModLead M.poly M.deg one P).1

theorem quotM_remM_spec (M : MonicPoly R) (P : UPoly R) :
    P = add (mul (quotM M P) M.poly) (remM M P) ∧ (remM M P).natDeg < M.deg := by
  have hInv : mul (one : R) (coeffAt M.poly.coeffs M.deg) = one := by
    rw [M.coeff_deg, LawfulCommRing.one_mul]
  exact divModLead_spec M.poly M.deg one M.deg_pos M.natDeg_le hInv P

theorem eq_zero_of_mul_monic_lt (M : MonicPoly R) {Q : UPoly R}
    (hLt : (mul Q M.poly).natDeg < M.deg) : Q = zero := by
  apply Decidable.byContradiction; intro hQ0
  let u := Q.natDeg
  have hZero : coeffAt (mul Q M.poly).coeffs (u + M.deg) = zero :=
    (mul Q M.poly).coeffAt_eq_zero_of_natDeg_lt (by omega)
  if hM0 : M.poly = zero then
    have h10 : (one : R) = zero := by
      rw [← M.coeff_deg, hM0, coeffs_zero, coeffAt_nil]
    have hQl : Q.lead = zero := by
      rw [← LawfulCommRing.mul_one Q.lead, h10, LawfulCommRing.mul_zero]
    exact lead_ne_zero hQ0 hQl
  else
    have hMdeg : M.poly.natDeg = M.deg := by
      apply Nat.le_antisymm M.natDeg_le
      apply Decidable.byContradiction; intro hNot
      have hz := M.poly.coeffAt_eq_zero_of_natDeg_lt (Nat.lt_of_not_le hNot)
      rw [M.coeff_deg] at hz
      exact lead_ne_zero hQ0 (by
        rw [← LawfulCommRing.mul_one Q.lead, hz, LawfulCommRing.mul_zero])
    have hTop := (coeffAt_mul_top Q M.poly).2
    simp only [lead_eq] at hTop
    rw [hMdeg, M.coeff_deg, LawfulCommRing.mul_one] at hTop
    rw [hTop] at hZero
    exact lead_ne_zero hQ0 (by simpa only [lead_eq] using hZero)

theorem remM_eq_of_sub_mul (M : MonicPoly R) {P R0 Q : UPoly R}
    (hSub : sub P R0 = mul Q M.poly) (hDeg : R0.natDeg < M.deg) :
    remM M P = R0 := by
  obtain ⟨hDiv, hRemDeg⟩ := quotM_remM_spec M P
  have hDiff : sub (remM M P) R0 = mul (sub Q (quotM M P)) M.poly := by
    have h1 : remM M P = sub P (mul (quotM M P) M.poly) := by
      conv => rhs; lhs; rw [hDiv]
      constructive_ring
    rw [h1]
    have h2 : sub (sub P (mul (quotM M P) M.poly)) R0 =
        sub (sub P R0) (mul (quotM M P) M.poly) := by constructive_ring
    rw [h2, hSub]; constructive_ring
  have hDiffDeg : (mul (sub Q (quotM M P)) M.poly).natDeg < M.deg := by
    rw [← hDiff, LawfulCommRing.sub_eq_add_neg]
    have h1 := natDeg_add_le (remM M P) (neg R0)
    have hNeg : (neg R0).natDeg ≤ R0.natDeg :=
      natDeg_le_of_coeffAt _ _ fun k hk => by
        rw [coeffAt_neg, R0.coeffAt_eq_zero_of_natDeg_lt hk, LawfulCommRing.neg_zero]
    omega
  have hQeq := eq_zero_of_mul_monic_lt M hDiffDeg
  rw [hQeq, LawfulCommRing.zero_mul] at hDiff
  exact LawfulCommRing.sub_eq_zero_iff.mp hDiff

theorem remM_of_lt (M : MonicPoly R) {P : UPoly R} (hP : P.natDeg < M.deg) :
    remM M P = P :=
  remM_eq_of_sub_mul M (Q := zero)
    (by rw [LawfulCommRing.sub_self, LawfulCommRing.zero_mul]) hP

@[ext]
structure ModMonic (M : MonicPoly R) where
  rep : UPoly R
  reduced : rep.natDeg < M.deg

instance (M : MonicPoly R) : DecidableEq (ModMonic M) := fun a b =>
  if h : a.rep = b.rep then isTrue (ModMonic.ext h)
  else isFalse (fun e => h (congrArg ModMonic.rep e))

namespace ModMonic

theorem natDeg_zero_lt (M : MonicPoly R) : (zero : UPoly R).natDeg < M.deg := by
  have : (zero : UPoly R).natDeg = 0 := UPoly.natDeg_zero
  have := M.deg_pos; omega

theorem natDeg_C_lt (M : MonicPoly R) (c : R) : (C c : UPoly R).natDeg < M.deg := by
  have hc0 : (C c : UPoly R).natDeg = 0 :=
    Nat.le_zero.mp (natDeg_le_of_coeffAt _ 0 fun k hk => by
      cases k with
      | zero => omega
      | succ k => exact coeffAt_C_succ c k)
  have := M.deg_pos; omega

theorem natDeg_add_lt (M : MonicPoly R) {a b : UPoly R}
    (ha : a.natDeg < M.deg) (hb : b.natDeg < M.deg) : (add a b).natDeg < M.deg := by
  have h := natDeg_add_le a b; omega

theorem natDeg_neg_lt (M : MonicPoly R) {a : UPoly R}
    (ha : a.natDeg < M.deg) : (neg a).natDeg < M.deg := by
  have h : (neg a).natDeg ≤ a.natDeg :=
    natDeg_le_of_coeffAt _ _ fun k hk => by
      rw [coeffAt_neg, a.coeffAt_eq_zero_of_natDeg_lt hk, LawfulCommRing.neg_zero]
  omega

instance (M : MonicPoly R) : LawfulCommRing (ModMonic M) where
  zero := ⟨zero, natDeg_zero_lt M⟩
  one := ⟨one, by rw [one_eq_C]; exact natDeg_C_lt M one⟩
  add a b := ⟨add a.rep b.rep, natDeg_add_lt M a.reduced b.reduced⟩
  mul a b := ⟨remM M (mul a.rep b.rep), (quotM_remM_spec M _).2⟩
  neg a := ⟨neg a.rep, natDeg_neg_lt M a.reduced⟩
  sub a b := ⟨sub a.rep b.rep, by
    rw [LawfulCommRing.sub_eq_add_neg]
    exact natDeg_add_lt M a.reduced (natDeg_neg_lt M b.reduced)⟩
  add_assoc a b c := by apply ModMonic.ext; exact LawfulCommRing.add_assoc _ _ _
  add_comm a b := by apply ModMonic.ext; exact LawfulCommRing.add_comm _ _
  zero_add a := by apply ModMonic.ext; exact LawfulCommRing.zero_add _
  add_zero a := by apply ModMonic.ext; exact LawfulCommRing.add_zero _
  add_left_neg a := by apply ModMonic.ext; exact LawfulCommRing.add_left_neg _
  sub_eq_add_neg a b := by apply ModMonic.ext; exact LawfulCommRing.sub_eq_add_neg _ _
  mul_comm a b := by apply ModMonic.ext; dsimp; rw [LawfulCommRing.mul_comm]
  one_mul a := by
    apply ModMonic.ext; dsimp
    rw [LawfulCommRing.one_mul, remM_of_lt M a.reduced]
  mul_one a := by
    apply ModMonic.ext; dsimp
    rw [LawfulCommRing.mul_one, remM_of_lt M a.reduced]
  left_distrib a b c := by
    apply ModMonic.ext; dsimp
    rw [LawfulCommRing.left_distrib]
    obtain ⟨hB, hBd⟩ := quotM_remM_spec M (mul a.rep b.rep)
    obtain ⟨hC, hCd⟩ := quotM_remM_spec M (mul a.rep c.rep)
    refine remM_eq_of_sub_mul M (Q := add (quotM M (mul a.rep b.rep)) (quotM M (mul a.rep c.rep)))
      ?_ (natDeg_add_lt M hBd hCd)
    conv => lhs; lhs; rw [hB, hC]
    constructive_ring
  right_distrib a b c := by
    apply ModMonic.ext; dsimp
    rw [LawfulCommRing.right_distrib]
    obtain ⟨hA, hAd⟩ := quotM_remM_spec M (mul a.rep c.rep)
    obtain ⟨hB, hBd⟩ := quotM_remM_spec M (mul b.rep c.rep)
    refine remM_eq_of_sub_mul M (Q := add (quotM M (mul a.rep c.rep)) (quotM M (mul b.rep c.rep)))
      ?_ (natDeg_add_lt M hAd hBd)
    conv => lhs; lhs; rw [hA, hB]
    constructive_ring
  mul_assoc a b c := by
    apply ModMonic.ext; dsimp
    obtain ⟨hAB, _⟩ := quotM_remM_spec M (mul a.rep b.rep)
    obtain ⟨hBC, _⟩ := quotM_remM_spec M (mul b.rep c.rep)
    obtain ⟨hR, hRd⟩ := quotM_remM_spec M (mul a.rep (remM M (mul b.rep c.rep)))
    refine remM_eq_of_sub_mul M
      (Q := sub (add (quotM M (mul a.rep (remM M (mul b.rep c.rep)))) (mul a.rep (quotM M (mul b.rep c.rep))))
        (mul (quotM M (mul a.rep b.rep)) c.rep)) ?_ hRd
    have hEqABC : mul (add (mul (quotM M (mul a.rep b.rep)) M.poly) (remM M (mul a.rep b.rep))) c.rep =
        mul a.rep (add (mul (quotM M (mul b.rep c.rep)) M.poly) (remM M (mul b.rep c.rep))) := by
      rw [← hAB, ← hBC, LawfulCommRing.mul_assoc]
    have hRemEq : mul (remM M (mul a.rep b.rep)) c.rep =
        sub (mul a.rep (add (mul (quotM M (mul b.rep c.rep)) M.poly) (remM M (mul b.rep c.rep))))
          (mul (mul (quotM M (mul a.rep b.rep)) M.poly) c.rep) := by
      rw [← hEqABC]; constructive_ring
    rw [hRemEq]
    have hR' : remM M (mul a.rep (remM M (mul b.rep c.rep))) =
        sub (mul a.rep (remM M (mul b.rep c.rep)))
          (mul (quotM M (mul a.rep (remM M (mul b.rep c.rep)))) M.poly) := by
      conv => rhs; lhs; rw [hR]
      constructive_ring
    conv => lhs; rhs; rw [hR']
    constructive_ring

instance [NontrivialRing R] (M : MonicPoly R) : NontrivialRing (ModMonic M) where
  one_ne_zero h := by
    have hRep : (one : UPoly R) = zero := congrArg ModMonic.rep h
    have hc := congrArg (fun p : UPoly R => coeffAt p.coeffs 0) hRep
    rw [one_eq_C, coeffAt_C_zero, coeffs_zero, coeffAt_nil] at hc
    exact NontrivialRing.one_ne_zero hc

theorem rep_zero (M : MonicPoly R) : (zero : ModMonic M).rep = (zero : UPoly R) := by rfl

def modQuotHom (M : MonicPoly R) : RingHom (UPoly R) (ModMonic M) where
  toFun P := ⟨remM M P, (quotM_remM_spec M P).2⟩
  map_zero := by apply ModMonic.ext; exact remM_of_lt M (natDeg_zero_lt M)
  map_one := by
    apply ModMonic.ext
    exact remM_of_lt M (by rw [one_eq_C]; exact natDeg_C_lt M one)
  map_add A B := by
    apply ModMonic.ext
    change remM M (add A B) = add (remM M A) (remM M B)
    obtain ⟨hA, hAd⟩ := quotM_remM_spec M A
    obtain ⟨hB, hBd⟩ := quotM_remM_spec M B
    refine remM_eq_of_sub_mul M (Q := add (quotM M A) (quotM M B)) ?_ (natDeg_add_lt M hAd hBd)
    conv => lhs; lhs; rw [hA, hB]
    constructive_ring
  map_mul A B := by
    apply ModMonic.ext
    change remM M (mul A B) = remM M (mul (remM M A) (remM M B))
    obtain ⟨hA, _⟩ := quotM_remM_spec M A
    obtain ⟨hB, _⟩ := quotM_remM_spec M B
    obtain ⟨hR, hRd⟩ := quotM_remM_spec M (mul (remM M A) (remM M B))
    refine remM_eq_of_sub_mul M
      (Q := add (add (mul (quotM M A) (mul (quotM M B) M.poly))
          (add (mul (quotM M A) (remM M B)) (mul (remM M A) (quotM M B))))
        (quotM M (mul (remM M A) (remM M B)))) ?_ hRd
    conv => lhs; lhs; rw [hA, hB]
    have hR' : remM M (mul (remM M A) (remM M B)) =
        sub (mul (remM M A) (remM M B))
          (mul (quotM M (mul (remM M A) (remM M B))) M.poly) := by
      conv => rhs; lhs; rw [hR]
      constructive_ring
    conv => lhs; rhs; rw [hR']
    constructive_ring

def modInl (M : MonicPoly R) : RingHom R (ModMonic M) :=
  (modQuotHom M).comp CHom

theorem modInl_inj (M : MonicPoly R) {r : R} (h : (modInl M).toFun r = zero) : r = zero := by
  have hRep : remM M (C r) = zero := by
    simpa only [modInl, RingHom.comp_apply, CHom_apply, modQuotHom, rep_zero] using congrArg ModMonic.rep h
  rw [remM_of_lt M (natDeg_C_lt M r)] at hRep
  have hc := congrArg (fun p : UPoly R => coeffAt p.coeffs 0) hRep
  rwa [coeffAt_C_zero, coeffs_zero, coeffAt_nil] at hc

def modGen (M : MonicPoly R) : ModMonic M :=
  (modQuotHom M).toFun X

theorem eval_mapHom_modInl (M : MonicPoly R) (P : UPoly R) :
    ((mapHom (modInl M)).toFun P).eval (modGen M) = (modQuotHom M).toFun P := by
  show eval₂ (RingHom.id _) (modGen M) ((mapHom (modInl M)).toFun P) = _
  rw [eval₂_mapHom]
  have hEqFun : ∀ c : R, ((RingHom.id (ModMonic M)).comp (modInl M)).toFun c =
      ((modQuotHom M).comp CHom).toFun c := fun c => by simp only [RingHom.comp_apply, RingHom.id_apply, modInl]
  show evalCoeffs (P.coeffs.map ((RingHom.id (ModMonic M)).comp (modInl M)).toFun) (modGen M) = _
  have hMap : P.coeffs.map ((RingHom.id (ModMonic M)).comp (modInl M)).toFun =
      P.coeffs.map ((modQuotHom M).comp CHom).toFun := List.map_congr_left fun c _ => hEqFun c
  rw [hMap]
  change eval₂ ((modQuotHom M).comp CHom) ((modQuotHom M).toFun X) P = (modQuotHom M).toFun P
  have hIdP : P = eval₂ CHom X P := by
    conv => lhs; rw [← ofList_coeffs P]
    change ofList P.coeffs = evalCoeffs (P.coeffs.map CHom.toFun) X
    generalize P.coeffs = l
    induction l with
    | nil => rfl
    | cons c cs ih =>
      simp only [List.map_cons, evalCoeffs, CHom_apply]
      show ofList (c :: cs) = add (C c) (mul X _)
      rw [ofList_cons, ← ih]
  conv => rhs; rw [hIdP]
  exact (hom_eval₂ (modQuotHom M) CHom X P).symm

theorem modQuotHom_self_eq_zero (M : MonicPoly R) : (modQuotHom M).toFun M.poly = zero := by
  apply ModMonic.ext
  change remM M M.poly = zero
  exact remM_eq_of_sub_mul M (Q := one)
    (by rw [LawfulCommRing.sub_zero, LawfulCommRing.one_mul]) (natDeg_zero_lt M)

theorem eval_modGen_eq_zero (M : MonicPoly R) :
    ((mapHom (modInl M)).toFun M.poly).eval (modGen M) = zero := by
  rw [eval_mapHom_modInl, modQuotHom_self_eq_zero]

end ModMonic

/-! ## `d_G ≥ 2` Common-Factor Vanishing of `sylResDeriv` -/

theorem sylResDeriv_eq_zero_of_common_factor_ge_two {m N d_G : Nat}
    {C1 P0 G Q_C Q_P : UPoly R}
    (hdG : 2 ≤ d_G) (hdGm : d_G ≤ m) (hP0 : P0.natDeg ≤ N)
    (hGdeg : G.natDeg ≤ d_G) (hGmon : coeffAt G.coeffs d_G = one)
    (hC1fac : C1 = mul G Q_C) (hQCdeg : Q_C.natDeg ≤ m - d_G)
    (hP0fac : P0 = mul G Q_P) :
    sylResDeriv m N C1 P0 one = zero := by
  let M1 : MonicPoly R := ⟨G, d_G, by omega, hGdeg, hGmon⟩
  let φ1 := ModMonic.modInl M1
  let T1 := ModMonic.modGen M1
  let G_1 := (mapHom φ1).toFun G
  have hG1root : G_1.eval T1 = zero := ModMonic.eval_modGen_eq_zero M1
  obtain ⟨hG1div, hG1deg_raw⟩ := divXSub_spec G_1 T1
  have hC0_1 : (C (zero : ModMonic M1) : UPoly (ModMonic M1)) = zero := by
    rw [← CHom_apply]; exact CHom.map_zero
  rw [hG1root, hC0_1, LawfulCommRing.zero_add] at hG1div
  let G1 := divXSub G_1 T1
  have hG1_le : G1.natDeg ≤ d_G - 1 := by
    have hmap : G_1.natDeg ≤ G.natDeg := natDeg_mapHom_le φ1 G
    change (divXSub G_1 T1).natDeg ≤ d_G - 1
    omega
  have hG1_mon : coeffAt G1.coeffs (d_G - 1) = one := by
    have hTop : coeffAt G_1.coeffs d_G = one := by
      dsimp only [G_1]; rw [coeffAt_mapHom, hGmon, φ1.map_one]
    have hExpand : mul (sub X (C T1)) G1 = sub (mul X G1) (mul (C T1) G1) := by constructive_ring
    obtain ⟨d', hd'⟩ : ∃ d', d_G = d' + 1 := ⟨d_G - 1, by omega⟩
    rw [hG1div, hExpand, hd', coeffAt_sub, coeffAt_X_mul_succ, coeffAt_C_mul,
      G1.coeffAt_eq_zero_of_natDeg_lt (k := d' + 1) (by omega), LawfulCommRing.mul_zero,
      LawfulCommRing.sub_zero] at hTop
    rwa [show d_G - 1 = d' by omega]
  let C1_1 := (mapHom φ1).toFun C1
  let P0_1 := (mapHom φ1).toFun P0
  let QC_1 := (mapHom φ1).toFun Q_C
  let QP_1 := (mapHom φ1).toFun Q_P
  have hC1_1_eq : C1_1 = mul (sub X (C T1)) (mul G1 QC_1) := by
    dsimp only [C1_1, QC_1]
    rw [hC1fac, RingHom.map_mul]; change mul G_1 QC_1 = _
    rw [hG1div, LawfulCommRing.mul_assoc]
  have hP0_1_root : P0_1.eval T1 = zero := by
    dsimp only [P0_1]
    rw [hP0fac, RingHom.map_mul]; rw [← evalHom_apply]
    rw [RingHom.map_mul, evalHom_apply, hG1root, LawfulCommRing.zero_mul]
  have hG1QC_deg : (mul G1 QC_1).natDeg ≤ m - 1 := by
    have h1 := natDeg_mul_le G1 QC_1
    have h2 : QC_1.natDeg ≤ Q_C.natDeg := natDeg_mapHom_le φ1 Q_C
    omega
  have hP0_1_deg : P0_1.natDeg ≤ N := Nat.le_trans (natDeg_mapHom_le φ1 P0) hP0
  have hOne_deg : (one : UPoly (ModMonic M1)).natDeg ≤ N := by
    rw [natDeg_one]; exact Nat.zero_le N
  have hStep1 : φ1.toFun (sylResDeriv m N C1 P0 one) = sylRes (m - 1) N (mul G1 QC_1) P0_1 := by
    rw [map_sylResDeriv φ1, RingHom.map_one]
    change sylResDeriv m N C1_1 P0_1 one = _
    obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [hm', show m' + 1 - 1 = m' by omega] at hG1QC_deg ⊢
    rw [hC1_1_eq, sylResDeriv_of_factor m' N T1 (mul G1 QC_1) P0_1 one hG1QC_deg hP0_1_deg hOne_deg hP0_1_root,
      one_eq_C, eval_C, LawfulCommRing.one_mul]
  let M2 : MonicPoly (ModMonic M1) := ⟨G1, d_G - 1, by omega, hG1_le, hG1_mon⟩
  let φ2 := ModMonic.modInl M2
  let T2 := ModMonic.modGen M2
  have hG1_2_root : ((mapHom φ2).toFun G1).eval T2 = zero := ModMonic.eval_modGen_eq_zero M2
  have hStep2 : φ2.toFun (sylRes (m - 1) N (mul G1 QC_1) P0_1) = zero := by
    rw [map_sylRes φ2]
    refine sylRes_eq_zero_of_common_root (ζ := T2) (by omega)
      (Nat.le_trans (natDeg_mapHom_le φ2 _) hG1QC_deg)
      (Nat.le_trans (natDeg_mapHom_le φ2 _) hP0_1_deg) ?_ ?_
    · rw [RingHom.map_mul]; rw [← evalHom_apply]
      rw [RingHom.map_mul, evalHom_apply, hG1_2_root, LawfulCommRing.zero_mul]
    · dsimp only [P0_1]
      rw [hP0fac, RingHom.map_mul]; change ((mapHom φ2).toFun (mul G_1 QP_1)).eval T2 = zero
      rw [hG1div, RingHom.map_mul, RingHom.map_mul]
      rw [← evalHom_apply]
      rw [RingHom.map_mul, RingHom.map_mul, evalHom_apply T2 ((mapHom φ2).toFun G1), hG1_2_root,
        LawfulCommRing.mul_zero, LawfulCommRing.zero_mul]
  apply ModMonic.modInl_inj M1
  apply ModMonic.modInl_inj M2
  rw [hStep1, hStep2]

/-! ## Polynomial coordinates for common roots -/

/-- Homogeneous evaluation padded to degree `l.length`. The extra denominator factor
keeps the recursion uniform, including the zero and constant polynomials. -/
def homEvalCoeffs (a b : R) : List R → R
  | [] => zero
  | c :: cs => add (mul c (CRing.npow b (cs.length + 1))) (mul a (homEvalCoeffs a b cs))

omit [DecidableEq R] in
/-- Clearing denominators uses a polynomial identity, so it also holds in quotient rings. -/
theorem homEvalCoeffs_mul (z b : R) : ∀ l : List R,
    homEvalCoeffs (mul z b) b l = mul (CRing.npow b l.length) (evalCoeffs l z)
  | [] => by
    show zero = mul one zero
    rw [LawfulCommRing.mul_zero]
  | c :: cs => by
    simp only [homEvalCoeffs, List.length_cons]
    rw [homEvalCoeffs_mul z b cs]
    show add (mul c (mul (CRing.npow b cs.length) b))
      (mul (mul z b) (mul (CRing.npow b cs.length) (evalCoeffs cs z))) =
      mul (mul (CRing.npow b cs.length) b) (add c (mul z (evalCoeffs cs z)))
    constructive_ring

omit [DecidableEq R] in
theorem map_homEvalCoeffs {S : Type} [LawfulCommRing S]
    (φ : RingHom R S) (a b : R) : ∀ l : List R,
    φ.toFun (homEvalCoeffs a b l) = homEvalCoeffs (φ.toFun a) (φ.toFun b) (l.map φ.toFun)
  | [] => φ.map_zero
  | c :: cs => by
    simp only [homEvalCoeffs, List.map_cons, List.length_map]
    rw [φ.map_add, φ.map_mul, φ.map_mul, RingHom.map_npow, map_homEvalCoeffs φ a b cs]

/-- Naturality plus denominator clearing; normalization of mapped coefficient lists is unnecessary. -/
theorem homEvalCoeffs_map_root {S : Type} [LawfulCommRing S]
    (φ : RingHom R S) (a b : R) (z : S) (h : φ.toFun a = mul z (φ.toFun b)) (P : UPoly R) :
    φ.toFun (homEvalCoeffs a b P.coeffs) =
      mul (CRing.npow (φ.toFun b) P.coeffs.length) (eval₂ φ z P) := by
  rw [map_homEvalCoeffs, h, homEvalCoeffs_mul, List.length_map]
  rfl

/-- Clearing an invertible denominator preserves precisely the zero constraints,
even when the target quotient has zero divisors. -/
theorem homEvalCoeffs_map_zero_iff {S : Type} [LawfulCommRing S]
    (φ : RingHom R S) (a b : R) (z b_inv : S)
    (hcoord : φ.toFun a = mul z (φ.toFun b)) (hunit : mul b_inv (φ.toFun b) = one)
    (P : UPoly R) :
    φ.toFun (homEvalCoeffs a b P.coeffs) = zero ↔ eval₂ φ z P = zero := by
  have hpow : ∀ n, mul (CRing.npow b_inv n) (CRing.npow (φ.toFun b) n) = one := by
    intro n; induction n with
    | zero => exact LawfulCommRing.one_mul one
    | succ n ih =>
      have hEq : mul (mul (CRing.npow b_inv n) b_inv) (mul (CRing.npow (φ.toFun b) n) (φ.toFun b)) =
          mul (mul (CRing.npow b_inv n) (CRing.npow (φ.toFun b) n)) (mul b_inv (φ.toFun b)) := by
        constructive_ring
      change mul (mul (CRing.npow b_inv n) b_inv) (mul (CRing.npow (φ.toFun b) n) (φ.toFun b)) = one
      rw [hEq, ih, hunit, LawfulCommRing.one_mul]
  rw [homEvalCoeffs_map_root φ a b z hcoord P]
  constructor
  · intro h
    have hcancel := congrArg (mul (CRing.npow b_inv P.coeffs.length)) h
    rwa [← LawfulCommRing.mul_assoc, hpow, LawfulCommRing.one_mul,
      LawfulCommRing.mul_zero] at hcancel
  · intro h
    rw [h, LawfulCommRing.mul_zero]

omit [DecidableEq R] in
/-- Degree control depends only on the input coefficients and the two resultant coordinates. -/
theorem degFn_homEvalCoeffs_le {w : R → Nat} (hw : DegFn w) (hw1 : w one = 0)
    (a b : R) (A B : Nat) (ha : w a ≤ B) (hb : w b ≤ B) :
    ∀ l : List R, (∀ c ∈ l, w c ≤ A) → w (homEvalCoeffs a b l) ≤ A + l.length * B
  | [], _ => by show w zero ≤ A + 0 * B; rw [hw.zero]; omega
  | c :: cs, hc => by
    have hhead := hc c (.head _)
    have htail := degFn_homEvalCoeffs_le hw hw1 a b A B ha hb cs (fun x hx => hc x (.tail _ hx))
    have hpow := degFn_npow_le hw hw1 b B hb (cs.length + 1)
    have hleft := hw.mul_le c (CRing.npow b (cs.length + 1))
    have hright := hw.mul_le a (homEvalCoeffs a b cs)
    have hadd := hw.add_le (mul c (CRing.npow b (cs.length + 1))) (mul a (homEvalCoeffs a b cs))
    change w (add (mul c (CRing.npow b (cs.length + 1))) (mul a (homEvalCoeffs a b cs))) ≤ _
    rw [List.length_cons, Nat.succ_mul]
    rw [Nat.succ_mul] at hpow
    omega

/-- Weighted polynomial-degree form of the denominator-clearing bound. -/
theorem degFn_homEvalCoeffs_poly_le {w : R → Nat} (hw : DegFn w) (hw1 : w one = 0)
    (a b : R) (B : Nat) (ha : w a ≤ B) (hb : w b ≤ B) (P : UPoly R) :
    w (homEvalCoeffs a b P.coeffs) ≤ P.wdeg w 1 + (P.natDeg + 1) * B := by
  have hc : ∀ c ∈ P.coeffs, w c ≤ P.wdeg w 1 := by
    intro c hmem
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hmem
    have hget : coeffAt P.coeffs k = c := by simp [coeffAt_eq_getD, List.getD, hk]
    if h0 : c = zero then rw [h0, hw.zero]; exact Nat.zero_le _
    else
      have hne : coeffAt P.coeffs k ≠ zero := by rwa [hget]
      have hdeg := le_wdeg w 1 P k hne
      rw [hget] at hdeg
      omega
  have hlen : P.coeffs.length ≤ P.natDeg + 1 := by unfold natDeg; omega
  exact Nat.le_trans (degFn_homEvalCoeffs_le hw hw1 a b _ B ha hb P.coeffs hc)
    (Nat.add_le_add_left (Nat.mul_le_mul_right B hlen) _)

/-- At a common root, the two derivative resultants are homogeneous coordinates for it. -/
theorem sylResDeriv_X_common_root {m N : Nat} {C1 P0 : UPoly R} {z : R}
    (hm : 1 ≤ m) (hN : 1 ≤ N) (hC : C1.natDeg ≤ m) (hP : P0.natDeg ≤ N)
    (hCz : C1.eval z = zero) (hPz : P0.eval z = zero) :
    sylResDeriv m N C1 P0 X = mul z (sylResDeriv m N C1 P0 one) := by
  have hX : (X : UPoly R).natDeg ≤ N := by
    apply Nat.le_trans (m := 1) ?_ hN
    apply natDeg_le_of_coeffAt
    intro k hk
    cases k with
    | zero => omega
    | succ k => cases k with
      | zero => omega
      | succ k =>
        show coeffAt (ofList [zero, one]).coeffs (k + 2) = zero
        rw [coeffAt_ofList, coeffAt_cons_succ, coeffAt_cons_succ, coeffAt_nil]
  have h := sylResDeriv_common_root hm hC hP hX hCz hPz
  rwa [eval_X] at h

/-- The homogeneous root coordinates commute with coefficient specialization. -/
theorem sylResDeriv_X_mapped_common_root {S : Type} [LawfulCommRing S] [DecidableEq S]
    (φ : RingHom R S) {m N : Nat} {C1 P0 : UPoly R} {z : S}
    (hm : 1 ≤ m) (hN : 1 ≤ N) (hC : C1.natDeg ≤ m) (hP : P0.natDeg ≤ N)
    (hCz : ((mapHom φ).toFun C1).eval z = zero)
    (hPz : ((mapHom φ).toFun P0).eval z = zero) :
    φ.toFun (sylResDeriv m N C1 P0 X) = mul z (φ.toFun (sylResDeriv m N C1 P0 one)) := by
  rw [map_sylResDeriv, map_sylResDeriv, mapHom_X, RingHom.map_one]
  exact sylResDeriv_X_common_root hm hN (Nat.le_trans (natDeg_mapHom_le φ C1) hC)
    (Nat.le_trans (natDeg_mapHom_le φ P0) hP) hCz hPz

/-- All polynomial constraints can be pulled back with an explicit polynomial denominator. -/
theorem homEvalCoeffs_resultant_root {m N : Nat} {C1 P0 P : UPoly R} {z : R}
    (hm : 1 ≤ m) (hN : 1 ≤ N) (hC : C1.natDeg ≤ m) (hP : P0.natDeg ≤ N)
    (hCz : C1.eval z = zero) (hPz : P0.eval z = zero) :
    homEvalCoeffs (sylResDeriv m N C1 P0 X) (sylResDeriv m N C1 P0 one) P.coeffs =
      mul (CRing.npow (sylResDeriv m N C1 P0 one) P.coeffs.length) (P.eval z) := by
  rw [sylResDeriv_X_common_root hm hN hC hP hCz hPz, homEvalCoeffs_mul, UPoly.eval_eq]

/-- The derivative-zero locus is the only possible ambiguity in the projected root. -/
theorem common_root_unique_of_sylResDeriv_ne_zero [NoZeroDivisors R]
    {m N : Nat} {C1 P0 : UPoly R} {z z' : R}
    (hm : 1 ≤ m) (hN : 1 ≤ N) (hC : C1.natDeg ≤ m) (hP : P0.natDeg ≤ N)
    (hCz : C1.eval z = zero) (hPz : P0.eval z = zero)
    (hCz' : C1.eval z' = zero) (hPz' : P0.eval z' = zero)
    (hDeriv : sylResDeriv m N C1 P0 one ≠ zero) : z = z' :=
  mul_right_cancel' hDeriv ((sylResDeriv_X_common_root hm hN hC hP hCz hPz).symm.trans
    (sylResDeriv_X_common_root hm hN hC hP hCz' hPz'))

end ModMonicRing
end SylElim

end Qsag

end

section
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
  (UPoly.C_mul_eq a b).symm

theorem C_zero_eq {R : Type} [LawfulCommRing R] [DecidableEq R] :
    (C (zero : R) : UPoly R) = zero :=
  UPoly.C_zero_eq

/-! ## Total-degree additivity via homogenization `P(Y, Z) ↦ P(T, X·T)` -/

abbrev c2 (P : Poly2 E) (i d : Nat) : E :=
  coeffAt (coeffAt P.coeffs d).coeffs i

theorem c2_zero (i d : Nat) : c2 (zero : Poly2 E) i d = zero := by
  unfold c2
  rw [coeffs_zero]
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
    simp only [List.map_cons, RingHom.comp_apply, CHom_apply, evalCoeffs]
    show c2 (add (C (C c)) (mul X (evalCoeffs _ X))) j d = _
    rw [c2_add]
    cases d with
    | zero =>
      rw [c2_X_mul_zero, LawfulCommRing.add_zero]
      show coeffAt (coeffAt (C (C c)).coeffs 0).coeffs j = _
      rw [coeffAt_C_zero]
      cases j with
      | zero => rw [coeffAt_C_zero, coeffAt_cons_zero]; rfl
      | succ j => rw [coeffAt_C_succ]; rfl
    | succ d =>
      have hCC0 : c2 (C (C c) : Poly2 E) j (d + 1) = zero := by
        show coeffAt (coeffAt (C (C c)).coeffs (d + 1)).coeffs j = zero
        rw [coeffAt_C_succ, coeffs_zero, coeffAt_nil]
      rw [hCC0, LawfulCommRing.zero_add, c2_X_mul_succ, c2_innerHom_eval tl j d]
      cases j <;> simp only [coeffAt_cons_succ, Nat.succ_ne_zero, reduceIte]

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
      by simpa only [innerHom, eval₂Hom_apply, eval₂] using c2_innerHom_eval (E := E) q.coeffs j d
    rw [hq]
    cases j with
    | zero =>
      rw [c2_CX_mul_zero, LawfulCommRing.add_zero]
      simp only [coeffAt_cons_zero, Nat.zero_le, Nat.sub_zero, reduceIte]
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
  by simpa only [homogHom, eval₂Hom_apply, eval₂, c2] using c2_homog_eval (E := E) P.coeffs j d

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
      exact hlead (by simpa only [lead_eq, c2, i] using hz2)

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
    have hc0 : (zero : UPoly E).natDeg = 0 := UPoly.natDeg_zero
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

