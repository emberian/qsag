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

