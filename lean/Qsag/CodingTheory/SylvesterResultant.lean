module
/-
# Qsag.CodingTheory.SylvesterResultant — constructive elimination of `Z` with a degree bound

For `A, B ∈ K[Y][Z]` over a field, `eliminant A B = (u, v, r)` satisfies the Bézout
identity `u·A + v·B = r ∈ K[Y]` with `deg r ≤ deg_{Y,Z} A · deg_{Y,Z} B`, and `r ≠ 0` exactly
when `A` and `B` are coprime over `K(Y)`. Common zeros project to roots of `r`.

The cofactors are found by Gaussian elimination over `K`, in the graded pieces that the
Sylvester matrix acts on: `u` ranges over polynomials with `deg_Z u < deg_Z B` and total
degree at most `T - deg A`, `v` symmetrically, and the equations kill every `Z^k`, `k ≥ 1`,
coefficient of `u·A + v·B`. There is exactly one more unknown than equations when
`T = deg_Z B · deg A + deg_Z A · (deg B - deg_Z B)`. `r` generates the same degree bound as
the Sylvester determinant; equality with that determinant is not claimed here.
-/

public import Qsag.CodingTheory.PolyMv3
import all Qsag.CodingTheory.PolyMv3
public import Qsag.AffineProximityGaps
import all Qsag.AffineProximityGaps

public section
namespace Qsag

set_option autoImplicit false

open CommRingOps RoundPoly UPoly

/-! ## Triangular index sets -/

/-- `Σ_{j<n} f j`. -/
def sumTo (f : Nat → Nat) : Nat → Nat
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
    rw [coeff2_zero]; cases gs <;> rfl
  | _ :: _, [] => coeff2_zero i k
  | x :: xs, g :: gs => by
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
private theorem dotVec_zero_left : ∀ (row xs : List K), (∀ r ∈ row, r = zero) →
    dotVec row xs = zero
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | r :: row, x :: xs, h => by
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
            (fun g => coeff2 g p.1 p.2)) xs) = zero := h0
      rw [hz, coeff2_mono_self, LawfulCommRing.one_mul, LawfulCommRing.add_zero] at h1
      exact h1
    cases hc with
    | head => exact hx
    | tail _ hc' =>
      refine eq_zero_of_lincomb_mono ps xs hp.2 (by simpa using hl) (fun i j => ?_) c hc'
      have h1 : add (mul (coeff2 (mono (K := K) p.1 p.2) i j) x)
          (dotVec ((ps.map (fun q => mono (K := K) q.1 q.2)).map (fun g => coeff2 g i j)) xs)
          = zero := h i j
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
    have := le_wdeg UPoly.natDeg 1 P P.natDeg (lead_ne_zero h)
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
      exact absurd (lincomb_nil _) hu
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

private theorem exists_ne_zero_of_ne_zero {p : UPoly K} (h : p ≠ zero) :
    ∃ c ∈ p.coeffs, c ≠ zero := by
  have hl := lead_ne_zero h
  have hlen : p.natDeg < p.coeffs.length := by
    have : p.coeffs ≠ [] := fun e => h ((eq_zero_iff p).mpr e)
    have := List.length_pos_iff.mpr this
    show p.coeffs.length - 1 < _; omega
  refine ⟨p.coeffs[p.natDeg], List.getElem_mem hlen, ?_⟩
  have : coeffAt p.coeffs p.natDeg = p.coeffs[p.natDeg] := by
    show p.coeffs.getD p.natDeg zero = _
    simp [List.getD, hlen]
  rw [← this]; exact hl

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

namespace Poly2.Tests
open Poly2

def g (n : Nat) : Goldilocks := Goldilocks.ofNat n

/-- `A = Z² - Y` and `B = Z - 1`, meeting only at `(1, 1)`. -/
def pA : Poly2 Goldilocks := ofList [ofList [g 0, neg (g 1)], zero, one]
def pB : Poly2 Goldilocks := ofList [ofList [neg (g 1)], one]

/-- `Z - Y`, which shares the whole diagonal with itself. -/
def pDiag : Poly2 Goldilocks := ofList [ofList [g 0, neg (g 1)], one]

/-- The computed eliminant of `Z² - Y` and `Z - 1` is a nonzero linear polynomial vanishing
    at `Y = 1`: the Gaussian solve, the Bézout identity and the degree budget all execute. -/
theorem resZ_parabola_line :
    resZ pA pB ≠ zero ∧ (resZ pA pB).natDeg = 1 ∧ (resZ pA pB).eval (g 1) = zero ∧
      add (mul (eliminant pA pB).1 pA) (mul (eliminant pA pB).2.1 pB) = C (resZ pA pB) := by
  decide +kernel

/-- The hypotheses of `common_roots_card_le_mul_deg` are jointly satisfiable:
    `1·A - (Z + 1)·B = 1 - Y` certifies coprimality and `(1, 1)` is a common zero. -/
theorem inhabited_common_roots :
    ∃ (A B : Poly2 Goldilocks) (pts : List (Goldilocks × Goldilocks)),
      1 ≤ A.natDeg ∧ B ≠ zero ∧ CoprimeZ A B ∧ (pts.map Prod.fst).Nodup ∧
      (∀ p ∈ pts, A.eval2 p.1 p.2 = zero ∧ B.eval2 p.1 p.2 = zero) ∧ pts.length = 1 :=
  ⟨pA, pB, [(g 1, g 1)], by decide, by decide,
    ⟨one, ofList [ofList [neg (g 1)], ofList [neg (g 1)]], ofList [g 1, neg (g 1)],
      by decide, by decide +kernel⟩, by decide, by decide, rfl⟩

/-- Without coprimality the bound fails: `Z - Y` and itself share two points with distinct
    ordinates, more than `1 · 1`. -/
theorem tooth_common_roots_needs_coprime :
    ∃ (A B : Poly2 Goldilocks) (pts : List (Goldilocks × Goldilocks)),
      1 ≤ A.natDeg ∧ B ≠ zero ∧ (pts.map Prod.fst).Nodup ∧
      (∀ p ∈ pts, A.eval2 p.1 p.2 = zero ∧ B.eval2 p.1 p.2 = zero) ∧
      ¬ pts.length ≤ tdeg A * tdeg B :=
  ⟨pDiag, pDiag, [(g 0, g 0), (g 1, g 1)], by decide, by decide, by decide, by decide,
    by decide⟩

#verify_constructive eliminant_bezout natDeg_resZ_le resZ_ne_zero_iff eval_resZ_eq_zero
#verify_constructive common_roots_card_le_mul_deg resZ_parabola_line
#tooth_pair common_roots_card_le_mul_deg vs tooth_common_roots_needs_coprime
#verify_inhabited common_roots_card_le_mul_deg inhabited_common_roots

end Poly2.Tests

end Qsag
end
