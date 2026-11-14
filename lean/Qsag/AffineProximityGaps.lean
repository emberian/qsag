module
/-
# Qsag.AffineProximityGaps — Constructive Affine Combiners for Reed–Solomon Proximity Gaps (`ia.cr/2026/2863`)

Self-contained constructive (`0` classical choice axioms, `0` external math libraries, `0` unproved goals)
Lean 4.35 mechanization of `[CWYZ26]` (*Affine Combiners for Reed–Solomon Proximity Gaps*,
Chiesa–Weissenberg–Yogev–Zheng, IACR ePrint `2026/2863`):

1. **§1. Constructive `LawfulField`, `+1` Fold Degree-Overflow Invariant & 2-Point Affine Pruning (`Tier 1A`)**:
   - `LawfulField F` (constructive multiplicative inverses over `LawfulCommRing F`, deriving `NoZeroDivisors F`),
     instantiated for `Goldilocks` and `GoldilocksExt2` (and `QuarticGoldilocks` in `ConcreteSecurityBudget`).
   - `affine_fold_degree_le_pow2_add_one`: proves $d_0 = 2^\ell - 1,\ d_{j+1} = \lfloor d_j / 2 \rfloor + 1 \implies
     d_s \le 2^{\ell - s} + 1$ for all $s \le \ell$, establishing that equal-degree affine folding (`Theorem 5.1`)
     accumulates **at most `2` overflow monomials** across arbitrarily many binary folding steps.
   - `affine_line_unique_of_two_points`, `affine_duet_roots_le_card`, and
     `committed_polynomial_pair_bad_lines_le_choose2` (`≤ D.length * (D.length - 1) / 2` bad pairs in `S × S`).

2. **§2. Constructive `#tooth` Lower-Bound Separation Witnesses (`Propositions 6.1 & 6.2`)**:
   - `tooth_scalar_combiner_linear_n_over_q_floor`: proves scalar combiners $f + \alpha g$ suffer at least
     `1 + (D.length - A) / (s + 1)` exceptional challenges even with $s$-coordinate agreement loss.
   - `tooth_affine_combiner_zero_loss_linear_floor`: proves affine combiners $f + (\alpha + \beta x) g$ with
     **zero** agreement loss ($s = 0$) suffer `(D.length - A + 1) * |S \ {0}|` exceptional challenge pairs,
     while `(F = 0, G = 0)` succeeds at $s = 1$, certifying that $s = 1$ loss is strictly necessary.

3. **§3–§4. Elementary Constructive Welch–Berlekamp Affine Proximity-Gap Theorem (`Tier 1B`, $\delta < (1 - \rho)/3$)**:
   - Primitive-recursion homogeneous linear solver `gauss_nullspace_witness` over `[LawfulField F] [DecidableEq F]`.
   - Canonical trimmed univariate polynomial arithmetic, `exists_nonroot_of_trim_ne_nil`, Euclidean division
     `polyDivMod`, and `polyGcd` (`0` Bezout / `0` algebraic closure / `0` classical choice).
   - 3-way $\deg \tilde{Q}_1$ split proving `welch_berlekamp_affine_proximity_gap`:
     `badPairs.length ≤ Nat.max S.length (D.length * (D.length - 1) / 2)` whenever `2 * D.length < 3 * A - d - 1`.

4. **§5. Finite `Theorem 4.8 + Theorem 5.1` Witness Verifier for `Hem` WHIR (`nv = 20` & `nv = 24`)**:
   - `WhirAffineWitness`, `checkWhirAffineWitness` (verifying `M ≥ 1`, exact Equation `(4.5)` interpolation
     dimension inequality, `B^2 > n_f * (d_f + 1)`, `(A - 1)^2 > n_f * d_f`, and $s_i$-loss query target bits),
     and `whirAffineEqualDegreeCommitFoldNum` certified by kernel `decide` across all stages of `nv = 20` and `nv = 24`.
-/

public import Qsag.Constructive
public import Qsag.Goldilocks
import all Qsag.Goldilocks

public section
namespace Qsag

set_option autoImplicit false
set_option exponentiation.threshold 2048

/-! ## §1. Constructive `LawfulField`, Fold Degree Invariant & 2-Point Affine Vandermonde Pruning -/

/-- Constructive field typeclass extending `LawfulCommRing F` with an explicit total inverse `inv`
    satisfying `a * inv a = 1` for `a ≠ 0`. -/
class LawfulField (F : Type) extends LawfulCommRing F where
  inv : F → F
  zero_ne_one : CommRingOps.zero ≠ CommRingOps.one
  mul_inv_cancel : ∀ {a : F}, a ≠ CommRingOps.zero →
    CommRingOps.mul a (inv a) = CommRingOps.one

namespace LawfulField
variable {F : Type} [LawfulField F]
open CommRingOps

theorem inv_mul_cancel {a : F} (ha : a ≠ zero) : mul (inv a) a = one := by
  rw [LawfulCommRing.mul_comm, mul_inv_cancel ha]

theorem one_ne_zero : (one : F) ≠ zero :=
  fun h => zero_ne_one h.symm

theorem mul_eq_zero {a b : F} [DecidableEq F]
    (h : mul a b = zero) : a = zero ∨ b = zero := by
  if ha : a = zero then
    exact .inl ha
  else
    right
    have hmul := congrArg (mul (inv a)) h
    rw [LawfulCommRing.mul_zero, ← LawfulCommRing.mul_assoc,
        inv_mul_cancel ha, LawfulCommRing.one_mul] at hmul
    exact hmul

/-- Constructive `NoZeroDivisors F` dictionary derived from `LawfulField F` without creating
    global typeclass diamonds against concrete rings that already register `NoZeroDivisors`. -/
def toNoZeroDivisors (F : Type) [LawfulField F] [DecidableEq F] : NoZeroDivisors F where
  eq_zero_or_eq_zero_of_mul_eq_zero := mul_eq_zero

end LawfulField

instance : LawfulField Goldilocks where
  inv := Goldilocks.inv
  zero_ne_one := by decide
  mul_inv_cancel := Goldilocks.mul_inv_cancel

instance : LawfulField GoldilocksExt2 where
  inv := GoldilocksExt2.inv
  zero_ne_one := by decide
  mul_inv_cancel := GoldilocksExt2.mul_inv_cancel

/-- One step of equal-degree affine binary folding (`Theorem 5.1`): two polynomials of degree `≤ d_j / 2`
    combine via `g(y) + (α + β y)(f(y) + θ g(y))` into degree `≤ d_j / 2 + 1`. -/
@[expose] def affineFoldDegreeStep (d : Nat) : Nat :=
  d / 2 + 1

/-- Iterated univariate degree bound across `s` equal-degree affine binary folds. -/
@[expose] def affineFoldDegreeIter : Nat → Nat → Nat
  | 0, d => d
  | s + 1, d => affineFoldDegreeIter s (affineFoldDegreeStep d)

private theorem affineFoldDegreeIter_le_of_le :
    ∀ (s m d : Nat), s ≤ m → d ≤ 2 ^ m + 1 → affineFoldDegreeIter s d ≤ 2 ^ (m - s) + 1
  | 0, m, d, _, hd => by simpa using hd
  | s + 1, 0, _, hs, _ => by omega
  | s + 1, m + 1, d, hs, hd => by
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; omega
    have hstep : affineFoldDegreeStep d ≤ 2 ^ m + 1 := by
      unfold affineFoldDegreeStep
      omega
    have ih := affineFoldDegreeIter_le_of_le s m (affineFoldDegreeStep d) (by omega) hstep
    have hsub : m + 1 - (s + 1) = m - s := by omega
    rwa [hsub]

/-- **Equal-Degree Affine Fold Degree Stability (`affine_fold_degree_le_pow2_add_one`)**:
    Starting from multilinear univariate degree `d_0 = 2^ℓ - 1`, after ANY number `s ≤ ℓ` of
    equal-degree `[CWYZ26]` Theorem 5.1 folds (`d ↦ ⌊d/2⌋ + 1`), the folded polynomial has degree
    **`≤ 2^(ℓ - s) + 1`** — i.e., **at most `2` overflow monomials** (`2^(ℓ - s) + 2` coefficients),
    never growing unboundedly with `s`! -/
theorem affine_fold_degree_le_pow2_add_one (ℓ s : Nat) (hs : s ≤ ℓ) :
    affineFoldDegreeIter s (2 ^ ℓ - 1) ≤ 2 ^ (ℓ - s) + 1 :=
  affineFoldDegreeIter_le_of_le s ℓ (2 ^ ℓ - 1) hs (by omega)

/-- **Two-Point Affine Line Uniqueness (`affine_line_unique_of_two_points`)**:
    Over any `[LawfulField F] [DecidableEq F]`, if two affine functions `α₁ + β₁ x` and `α₂ + β₂ x`
    agree at two distinct points `z₀ ≠ z₁`, then `α₁ = α₂ ∧ β₁ = β₂`. -/
theorem affine_line_unique_of_two_points
    {F : Type} [LawfulField F] [DecidableEq F]
    {α₁ β₁ α₂ β₂ z₀ z₁ : F}
    (hz : z₀ ≠ z₁)
    (h₀ : CommRingOps.add α₁ (CommRingOps.mul β₁ z₀) =
          CommRingOps.add α₂ (CommRingOps.mul β₂ z₀))
    (h₁ : CommRingOps.add α₁ (CommRingOps.mul β₁ z₁) =
          CommRingOps.add α₂ (CommRingOps.mul β₂ z₁)) :
    α₁ = α₂ ∧ β₁ = β₂ := by
  have hdiff : CommRingOps.sub
      (CommRingOps.add α₁ (CommRingOps.mul β₁ z₀))
      (CommRingOps.add α₁ (CommRingOps.mul β₁ z₁)) =
      CommRingOps.sub
      (CommRingOps.add α₂ (CommRingOps.mul β₂ z₀))
      (CommRingOps.add α₂ (CommRingOps.mul β₂ z₁)) := by
    rw [h₀, h₁]
  have cancel_alpha : ∀ a b x y : F,
      CommRingOps.sub (CommRingOps.add a x) (CommRingOps.add a y) = CommRingOps.sub x y := by
    intro a b x y
    apply LawfulCommRing.add_left_cancel (a := CommRingOps.add a y)
    rw [LawfulCommRing.add_sub_cancel_left,
        LawfulCommRing.add_comm a y,
        ← LawfulCommRing.add_assoc y a (CommRingOps.sub x y),
        LawfulCommRing.add_comm y a,
        LawfulCommRing.add_assoc a y (CommRingOps.sub x y),
        LawfulCommRing.add_sub_cancel_left]
  rw [cancel_alpha α₁ α₁, cancel_alpha α₂ α₂,
      ← LawfulCommRing.mul_sub, ← LawfulCommRing.mul_sub] at hdiff
  have hprod : CommRingOps.mul (CommRingOps.sub β₁ β₂) (CommRingOps.sub z₀ z₁) =
      CommRingOps.zero := by
    rw [LawfulCommRing.sub_mul]
    exact LawfulCommRing.sub_eq_zero_iff.mpr hdiff
  have hzSub : CommRingOps.sub z₀ z₁ ≠ CommRingOps.zero :=
    fun h0 => hz (LawfulCommRing.sub_eq_zero_iff.mp h0)
  rcases LawfulField.mul_eq_zero hprod with hβ0 | hz0
  · have hβ : β₁ = β₂ := LawfulCommRing.sub_eq_zero_iff.mp hβ0
    subst hβ
    have hα : α₁ = α₂ := by
      apply LawfulCommRing.add_left_cancel (a := CommRingOps.mul β₁ z₀)
      rw [LawfulCommRing.add_comm _ α₁, LawfulCommRing.add_comm _ α₂]
      exact h₀
    exact ⟨hα, rfl⟩
  · exact False.elim (hzSub hz0)

/-- Constructive `2 × 2` Vandermonde solver returning `(α, β)` with `α + β z₀ = y₀` and `α + β z₁ = y₁`. -/
def solveAffineLine {F : Type} [LawfulField F] (z₀ y₀ z₁ y₁ : F) : F × F :=
  let β := CommRingOps.mul (CommRingOps.sub y₀ y₁) (LawfulField.inv (CommRingOps.sub z₀ z₁))
  let α := CommRingOps.sub y₀ (CommRingOps.mul β z₀)
  (α, β)

theorem solveAffineLine_eq_of_eval
    {F : Type} [LawfulField F] [DecidableEq F]
    {α β z₀ y₀ z₁ y₁ : F}
    (hz : z₀ ≠ z₁)
    (h₀ : CommRingOps.add α (CommRingOps.mul β z₀) = y₀)
    (h₁ : CommRingOps.add α (CommRingOps.mul β z₁) = y₁) :
    (α, β) = solveAffineLine z₀ y₀ z₁ y₁ := by
  unfold solveAffineLine
  dsimp only
  have hzSub : CommRingOps.sub z₀ z₁ ≠ CommRingOps.zero :=
    fun h => hz (LawfulCommRing.sub_eq_zero_iff.mp h)
  let β' := CommRingOps.mul (CommRingOps.sub y₀ y₁) (LawfulField.inv (CommRingOps.sub z₀ z₁))
  let α' := CommRingOps.sub y₀ (CommRingOps.mul β' z₀)
  have h₀' : CommRingOps.add α' (CommRingOps.mul β' z₀) = y₀ := by
    dsimp [α']
    rw [LawfulCommRing.add_comm, LawfulCommRing.add_sub_cancel_left]
  have hDiff : CommRingOps.mul β' (CommRingOps.sub z₀ z₁) = CommRingOps.sub y₀ y₁ := by
    dsimp [β']
    rw [LawfulCommRing.mul_assoc, LawfulField.inv_mul_cancel hzSub, LawfulCommRing.mul_one]
  have h₁' : CommRingOps.add α' (CommRingOps.mul β' z₁) = y₁ := by
    apply LawfulCommRing.add_left_cancel (a := CommRingOps.sub y₀ y₁)
    have hL : CommRingOps.add (CommRingOps.sub y₀ y₁) (CommRingOps.add α' (CommRingOps.mul β' z₁)) =
        CommRingOps.add α' (CommRingOps.add (CommRingOps.mul β' (CommRingOps.sub z₀ z₁))
          (CommRingOps.mul β' z₁)) := by
      rw [← hDiff, LawfulCommRing.add_comm (CommRingOps.mul β' _) _, LawfulCommRing.add_assoc]
    rw [hL, LawfulCommRing.mul_sub, LawfulCommRing.add_comm (CommRingOps.sub _ _) _,
        LawfulCommRing.add_sub_cancel_left, h₀',
        LawfulCommRing.add_comm (CommRingOps.sub y₀ y₁) y₁,
        LawfulCommRing.add_sub_cancel_left]
  rcases affine_line_unique_of_two_points hz (h₀.trans h₀'.symm) (h₁.trans h₁'.symm) with ⟨rfl, rfl⟩
  rfl

/-- Cartesian product challenge pool `S × S` preserving duplicate-freedom. -/
@[expose] def prodPool {α : Type} (S : List α) : List (α × α) :=
  S.flatMap (fun a => S.map (fun b => (a, b)))

theorem prodPool_length {α : Type} (S : List α) :
    (prodPool S).length = S.length * S.length := by
  unfold prodPool
  induction S with
  | nil => rfl
  | cons a tl ih =>
    have hrec : ∀ (xs : List α) (k : Nat),
        (xs.flatMap (fun x => List.map (fun b => (x, b)) (a :: tl))).length =
        xs.length * (tl.length + 1) := by
      intro xs _
      induction xs with
      | nil => simp
      | cons _ rest ihr =>
        simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons]
        rw [ihr]
        omega
    simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons]
    rw [hrec tl 0]
    omega

theorem mem_prodPool_iff {α : Type} {S : List α} {p : α × α} :
    p ∈ prodPool S ↔ p.1 ∈ S ∧ p.2 ∈ S := by
  rcases p with ⟨a, b⟩
  unfold prodPool
  simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨a', ha', b', hb', rfl, rfl⟩
    exact ⟨ha', hb'⟩
  · rintro ⟨ha, hb⟩
    exact ⟨a, ha, b, hb, rfl, rfl⟩

private theorem nodup_map_pair_right {α : Type} (a : α) :
    ∀ {S : List α}, S.Nodup → (S.map (fun b => (a, b))).Nodup
  | [], _ => .nil
  | b :: bs, .cons hnot hnd => by
    simp only [List.map]
    refine .cons ?_ (nodup_map_pair_right a hnd)
    intro p hp heq
    rw [List.mem_map] at hp
    rcases hp with ⟨b', hb', rfl⟩
    cases heq
    exact hnot b' hb' rfl

private theorem nodup_flatMap_pairs {α : Type} (B : List α) (hB : B.Nodup) :
    ∀ {A : List α}, A.Nodup → (A.flatMap (fun a => B.map (fun b => (a, b)))).Nodup
  | [], _ => .nil
  | a :: as, .cons hnot hnd => by
    simp only [List.flatMap_cons]
    rw [List.nodup_append]
    refine ⟨nodup_map_pair_right a hB, nodup_flatMap_pairs B hB hnd, ?_⟩
    intro p₁ hp₁ p₂ hp₂ heq
    subst heq
    rw [List.mem_map] at hp₁
    rw [List.mem_flatMap] at hp₂
    rcases hp₁ with ⟨b₁, _, rfl⟩
    rcases hp₂ with ⟨a₂, ha₂, hp₂'⟩
    rw [List.mem_map] at hp₂'
    rcases hp₂' with ⟨b₂, _, heq'⟩
    cases heq'
    exact hnot a ha₂ rfl

theorem prodPool_nodup {α : Type} {S : List α} (hS : S.Nodup) :
    (prodPool S).Nodup :=
  nodup_flatMap_pairs S hS hS

/-- Constructive first-occurrence erasure for proving `Nodup` subset length bounds (`0` choice). -/
private def eraseFirst {α : Type} [DecidableEq α] (x : α) : List α → List α
  | [] => []
  | y :: ys => if x = y then ys else y :: eraseFirst x ys

private theorem eraseFirst_length_of_mem {α : Type} [DecidableEq α] {x : α} :
    ∀ {M : List α}, x ∈ M → (eraseFirst x M).length + 1 = M.length
  | [], h => by cases h
  | y :: ys, h => by
    unfold eraseFirst
    if hxy : x = y then
      simp [hxy]
    else
      simp only [hxy, ↓reduceIte, List.length_cons]
      cases h with
      | head => exact False.elim (hxy rfl)
      | tail _ hm =>
        have ih := eraseFirst_length_of_mem hm
        omega

private theorem mem_eraseFirst_of_ne {α : Type} [DecidableEq α] {x z : α} (hne : z ≠ x) :
    ∀ {M : List α}, z ∈ M → z ∈ eraseFirst x M
  | [], h => by cases h
  | y :: ys, h => by
    unfold eraseFirst
    if hxy : x = y then
      subst hxy
      cases h with
      | head => exact False.elim (hne rfl)
      | tail _ hm => exact hm
    else
      simp only [hxy, ↓reduceIte]
      cases h with
      | head => exact .head _
      | tail _ hm => exact .tail _ (mem_eraseFirst_of_ne hne hm)

/-- Constructive Pigeonhole / Subset-Length Lemma: any `Nodup` list `L` contained in `M` satisfies
    `L.length ≤ M.length` (`0` classical axioms). -/
theorem nodup_length_le_of_subset {α : Type} [DecidableEq α] :
    ∀ {L M : List α}, L.Nodup → (∀ x ∈ L, x ∈ M) → L.length ≤ M.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, M, .cons hnot hnd, hsub => by
    have hxM : x ∈ M := hsub x (.head _)
    have hlen := eraseFirst_length_of_mem hxM
    have hsub' : ∀ z ∈ xs, z ∈ eraseFirst x M := by
      intro z hz
      have hne : z ≠ x := fun heq => hnot z hz heq.symm
      exact mem_eraseFirst_of_ne hne (hsub z (.tail _ hz))
    have ih := nodup_length_le_of_subset hnd hsub'
    simp only [List.length_cons]
    omega

private theorem filter_eq_max_one_of_nodup {α : Type} [DecidableEq α] (target : α) :
    ∀ {S : List α}, S.Nodup → (S.filter (fun x => decide (x = target))).length ≤ 1
  | [], _ => by simp
  | x :: xs, .cons hnot hnd => by
    simp only [List.filter]
    if hx : x = target then
      subst hx
      simp only [decide_true, List.length_cons]
      have hempty : xs.filter (fun y => decide (y = x)) = [] := by
        induction xs with
        | nil => rfl
        | cons y ys ih =>
          have hyne : y ≠ x := fun heq => hnot y (.head _) heq.symm
          have hnd' : ys.Nodup := by
            cases hnd with | cons _ t => exact t
          simp [List.filter, hyne, ih (fun z hz => hnot z (.tail _ hz)) hnd']
      rw [hempty]
      decide
    else
      simp only [hx, decide_false]
      exact filter_eq_max_one_of_nodup target hnd

private theorem filter_sub_length_le {α : Type} (p q : α → Bool) (hpq : ∀ x, p x = true → q x = true) :
    ∀ (xs : List α), (xs.filter p).length ≤ (xs.filter q).length
  | [] => Nat.le_refl 0
  | x :: xs => by
    simp only [List.filter]
    cases hpx : p x
    · cases hqx : q x <;> simp [filter_sub_length_le p q hpq xs] <;> omega
    · rw [hpq x hpx]
      simp only [List.length_cons]
      exact Nat.succ_le_succ (filter_sub_length_le p q hpq xs)

private theorem flatMap_filter_length_le {α β : Type} (f : α → List β) (p : β → Bool) (B : Nat) :
    ∀ {xs : List α}, (∀ x ∈ xs, ((f x).filter p).length ≤ B) →
      ((xs.flatMap f).filter p).length ≤ xs.length * B
  | [], _ => by simp
  | x :: xs, hB => by
    rw [List.flatMap_cons, List.filter_append, List.length_append, List.length_cons]
    have hx := hB x (.head _)
    have htl := flatMap_filter_length_le f p B (fun y hy => hB y (.tail _ hy))
    have hmul : (xs.length + 1) * B = B + xs.length * B := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    rw [hmul]
    exact Nat.add_le_add hx htl

/-- Affine duet discrepancy polynomial `Δ₀ + α Δ₁ + β Δ₂`. -/
@[expose] def evalAffineDuet {F : Type} [CommRingOps F] (Δ₀ Δ₁ Δ₂ α β : F) : F :=
  CommRingOps.add Δ₀ (CommRingOps.add (CommRingOps.mul α Δ₁) (CommRingOps.mul β Δ₂))

/-- **Affine Duet Root Bound (`affine_duet_roots_le_card`)**:
    Over any `[LawfulField F] [DecidableEq F]`, for any non-trivial discrepancy triple
    `(Δ₀, Δ₁, Δ₂) ≠ (0, 0, 0)` and duplicate-free challenge list `S`, at most `S.length` pairs
    `(α, β) ∈ prodPool S` satisfy `Δ₀ + α Δ₁ + β Δ₂ = 0` (`≤ |S| / |S|^2 = 1 / |S|` density). -/
theorem affine_duet_roots_le_card
    {F : Type} [LawfulField F] [DecidableEq F]
    (Δ₀ Δ₁ Δ₂ : F) (S : List F)
    (hS : S.Nodup)
    (hNonzero : Δ₀ ≠ CommRingOps.zero ∨ Δ₁ ≠ CommRingOps.zero ∨ Δ₂ ≠ CommRingOps.zero) :
    ((prodPool S).filter (fun p =>
      decide (evalAffineDuet Δ₀ Δ₁ Δ₂ p.1 p.2 = CommRingOps.zero))).length ≤ S.length := by
  if hΔ₂ : Δ₂ ≠ CommRingOps.zero then
    unfold prodPool
    have hbound := flatMap_filter_length_le
      (f := fun a => S.map (fun b => (a, b)))
      (p := fun p => decide (evalAffineDuet Δ₀ Δ₁ Δ₂ p.1 p.2 = CommRingOps.zero))
      (B := 1) (xs := S) ?_
    · rw [Nat.mul_one] at hbound
      exact hbound
    · intro a _
      let target := CommRingOps.neg
        (CommRingOps.mul (CommRingOps.add Δ₀ (CommRingOps.mul a Δ₁)) (LawfulField.inv Δ₂))
      have hmap : ((S.map (fun b => (a, b))).filter
          (fun p => decide (evalAffineDuet Δ₀ Δ₁ Δ₂ p.1 p.2 = CommRingOps.zero))).length =
          (S.filter (fun b => decide (evalAffineDuet Δ₀ Δ₁ Δ₂ a b = CommRingOps.zero))).length := by
        induction S with
        | nil => rfl
        | cons b bs ih =>
          simp only [List.map, List.filter]
          cases decide (evalAffineDuet Δ₀ Δ₁ Δ₂ a b = CommRingOps.zero) <;> simp [ih]
      rw [hmap]
      have hsub := filter_sub_length_le
        (fun b => decide (evalAffineDuet Δ₀ Δ₁ Δ₂ a b = CommRingOps.zero))
        (fun b => decide (b = target))
        (fun b hb => by
          have hev : evalAffineDuet Δ₀ Δ₁ Δ₂ a b = CommRingOps.zero := of_decide_eq_true hb
          unfold evalAffineDuet at hev
          rw [LawfulCommRing.add_comm Δ₀ _, ← LawfulCommRing.add_assoc,
              LawfulCommRing.add_comm (CommRingOps.mul a Δ₁) (CommRingOps.mul b Δ₂),
              LawfulCommRing.add_assoc] at hev
          have hmul0 : CommRingOps.mul b Δ₂ =
              CommRingOps.neg (CommRingOps.add Δ₀ (CommRingOps.mul a Δ₁)) := by
            apply LawfulCommRing.add_left_cancel
              (a := CommRingOps.add Δ₀ (CommRingOps.mul a Δ₁))
            rw [LawfulCommRing.add_right_neg,
                LawfulCommRing.add_comm Δ₀ _,
                LawfulCommRing.add_comm _ (CommRingOps.mul b Δ₂)]
            exact hev
          have hbEq := congrArg (fun z => CommRingOps.mul z (LawfulField.inv Δ₂)) hmul0
          rw [LawfulCommRing.mul_assoc, LawfulField.mul_inv_cancel hΔ₂, LawfulCommRing.mul_one,
              LawfulCommRing.neg_mul] at hbEq
          exact decide_eq_true hbEq)
        S
      exact Nat.le_trans hsub (filter_eq_max_one_of_nodup target hS)
  else
    have hΔ₂0 : Δ₂ = CommRingOps.zero :=
      if h : Δ₂ = CommRingOps.zero then h else False.elim (hΔ₂ h)
    if hΔ₁ : Δ₁ ≠ CommRingOps.zero then
      let target := CommRingOps.neg (CommRingOps.mul Δ₀ (LawfulField.inv Δ₁))
      let singlePairs := S.map (fun b => (target, b))
      have hndFilt : ((prodPool S).filter (fun p =>
          decide (evalAffineDuet Δ₀ Δ₁ Δ₂ p.1 p.2 = CommRingOps.zero))).Nodup := by
        have hndP := prodPool_nodup hS
        exact List.Pairwise.filter _ hndP
      have hsub : ∀ p ∈ (prodPool S).filter (fun p =>
          decide (evalAffineDuet Δ₀ Δ₁ Δ₂ p.1 p.2 = CommRingOps.zero)), p ∈ singlePairs := by
        intro p hp
        rw [List.mem_filter] at hp
        rcases hp with ⟨hpMem, hpZero⟩
        rcases p with ⟨a, b⟩
        have hbMem := (mem_prodPool_iff.mp hpMem).2
        have hev : evalAffineDuet Δ₀ Δ₁ Δ₂ a b = CommRingOps.zero := of_decide_eq_true hpZero
        unfold evalAffineDuet at hev
        rw [hΔ₂0, LawfulCommRing.mul_zero, LawfulCommRing.add_zero] at hev
        have hmul0 : CommRingOps.mul a Δ₁ = CommRingOps.neg Δ₀ := by
          apply LawfulCommRing.add_left_cancel (a := Δ₀)
          rw [LawfulCommRing.add_right_neg]
          exact hev
        have haEq := congrArg (fun z => CommRingOps.mul z (LawfulField.inv Δ₁)) hmul0
        rw [LawfulCommRing.mul_assoc, LawfulField.mul_inv_cancel hΔ₁, LawfulCommRing.mul_one,
            LawfulCommRing.neg_mul] at haEq
        subst haEq
        rw [List.mem_map]
        exact ⟨b, hbMem, rfl⟩
      have hle := nodup_length_le_of_subset hndFilt hsub
      simpa [singlePairs] using hle
    else
      have hΔ₁0 : Δ₁ = CommRingOps.zero :=
        if h : Δ₁ = CommRingOps.zero then h else False.elim (hΔ₁ h)
      have hΔ₀ : Δ₀ ≠ CommRingOps.zero := by
        rcases hNonzero with h0 | h1 | h2
        · exact h0
        · exact False.elim (hΔ₁ h1)
        · exact False.elim (hΔ₂ h2)
      have hempty : (prodPool S).filter (fun p =>
          decide (evalAffineDuet Δ₀ Δ₁ Δ₂ p.1 p.2 = CommRingOps.zero)) = [] := by
        induction prodPool S with
        | nil => rfl
        | cons p ps ih =>
          have hne : evalAffineDuet Δ₀ Δ₁ Δ₂ p.1 p.2 ≠ CommRingOps.zero := by
            unfold evalAffineDuet
            rw [hΔ₁0, hΔ₂0, LawfulCommRing.mul_zero, LawfulCommRing.mul_zero,
                LawfulCommRing.add_zero, LawfulCommRing.add_zero]
            exact hΔ₀
          simp [List.filter, hne, ih]
      rw [hempty]
      exact Nat.zero_le _

/-- Strictly ordered index pairs `(z₀, z₁)` from a domain list `D`, of exact size `D.length * (D.length - 1) / 2`. -/
def unorderedPairs {α : Type} : List α → List (α × α)
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ unorderedPairs xs

private theorem two_mul_unorderedPairs_length {α : Type} :
    ∀ (D : List α), 2 * (unorderedPairs D).length = D.length * (D.length - 1)
  | [] => rfl
  | x :: xs => by
    have ih := two_mul_unorderedPairs_length xs
    simp only [unorderedPairs, List.length_append, List.length_map, List.length_cons]
    have hmul : (xs.length + 1) * xs.length = 2 * xs.length + xs.length * (xs.length - 1) := by
      cases xs with
      | nil => rfl
      | cons _ tl =>
        simp only [List.length_cons, Nat.add_sub_cancel]
        rw [Nat.add_mul, Nat.mul_add]
        omega
    omega

theorem unorderedPairs_length {α : Type} (D : List α) :
    (unorderedPairs D).length = D.length * (D.length - 1) / 2 := by
  rw [← two_mul_unorderedPairs_length D]
  omega

theorem ne_of_mem_unorderedPairs_nodup {α : Type} :
    ∀ {D : List α} {p : α × α}, D.Nodup → p ∈ unorderedPairs D → p.1 ≠ p.2
  | [], _, _, hp => by cases hp
  | x :: xs, ⟨a, b⟩, .cons hnot hnd, hp => by
    simp only [unorderedPairs, List.mem_append, List.mem_map, Prod.mk.injEq] at hp
    rcases hp with ⟨y, hy, rfl, rfl⟩ | htl
    · exact fun heq => hnot a (heq ▸ hy) rfl
    · exact ne_of_mem_unorderedPairs_nodup hnd htl

private theorem filter_two_mem_unorderedPairs {α : Type} (pred : α → Bool) :
    ∀ {D : List α} {z₀ z₁ : α} {rest : List α},
      D.filter pred = z₀ :: z₁ :: rest → (z₀, z₁) ∈ unorderedPairs D
  | [], _, _, _, h => by cases h
  | x :: xs, z₀, z₁, rest, h => by
    simp only [List.filter] at h
    cases hpx : pred x
    · rw [hpx] at h
      have ih := filter_two_mem_unorderedPairs pred h
      simp only [unorderedPairs, List.mem_append]
      exact .inr ih
    · rw [hpx] at h
      cases h
      have hz₁InFilt : z₁ ∈ xs.filter pred := .head _
      have hz₁InXs : z₁ ∈ xs := (List.mem_filter.mp hz₁InFilt).1
      simp only [unorderedPairs, List.mem_append, List.mem_map, Prod.mk.injEq]
      exact .inl ⟨z₁, hz₁InXs, rfl, rfl⟩

/-- Predicate testing whether coordinate `z` is an **accidental agreement** between `(F, G)` and `(f, g)`
    along `(α, β)`: `F(z) + (α + β z) G(z) = f(z) + (α + β z) g(z)` while `(F(z), G(z)) ≠ (f(z), g(z))`. -/
@[expose] def isAccidentalAgreement
    {F : Type} [CommRingOps F] [DecidableEq F]
    (F_poly G_poly : List F) (f g : F → F) (α β z : F) : Bool :=
  let a := CommRingOps.add α (CommRingOps.mul β z)
  let lhs := CommRingOps.add (RoundPoly.evalCoeffs F_poly z)
    (CommRingOps.mul a (RoundPoly.evalCoeffs G_poly z))
  let rhs := CommRingOps.add (f z) (CommRingOps.mul a (g z))
  decide (lhs = rhs) &&
    !(decide (RoundPoly.evalCoeffs F_poly z = f z) && decide (RoundPoly.evalCoeffs G_poly z = g z))

private def pairLineCandidate
    {F : Type} [LawfulField F]
    (F_poly G_poly : List F) (f g : F → F) (pair : F × F) : F × F :=
  let ratio := fun z =>
    CommRingOps.mul
      (CommRingOps.sub (f z) (RoundPoly.evalCoeffs F_poly z))
      (LawfulField.inv (CommRingOps.sub (RoundPoly.evalCoeffs G_poly z) (g z)))
  solveAffineLine pair.1 (ratio pair.1) pair.2 (ratio pair.2)

private theorem accidental_agreement_forces_ratio
    {F : Type} [LawfulField F] [DecidableEq F]
    {F_poly G_poly : List F} {f g : F → F} {α β z : F}
    (hAcc : isAccidentalAgreement F_poly G_poly f g α β z = true) :
    CommRingOps.add α (CommRingOps.mul β z) =
      CommRingOps.mul
        (CommRingOps.sub (f z) (RoundPoly.evalCoeffs F_poly z))
        (LawfulField.inv (CommRingOps.sub (RoundPoly.evalCoeffs G_poly z) (g z))) := by
  unfold isAccidentalAgreement at hAcc
  rw [Bool.and_eq_true] at hAcc
  rcases hAcc with ⟨hEqDec, hNotBoth⟩
  have hEq : CommRingOps.add (RoundPoly.evalCoeffs F_poly z)
      (CommRingOps.mul (CommRingOps.add α (CommRingOps.mul β z)) (RoundPoly.evalCoeffs G_poly z)) =
      CommRingOps.add (f z)
      (CommRingOps.mul (CommRingOps.add α (CommRingOps.mul β z)) (g z)) :=
    of_decide_eq_true hEqDec
  let a := CommRingOps.add α (CommRingOps.mul β z)
  let dG := CommRingOps.sub (RoundPoly.evalCoeffs G_poly z) (g z)
  let dF := CommRingOps.sub (f z) (RoundPoly.evalCoeffs F_poly z)
  have hRel : CommRingOps.mul a dG = dF := by
    dsimp [a, dG, dF]
    rw [LawfulCommRing.mul_sub]
    apply LawfulCommRing.add_left_cancel
      (a := CommRingOps.add (RoundPoly.evalCoeffs F_poly z)
              (CommRingOps.mul (CommRingOps.add α (CommRingOps.mul β z)) (g z)))
    rw [LawfulCommRing.add_comm (RoundPoly.evalCoeffs F_poly z) _,
        LawfulCommRing.add_assoc _ (RoundPoly.evalCoeffs F_poly z) _,
        LawfulCommRing.add_comm (RoundPoly.evalCoeffs F_poly z) (CommRingOps.sub _ _),
        ← LawfulCommRing.add_assoc,
        LawfulCommRing.add_sub_cancel_left,
        LawfulCommRing.add_comm _ (RoundPoly.evalCoeffs F_poly z),
        hEq,
        LawfulCommRing.add_comm (CommRingOps.mul _ (g z)) _,
        ← LawfulCommRing.add_assoc,
        LawfulCommRing.add_comm (f z) _,
        LawfulCommRing.add_assoc,
        LawfulCommRing.add_sub_cancel_left,
        LawfulCommRing.add_comm]
  have hdGNe : dG ≠ CommRingOps.zero := by
    intro hdG0
    have hG : RoundPoly.evalCoeffs G_poly z = g z := LawfulCommRing.sub_eq_zero_iff.mp hdG0
    rw [hdG0, LawfulCommRing.mul_zero] at hRel
    have hF : RoundPoly.evalCoeffs F_poly z = f z :=
      (LawfulCommRing.sub_eq_zero_iff.mp hRel.symm).symm
    simp [hF, hG] at hNotBoth
  have hmul := congrArg (fun w => CommRingOps.mul w (LawfulField.inv dG)) hRel
  rw [LawfulCommRing.mul_assoc, LawfulField.mul_inv_cancel hdGNe, LawfulCommRing.mul_one] at hmul
  exact hmul

/-- **Persistent Polynomial-Pair Pruning (`committed_polynomial_pair_bad_lines_le_choose2`)**:
    For ANY fixed polynomial pair `(F_poly, G_poly)` and ANY received words `(f, g)` on a
    duplicate-free domain `D : List F`, the number of challenge pairs `(α, β) ∈ prodPool S` with
    **at least `2` accidental agreements** in `D` (i.e., failing $s = 1$ coordinate inheritance)
    is bounded by **`D.length * (D.length - 1) / 2`**! -/
theorem committed_polynomial_pair_bad_lines_le_choose2
    {F : Type} [LawfulField F] [DecidableEq F]
    (F_poly G_poly : List F) (f g : F → F) (D S : List F)
    (hD : D.Nodup) (hS : S.Nodup) :
    ((prodPool S).filter (fun p =>
      decide (2 ≤ (D.filter (isAccidentalAgreement F_poly G_poly f g p.1 p.2)).length))).length ≤
    D.length * (D.length - 1) / 2 := by
  let bad := (prodPool S).filter (fun p =>
    decide (2 ≤ (D.filter (isAccidentalAgreement F_poly G_poly f g p.1 p.2)).length))
  let cands := (unorderedPairs D).map (pairLineCandidate F_poly G_poly f g)
  have hndBad : bad.Nodup := List.Pairwise.filter _ (prodPool_nodup hS)
  have hsub : ∀ p ∈ bad, p ∈ cands := by
    intro p hp
    rw [List.mem_filter] at hp
    rcases hp with ⟨_, hgeDec⟩
    have hge : 2 ≤ (D.filter (isAccidentalAgreement F_poly G_poly f g p.1 p.2)).length :=
      of_decide_eq_true hgeDec
    cases hFilt : D.filter (isAccidentalAgreement F_poly G_poly f g p.1 p.2) with
    | nil => rw [hFilt] at hge; cases hge
    | cons z₀ tl =>
      cases tl with
      | nil => rw [hFilt] at hge; cases hge; contradiction
      | cons z₁ rest =>
        have hPairMem : (z₀, z₁) ∈ unorderedPairs D :=
          filter_two_mem_unorderedPairs _ hFilt
        have hzNe : z₀ ≠ z₁ := ne_of_mem_unorderedPairs_nodup hD hPairMem
        have hz₀Acc : isAccidentalAgreement F_poly G_poly f g p.1 p.2 z₀ = true :=
          (List.mem_filter.mp (by rw [hFilt]; exact .head _)).2
        have hz₁Acc : isAccidentalAgreement F_poly G_poly f g p.1 p.2 z₁ = true :=
          (List.mem_filter.mp (by rw [hFilt]; exact .tail _ (.head _))).2
        have hpEq := solveAffineLine_eq_of_eval hzNe
          (accidental_agreement_forces_ratio hz₀Acc)
          (accidental_agreement_forces_ratio hz₁Acc)
        rw [List.mem_map]
        exact ⟨(z₀, z₁), hPairMem, hpEq.symm⟩
  have hle := nodup_length_le_of_subset hndBad hsub
  rw [List.length_map, unorderedPairs_length] at hle
  exact hle


/-! ## §2. Constructive `#tooth` Lower Bounds (`Proposition 6.1` Scalar & `Proposition 6.2` $s=0$ Affine) -/

/-- Monic vanishing polynomial `∏_{c ∈ C} (X - c)` of degree `C.length`. -/
def vanishingPoly {F : Type} [CommRingOps F] : List F → List F
  | [] => [CommRingOps.one]
  | c :: cs =>
    let p := vanishingPoly cs
    RoundPoly.subCoeffs (CommRingOps.zero :: p) (p.map (CommRingOps.mul c))

theorem vanishingPoly_length {F : Type} [CommRingOps F] :
    ∀ (C : List F), (vanishingPoly C).length = C.length + 1
  | [] => rfl
  | c :: cs => by
    simp only [vanishingPoly, RoundPoly.subCoeffs_length, List.length_cons, List.length_map,
               vanishingPoly_length cs]
    omega

private theorem evalCoeffs_map_mul {F : Type} [LawfulCommRing F] (c x : F) :
    ∀ (p : List F), RoundPoly.evalCoeffs (p.map (CommRingOps.mul c)) x =
      CommRingOps.mul c (RoundPoly.evalCoeffs p x)
  | [] => by simp [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero]
  | a :: as => by
    simp only [List.map, RoundPoly.evalCoeffs, evalCoeffs_map_mul c x as]
    rw [LawfulCommRing.left_distrib,
        ← LawfulCommRing.mul_assoc c x _,
        LawfulCommRing.mul_comm c x,
        LawfulCommRing.mul_assoc]

theorem eval_vanishingPoly_eq_zero_of_mem {F : Type} [LawfulCommRing F] :
    ∀ {C : List F} {z : F}, z ∈ C → RoundPoly.evalCoeffs (vanishingPoly C) z = CommRingOps.zero
  | [], _, h => by cases h
  | c :: cs, z, h => by
    simp only [vanishingPoly, RoundPoly.evalCoeffs_sub, RoundPoly.evalCoeffs_cons,
               LawfulCommRing.zero_add, evalCoeffs_map_mul]
    rw [← LawfulCommRing.sub_mul]
    cases h with
    | head =>
      rw [LawfulCommRing.sub_self, LawfulCommRing.zero_mul]
    | tail _ hm =>
      rw [eval_vanishingPoly_eq_zero_of_mem hm, LawfulCommRing.mul_zero]

theorem eval_vanishingPoly_ne_zero_of_not_mem
    {F : Type} [LawfulField F] [DecidableEq F] :
    ∀ {C : List F} {z : F}, z ∉ C → RoundPoly.evalCoeffs (vanishingPoly C) z ≠ CommRingOps.zero
  | [], z, _ => by
    simp only [vanishingPoly, RoundPoly.evalCoeffs_cons, RoundPoly.evalCoeffs_nil,
               LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    exact LawfulField.one_ne_zero
  | c :: cs, z, hnot => by
    simp only [vanishingPoly, RoundPoly.evalCoeffs_sub, RoundPoly.evalCoeffs_cons,
               LawfulCommRing.zero_add, evalCoeffs_map_mul, ← LawfulCommRing.sub_mul]
    have hzc : z ≠ c := fun heq => hnot (heq ▸ .head _)
    have hzNotCs : z ∉ cs := fun hm => hnot (.tail _ hm)
    have hsubNe : CommRingOps.sub z c ≠ CommRingOps.zero :=
      fun h0 => hzc (LawfulCommRing.sub_eq_zero_iff.mp h0)
    have ih := eval_vanishingPoly_ne_zero_of_not_mem hzNotCs
    intro hprod
    rcases LawfulField.mul_eq_zero hprod with h1 | h2
    · exact hsubNe h1
    · exact ih h2

private theorem last_subCoeffs_vanishingPoly
    {F : Type} [LawfulField F] :
    ∀ (p G : List F),
      0 < p.length →
      p.getD (p.length - 1) CommRingOps.zero = CommRingOps.one →
      G.length < p.length →
      (RoundPoly.subCoeffs p G).getD (p.length - 1) CommRingOps.zero = CommRingOps.one
  | [], _, hp, _, _ => by cases hp
  | [c], [], _, hlast, _ => by
    simpa [RoundPoly.subCoeffs] using hlast
  | [_], _ :: _, _, _, hlt => by simp at hlt; omega
  | c₀ :: c₁ :: cs, [], _, hlast, _ => by
    have hpos : 0 < (c₁ :: cs).length := by simp
    have ih := last_subCoeffs_vanishingPoly (c₁ :: cs) [] hpos hlast (by simp)
    simpa [RoundPoly.subCoeffs] using ih
  | c₀ :: c₁ :: cs, g₀ :: gs, _, hlast, hlt => by
    have hpos : 0 < (c₁ :: cs).length := by simp
    have hlt' : gs.length < (c₁ :: cs).length := by simp at hlt ⊢; omega
    have ih := last_subCoeffs_vanishingPoly (c₁ :: cs) gs hpos hlast hlt'
    simpa [RoundPoly.subCoeffs] using ih

private theorem exists_nonroot_of_monic_len
    {F : Type} [LawfulField F] [DecidableEq F] :
    ∀ (k : Nat) (p U : List F),
      p.length = k + 1 →
      p.getD k CommRingOps.zero = CommRingOps.one →
      U.Nodup →
      k + 1 ≤ U.length →
      ∃ x₀ ∈ U, RoundPoly.evalCoeffs p x₀ ≠ CommRingOps.zero
  | 0, [c], u :: _, _, hlast, _, _ => by
    simp only [List.getD, List.getElem?_cons_zero, Option.getD_some] at hlast
    subst hlast
    refine ⟨u, .head _, ?_⟩
    simp [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    exact LawfulField.one_ne_zero
  | 0, [], _, hlen, _, _, _ => by cases hlen
  | 0, _ :: _ :: _, _, hlen, _, _, _ => by simp at hlen
  | k + 1, p, [], _, _, _, hU => by simp at hU
  | k + 1, p, u :: us, hlen, hlast, .cons hnot hnd, hU => by
    if hev : RoundPoly.evalCoeffs p u = CommRingOps.zero then
      let q := RoundPoly.quotLinear p u
      have hqLen : q.length = k + 1 := by
        dsimp [q]; rw [RoundPoly.quotLinear_length, hlen]; omega
      have hqLast : q.getD k CommRingOps.zero = CommRingOps.one := by
        have aux : ∀ (m : Nat) (xs : List F),
            xs.length = m + 2 →
            (RoundPoly.quotLinear xs u).getD m CommRingOps.zero =
              xs.getD (m + 1) CommRingOps.zero := by
          intro m xs hxs
          induction m generalizing xs with
          | zero =>
            rcases xs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp at hxs
            simp [RoundPoly.quotLinear, RoundPoly.evalCoeffs,
                  LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
          | succ m' ihm =>
            rcases xs with _ | ⟨a, _ | ⟨b, tl⟩⟩ <;> simp at hxs
            have htl : (b :: tl).length = m' + 2 := by simp; omega
            have r := ihm (b :: tl) htl
            simpa [RoundPoly.quotLinear] using r
        rw [aux k p hlen, hlast]
      have hUsLen : k + 1 ≤ us.length := by simp at hU; omega
      rcases exists_nonroot_of_monic_len k q us hqLen hqLast hnd hUsLen with ⟨x₁, hx₁Mem, hx₁Ne⟩
      refine ⟨x₁, .tail _ hx₁Mem, ?_⟩
      rw [RoundPoly.evalCoeffs_eq_mul_quotLinear_add p u x₁, hev, LawfulCommRing.add_zero]
      have hneU : x₁ ≠ u := fun heq => hnot x₁ hx₁Mem heq.symm
      have hsubNe : CommRingOps.sub x₁ u ≠ CommRingOps.zero :=
        fun h0 => hneU (LawfulCommRing.sub_eq_zero_iff.mp h0)
      intro hprod
      rcases LawfulField.mul_eq_zero hprod with h1 | h2
      · exact hsubNe h1
      · exact hx₁Ne h2
    else
      exact ⟨u, .head _, hev⟩

/-- Lookup index of `x` in `D` (`none` if absent). -/
private def indexOf? {α : Type} [DecidableEq α] (x : α) : List α → Option Nat
  | [] => none
  | y :: ys => if x = y then some 0 else (indexOf? x ys).map (· + 1)

private theorem indexOf?_of_getElem? {α : Type} [DecidableEq α] :
    ∀ {D : List α} {i : Nat} {x : α}, D.Nodup → D[i]? = some x → indexOf? x D = some i
  | [], _, _, _, h => by simp at h
  | y :: ys, 0, x, _, h => by
    simp at h; subst h; simp [indexOf?]
  | y :: ys, i + 1, x, .cons hnot hnd, h => by
    simp only [List.getElem?_cons_succ] at h
    have hxMem : x ∈ ys := List.mem_of_getElem? h
    have hne : x ≠ y := fun heq => hnot x hxMem heq.symm
    simp [indexOf?, hne, indexOf?_of_getElem? hnd h]

/-- Adversarial received-word pair `(f, g)` for `[CWYZ26]` Proposition 6.1 (`prop:scfloor`). -/
def scalarFloorWords
    {F : Type} [LawfulField F] [DecidableEq F]
    (D gammas : List F) (A s : Nat) : (F → F) × (F → F) :=
  let cLen := A - s - 1
  let C := D.take cLen
  let gFn := fun z => RoundPoly.evalCoeffs (vanishingPoly C) z
  let fFn := fun z =>
    match indexOf? z D with
    | none => CommRingOps.zero
    | some idx =>
      if idx < cLen then CommRingOps.zero
      else
        let blk := (idx - cLen) / (s + 1)
        if blk < gammas.length ∧ cLen + (blk + 1) * (s + 1) ≤ D.length then
          CommRingOps.neg (CommRingOps.mul (gammas.getD blk CommRingOps.zero) (gFn z))
        else
          CommRingOps.zero
  (fFn, gFn)

/-- **`#tooth` Proposition 6.1 (`tooth_scalar_combiner_linear_n_over_q_floor`)**:
    For ANY degree `d`, loss `s`, threshold `A` (`d + s + 1 < A`, `A ≤ D.length`), and ANY list
    `gammas` of `1 + (D.length - A) / (s + 1)` distinct non-zero challenges in `S`:
    every `γ ∈ gammas` makes `f + γ g` vanish on **at least `A` points of `D`** (`P = 0`), yet
    **NO polynomial `G_poly` of degree `≤ d`** agrees with `g` on `≥ A - s` of those points —
    proving scalar combiners incur `≥ (1 + ⌊(n - A)/(s + 1)⌋) / |S| = Ω(n/q)` error even for `s ≥ 1`! -/
theorem tooth_scalar_combiner_linear_n_over_q_floor
    {F : Type} [LawfulField F] [DecidableEq F]
    (D gammas : List F) (d s A : Nat)
    (hD : D.Nodup)
    (hGammas : gammas.Nodup)
    (hGammasNz : ∀ γ ∈ gammas, γ ≠ CommRingOps.zero)
    (hA_lo : d + s + 1 < A)
    (hA_hi : A ≤ D.length)
    (hGammasLen : gammas.length = 1 + (D.length - A) / (s + 1)) :
    let (f, g) := scalarFloorWords D gammas A s
    ∀ r : Fin gammas.length,
      let γ := gammas[r]
      let S_γ := D.filter (fun z =>
        decide (CommRingOps.add (f z) (CommRingOps.mul γ (g z)) = CommRingOps.zero))
      A ≤ S_γ.length ∧
      ∀ G_poly : List F, G_poly.length ≤ d + 1 →
        (S_γ.filter (fun z => decide (RoundPoly.evalCoeffs G_poly z = g z))).length < A - s := by
  dsimp only
  intro r
  let cLen := A - s - 1
  let C := D.take cLen
  let blkStart := cLen + r.1 * (s + 1)
  let T := (D.drop blkStart).take (s + 1)
  let fg := scalarFloorWords D gammas A s
  have hBlockFit : cLen + (r.1 + 1) * (s + 1) ≤ D.length := by
    have hrLt : r.1 < 1 + (D.length - A) / (s + 1) := by omega
    have hrLe : r.1 ≤ (D.length - A) / (s + 1) := by omega
    have hmul := Nat.mul_le_mul_right (s + 1) hrLe
    have hdiv := Nat.div_mul_le_self (D.length - A) (s + 1)
    omega
  have hSubCT : ∀ z ∈ C ++ T, z ∈ D.filter (fun z =>
      decide (CommRingOps.add (fg.1 z) (CommRingOps.mul gammas[r] (fg.2 z)) =
              CommRingOps.zero)) := by
    intro z hz
    rw [List.mem_append] at hz
    rcases hz with hzC | hzT
    · have hzD : z ∈ D := List.mem_of_mem_take hzC
      rw [List.mem_filter]
      refine ⟨hzD, decide_eq_true ?_⟩
      -- On `C`, `g z = 0` and `idx < cLen` so `f z = 0`:
      rcases List.getElem?_of_mem hzC with ⟨i, hi⟩
      have hiLt : i < cLen := by
        have hlt := List.lt_length_of_getElem? hi
        rw [List.length_take] at hlt
        omega
      have hiD : D[i]? = some z := by
        rw [List.getElem?_take_of_lt hiLt] at hi
        exact hi
      have hidx := indexOf?_of_getElem? hD hiD
      have hg0 : fg.2 z = CommRingOps.zero := eval_vanishingPoly_eq_zero_of_mem hzC
      have hf0 : fg.1 z = CommRingOps.zero := by
        dsimp [fg, scalarFloorWords]
        rw [hidx]
        simp [cLen, hiLt]
      rw [hf0, hg0, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    · -- On `T`, `idx = blkStart + j` so `blk = r.1` and `f z = -gammas[r] * g z`:
      rcases List.getElem?_of_mem hzT with ⟨j, hj⟩
      have hjLt : j < s + 1 := by
        have hlt := List.lt_length_of_getElem? hj
        rw [List.length_take] at hlt
        omega
      rw [List.getElem?_take_of_lt hjLt, List.getElem?_drop] at hj
      have hzD : z ∈ D := List.mem_of_getElem? hj
      have hidx := indexOf?_of_getElem? hD hj
      have hgeC : ¬ (blkStart + j < cLen) := by dsimp [blkStart]; omega
      have hblkEq : (blkStart + j - cLen) / (s + 1) = r.1 := by
        have h1 : blkStart + j - cLen = j + r.1 * (s + 1) := by dsimp [blkStart]; omega
        rw [h1, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hjLt, Nat.zero_add]
      have hgetGamma : gammas.getD r.1 CommRingOps.zero = gammas[r] := by
        simp [List.getD, r.2]
      have hfVal : fg.1 z = CommRingOps.neg (CommRingOps.mul gammas[r] (fg.2 z)) := by
        dsimp [fg, scalarFloorWords]
        rw [hidx]
        simp only [cLen, hgeC, ↓reduceIte, hblkEq, r.2, hBlockFit, and_self, hgetGamma]
      rw [List.mem_filter]
      refine ⟨hzD, decide_eq_true ?_⟩
      rw [hfVal, LawfulCommRing.add_left_neg]
  have hndCT : (C ++ T).Nodup := by
    -- `C ++ T` is a sublist of `D` since `C = D.take cLen` and `T` is a slice of `D.drop cLen`:
    have hSubD : List.Sublist (C ++ T) (D.take cLen ++ D.drop cLen) := by
      apply List.Sublist.append List.Sublist.refl
      have h1 : T = ((D.drop cLen).drop (r.1 * (s + 1))).take (s + 1) := by
        dsimp [T, blkStart]
        rw [List.drop_drop, Nat.add_comm cLen]
      rw [h1]
      exact List.Sublist.trans (List.take_sublist _ _) (List.drop_sublist _ _)
    rw [List.take_append_drop] at hSubD
    exact hSubD.nodup hD
  have hLenCT : (C ++ T).length = A := by
    rw [List.length_append, List.length_take, List.length_take, List.length_drop]
    dsimp [cLen, blkStart]
    omega
  constructor
  · have hle := nodup_length_le_of_subset hndCT hSubCT
    omega
  · intro G_poly hGLen
    let S_γ := D.filter (fun z =>
      decide (CommRingOps.add (fg.1 z) (CommRingOps.mul gammas[r] (fg.2 z)) = CommRingOps.zero))
    let diff := RoundPoly.subCoeffs (vanishingPoly C) G_poly
    have hpLen : (vanishingPoly C).length = cLen + 1 := by
      rw [vanishingPoly_length, List.length_take]
      dsimp [cLen]; omega
    have hGLtP : G_poly.length < (vanishingPoly C).length := by rw [hpLen]; dsimp [cLen]; omega
    have hDiffLen : diff.length = cLen + 1 := by
      dsimp [diff]
      rw [RoundPoly.subCoeffs_length, hpLen]
      omega
    have hVanLast : (vanishingPoly C).getD cLen CommRingOps.zero = CommRingOps.one := by
      clear hSubCT hndCT hLenCT hGLtP hDiffLen diff S_γ fg T blkStart
      induction C generalizing cLen with
      | nil => simp at hpLen; subst hpLen; rfl
      | cons c cs ih =>
        have hcsLen : (vanishingPoly cs).length = cs.length + 1 := vanishingPoly_length cs
        have h1 := ih cs.length hcsLen
        have hcEq : cLen = cs.length + 1 := by simp [vanishingPoly_length] at hpLen; omega
        subst hcEq
        have hmapLt : ((vanishingPoly cs).map (CommRingOps.mul c)).length <
            (CommRingOps.zero :: vanishingPoly cs).length := by simp [hcsLen]
        have h0Last : (CommRingOps.zero :: vanishingPoly cs).getD (cs.length + 1) CommRingOps.zero =
            CommRingOps.one := by simpa using h1
        simpa [vanishingPoly, hcsLen] using
          last_subCoeffs_vanishingPoly (CommRingOps.zero :: vanishingPoly cs)
            ((vanishingPoly cs).map (CommRingOps.mul c)) (by simp) h0Last hmapLt
    have hDiffLast : diff.getD cLen CommRingOps.zero = CommRingOps.one := by
      have h := last_subCoeffs_vanishingPoly (vanishingPoly C) G_poly
        (by rw [hpLen]; omega) (by rwa [hpLen, Nat.add_sub_cancel]) hGLtP
      rwa [hpLen, Nat.add_sub_cancel] at h
    rcases exists_nonroot_of_monic_len cLen diff D hDiffLen hDiffLast hD (by dsimp [cLen]; omega)
      with ⟨x₀, _, hx₀Ne⟩
    have hndS : S_γ.Nodup := List.Pairwise.filter _ hD
    have hRoots := @RoundPoly.roots_nodup_length_le F _ _ (LawfulField.toNoZeroDivisors F)
      cLen diff S_γ hndS (by omega) ⟨x₀, hx₀Ne⟩
    have hSubAgree := filter_sub_length_le
      (fun z => decide (RoundPoly.evalCoeffs G_poly z = fg.2 z))
      (fun z => decide (RoundPoly.evalCoeffs diff z = CommRingOps.zero))
      (fun z hz => by
        have hEq : RoundPoly.evalCoeffs G_poly z = fg.2 z := of_decide_eq_true hz
        dsimp [diff, fg, scalarFloorWords] at hEq ⊢
        rw [RoundPoly.evalCoeffs_sub, hEq, LawfulCommRing.sub_self]
        exact decide_eq_true rfl)
      S_γ
    have hLeC : (S_γ.filter (fun z => decide (RoundPoly.evalCoeffs G_poly z = fg.2 z))).length ≤ cLen :=
      Nat.le_trans hSubAgree hRoots
    dsimp [cLen] at hLeC
    omega

/-- Adversarial received-word pair `(f = 0, g = 1_{D \ C})` for `[CWYZ26]` Proposition 6.2 (`s = 0`). -/
def zeroLossAffineWords
    {F : Type} [CommRingOps F] [DecidableEq F]
    (D : List F) (A : Nat) : (F → F) × (F → F) :=
  let C := D.take (A - 1)
  (fun _ => CommRingOps.zero, fun z => if z ∈ C then CommRingOps.zero else CommRingOps.one)

/-- **`#tooth` Proposition 6.2 (`tooth_affine_combiner_zero_loss_linear_floor`)**:
    When **zero** agreement loss ($s = 0$) is demanded, affine combiners revert to $\Omega(n / q)$:
    for ANY `d + 1 < A ≤ D.length` and ANY list `S_nz` of distinct non-zero challenges `β`:
    1. All `(D.length - A + 1) * S_nz.length` challenge pairs `(α, β) = (-β z₀, β)` (`z₀ ∈ D.drop (A - 1)`,
       `β ∈ S_nz`) are **pairwise distinct** (`Nodup`),
    2. Every such pair makes `f(z) + (α + β z) g(z)` vanish on **at least `A` points** of `D` (`P = 0`),
    3. **NO polynomial `G_poly` of degree `≤ d - 1`** agrees with `g` on all `A` points (`s = 0` FAILS!),
    4. Yet `(F = 0, G = 0)` agrees on `A - 1` points (**`s = 1` SUCCEEDS**), proving $s = 1$ is necessary! -/
theorem tooth_affine_combiner_zero_loss_linear_floor
    {F : Type} [LawfulField F] [DecidableEq F]
    (D S_nz : List F) (d A : Nat)
    (hD : D.Nodup)
    (hSnz : S_nz.Nodup)
    (hSnzNe : ∀ β ∈ S_nz, β ≠ CommRingOps.zero)
    (hA_lo : d + 1 < A)
    (hA_hi : A ≤ D.length) :
    let (f, g) := zeroLossAffineWords D A
    let restD := D.drop (A - 1)
    let badPairs := restD.flatMap (fun z₀ => S_nz.map (fun β => (CommRingOps.neg (CommRingOps.mul β z₀), β)))
    badPairs.length = (D.length - A + 1) * S_nz.length ∧
    badPairs.Nodup ∧
    ∀ p ∈ badPairs,
      let S_p := D.filter (fun z =>
        decide (CommRingOps.add (f z)
          (CommRingOps.mul (CommRingOps.add p.1 (CommRingOps.mul p.2 z)) (g z)) = CommRingOps.zero))
      A ≤ S_p.length ∧
      (∀ G_poly : List F, G_poly.length ≤ d →
        ∃ z ∈ S_p, RoundPoly.evalCoeffs G_poly z ≠ g z) ∧
      (S_p.filter (fun z => !(decide (CommRingOps.zero = f z) && decide (CommRingOps.zero = g z)))).length ≤ 1 := by
  dsimp only
  let C := D.take (A - 1)
  let restD := D.drop (A - 1)
  let fg := zeroLossAffineWords D A
  let badPairs := restD.flatMap (fun z₀ => S_nz.map (fun β => (CommRingOps.neg (CommRingOps.mul β z₀), β)))
  have hLenRest : restD.length = D.length - A + 1 := by
    dsimp [restD]; rw [List.length_drop]; omega
  have hBadLen : badPairs.length = (D.length - A + 1) * S_nz.length := by
    have aux : ∀ (zs : List F),
        (zs.flatMap (fun z₀ => S_nz.map (fun β => (CommRingOps.neg (CommRingOps.mul β z₀), β)))).length =
        zs.length * S_nz.length := by
      intro zs
      induction zs with
      | nil => simp
      | cons _ tl ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons, ih]
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    rw [aux restD, hLenRest]
  have hndRest : restD.Nodup := (List.drop_sublist (A - 1) D).nodup hD
  have hBadNodup : badPairs.Nodup := by
    have aux : ∀ {zs : List F}, zs.Nodup →
        (zs.flatMap (fun z₀ => S_nz.map (fun β => (CommRingOps.neg (CommRingOps.mul β z₀), β)))).Nodup
      | [], _ => .nil
      | z₀ :: zs, .cons hnot hnd => by
        simp only [List.flatMap_cons]
        rw [List.nodup_append]
        refine ⟨?_, aux hnd, ?_⟩
        · have mnd : ∀ {bs : List F}, bs.Nodup →
              (bs.map (fun β => (CommRingOps.neg (CommRingOps.mul β z₀), β))).Nodup
            | [], _ => .nil
            | b :: bs, .cons hnb hndb => by
              simp only [List.map]
              refine .cons ?_ (mnd hndb)
              intro q hq heq
              rw [List.mem_map] at hq
              rcases hq with ⟨b', hb', rfl⟩
              cases heq
              exact hnb b' hb' rfl
          exact mnd hSnz
        · intro p₁ hp₁ p₂ hp₂ heq
          subst heq
          rw [List.mem_map] at hp₁
          rw [List.mem_flatMap] at hp₂
          rcases hp₁ with ⟨β₁, hβ₁Mem, rfl⟩
          rcases hp₂ with ⟨z₁, hz₁Mem, hp₂'⟩
          rw [List.mem_map] at hp₂'
          rcases hp₂' with ⟨β₂, _, heq'⟩
          cases heq'
          have hβNe := hSnzNe β₁ hβ₁Mem
          have hmulEq : CommRingOps.mul β₁ z₁ = CommRingOps.mul β₁ z₀ := by
            have hn := congrArg CommRingOps.neg (Prod.mk.inj heq').1
            simpa [LawfulCommRing.neg_neg] using hn
          have hzEq : z₁ = z₀ := by
            have hm := congrArg (CommRingOps.mul (LawfulField.inv β₁)) hmulEq
            simpa [← LawfulCommRing.mul_assoc, LawfulField.inv_mul_cancel hβNe,
                   LawfulCommRing.one_mul] using hm
          exact hnot z₁ hz₁Mem hzEq.symm
    exact aux hndRest
  refine ⟨hBadLen, hBadNodup, ?_⟩
  intro p hp
  rw [List.mem_flatMap] at hp
  rcases hp with ⟨z₀, hz₀Rest, hpMap⟩
  rw [List.mem_map] at hpMap
  rcases hpMap with ⟨β, hβMem, rfl⟩
  have hβNe := hSnzNe β hβMem
  -- Show `S_p = C ++ [z₀]`!
  have hDisjCRest : ∀ x ∈ C, x ∉ restD := by
    have hApp : C ++ restD = D := List.take_append_drop (A - 1) D
    have hndApp : (C ++ restD).Nodup := hApp ▸ hD
    rw [List.nodup_append] at hndApp
    intro x hxC hxR
    exact hndApp.2.2 x hxC x hxR rfl
  have hz₀NotC : z₀ ∉ C := fun hC => hDisjCRest z₀ hC hz₀Rest
  let predP := fun z =>
    decide (CommRingOps.add (fg.1 z)
      (CommRingOps.mul
        (CommRingOps.add (CommRingOps.neg (CommRingOps.mul β z₀)) (CommRingOps.mul β z))
        (fg.2 z)) = CommRingOps.zero)
  have hFiltC : C.filter predP = C := by
    have hall : ∀ z ∈ C, predP z = true := by
      intro z hzC
      dsimp [predP, fg, zeroLossAffineWords]
      simp [C, hzC, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    induction C with
    | nil => rfl
    | cons c cs ih =>
      have hc := hall c (.head _)
      simp only [List.filter, hc, ↓reduceIte]
      exact congrArg (c :: ·) (ih (fun y hy => hall y (.tail _ hy))
        (fun x hx => hDisjCRest x (.tail _ hx)) (fun h => hz₀NotC (.tail _ h)))
  have hFiltRest : restD.filter predP = [z₀] := by
    have hiff : ∀ z ∈ restD, predP z = true ↔ z = z₀ := by
      intro z hzR
      have hzNotC : z ∉ C := fun hC => hDisjCRest z hC hzR
      dsimp [predP, fg, zeroLossAffineWords]
      simp only [C, hzNotC, ↓reduceIte, LawfulCommRing.zero_add, LawfulCommRing.mul_one,
                 decide_eq_true_eq]
      rw [LawfulCommRing.add_comm, ← LawfulCommRing.sub_eq_add_neg, ← LawfulCommRing.mul_sub]
      constructor
      · intro h0
        rcases LawfulField.mul_eq_zero h0 with hb0 | hz0
        · exact False.elim (hβNe hb0)
        · exact LawfulCommRing.sub_eq_zero_iff.mp hz0
      · intro heq; subst heq
        rw [LawfulCommRing.sub_self, LawfulCommRing.mul_zero]
    clear hBadLen hBadNodup hLenRest hFiltC
    induction restD with
    | nil => cases hz₀Rest
    | cons r rs ih =>
      cases hndRest with
      | cons hnotR hndRs =>
        simp only [List.filter]
        if hrz : r = z₀ then
          subst hrz
          have hrTrue : predP r = true := (hiff r (.head _)).mpr rfl
          rw [hrTrue]
          have hrsEmpty : rs.filter predP = [] := by
            have hallFalse : ∀ y ∈ rs, predP y = false := by
              intro y hy
              cases hpy : predP y
              · rfl
              · have hyz : y = r := (hiff y (.tail _ hy)).mp hpy
                exact False.elim (hnotR y hy hyz.symm)
            clear ih hiff hz₀Rest hDisjCRest hnotR hndRs hrTrue
            induction rs with
            | nil => rfl
            | cons y ys ihy =>
              simp [List.filter, hallFalse y (.head _), ihy (fun w hw => hallFalse w (.tail _ hw))]
          rw [hrsEmpty]
        else
          have hrFalse : predP r = false := by
            cases hpr : predP r
            · rfl
            · exact False.elim (hrz ((hiff r (.head _)).mp hpr))
          rw [hrFalse]
          cases hz₀Rest with
          | head => exact False.elim (hrz rfl)
          | tail _ hz₀InRs =>
            exact ih hndRs hz₀InRs (fun x hx => hDisjCRest x) (fun z hz => hiff z (.tail _ hz))
  have hSpEq : D.filter predP = C ++ [z₀] := by
    have hApp : D = C ++ restD := (List.take_append_drop (A - 1) D).symm
    conv => lhs; rw [hApp]
    rw [List.filter_append, hFiltC, hFiltRest]
  have hLenC : C.length = A - 1 := by
    dsimp [C]; rw [List.length_take]; omega
  refine ⟨?_, ?_, ?_⟩
  · change A ≤ (D.filter predP).length
    rw [hSpEq, List.length_append, hLenC, List.length_singleton]
    omega
  · intro G_poly hGLen
    change ∃ z ∈ D.filter predP, RoundPoly.evalCoeffs G_poly z ≠ fg.2 z
    -- Constructively check via `List.find?` whether `G_poly` is non-zero on some `c ∈ C`;
    -- otherwise every `c ∈ C` (`|C| = A - 1 > d`) is a root of `G_poly`, forcing `G_poly(z₀) = 0 ≠ 1 = g(z₀)`.
    match hFind : C.find? (fun c => !(decide (RoundPoly.evalCoeffs G_poly c = CommRingOps.zero))) with
    | some c =>
      have hcMem : c ∈ C := List.mem_of_find?_eq_some hFind
      have hcPred : (!(decide (RoundPoly.evalCoeffs G_poly c = CommRingOps.zero))) = true :=
        List.find?_some hFind
      have hcNe : RoundPoly.evalCoeffs G_poly c ≠ CommRingOps.zero := by
        intro h0
        simp [h0] at hcPred
      have hgc : fg.2 c = CommRingOps.zero := by
        dsimp [fg, zeroLossAffineWords]; simp [C, hcMem]
      refine ⟨c, by rw [hSpEq, List.mem_append]; exact .inl hcMem, ?_⟩
      rwa [hgc]
    | none =>
      refine ⟨z₀, by rw [hSpEq, List.mem_append]; exact .inr (.head _), ?_⟩
      have hgz₀ : fg.2 z₀ = CommRingOps.one := by
        dsimp [fg, zeroLossAffineWords]; simp [C, hz₀NotC]
      rw [hgz₀]
      if hz0Eq : RoundPoly.evalCoeffs G_poly z₀ = CommRingOps.zero then
        rw [hz0Eq]
        exact LawfulField.zero_ne_one
      else
        have hAllRoots : ∀ c ∈ C, RoundPoly.evalCoeffs G_poly c = CommRingOps.zero := by
          intro c hc
          if hc0 : RoundPoly.evalCoeffs G_poly c = CommRingOps.zero then
            exact hc0
          else
            have hFalse := List.find?_eq_none.mp hFind c hc
            simp [hc0] at hFalse
        have hFiltAll :
            C.filter (fun c => decide (RoundPoly.evalCoeffs G_poly c = CommRingOps.zero)) = C := by
          clear hFiltC hFiltRest hSpEq hLenC hFind
          induction C with
          | nil => rfl
          | cons c cs ih =>
            simp [List.filter, hAllRoots c (.head _),
                  ih (fun x hx => hDisjCRest x (.tail _ hx))
                     (fun h => hz₀NotC (.tail _ h))
                     (fun y hy => hAllRoots y (.tail _ hy))]
        have hndC : C.Nodup := (List.take_sublist (A - 1) D).nodup hD
        cases d with
        | zero =>
          have hNil : G_poly = [] := by
            cases G_poly with
            | nil => rfl
            | cons _ _ => simp at hGLen
          subst hNil
          exact False.elim (hz0Eq rfl)
        | succ d' =>
          have hRoots := @RoundPoly.roots_nodup_length_le F _ _ (LawfulField.toNoZeroDivisors F)
            d' G_poly C hndC hGLen ⟨z₀, hz0Eq⟩
          rw [hFiltAll, hLenC] at hRoots
          omega
  · -- At `s = 1`, `(0, 0)` agrees on `C` and fails only at `z₀`:
    change ((D.filter predP).filter
      (fun z => !(decide (CommRingOps.zero = fg.1 z) && decide (CommRingOps.zero = fg.2 z)))).length ≤ 1
    rw [hSpEq, List.filter_append]
    have hCZero : C.filter
        (fun z => !(decide (CommRingOps.zero = fg.1 z) && decide (CommRingOps.zero = fg.2 z))) = [] := by
      have hall : ∀ z ∈ C,
          (decide (CommRingOps.zero = fg.1 z) && decide (CommRingOps.zero = fg.2 z)) = true := by
        intro z hzC
        dsimp [fg, zeroLossAffineWords]
        simp [C, hzC]
      clear hFiltC hFiltRest hSpEq hLenC
      induction C with
      | nil => rfl
      | cons c cs ih =>
        simp [List.filter, hall c (.head _),
              ih (fun x hx => hDisjCRest x (.tail _ hx))
                 (fun h => hz₀NotC (.tail _ h))
                 (fun y hy => hall y (.tail _ hy))]
    rw [hCZero, List.nil_append]
    cases decide (CommRingOps.zero = fg.1 z₀) && decide (CommRingOps.zero = fg.2 z₀) <;> simp


/-! ## §3. Constructive Homogeneous Linear Solver (`gauss_nullspace_witness`) -/

/-- Dot product of two `List F` vectors over `CommRingOps F`. -/
def dotVec {F : Type} [CommRingOps F] : List F → List F → F
  | [], _ => CommRingOps.zero
  | _, [] => CommRingOps.zero
  | a :: as, b :: bs => CommRingOps.add (CommRingOps.mul a b) (dotVec as bs)

/-- Scalar multiple `c · v` of a vector `v : List F`. -/
def scaleVec {F : Type} [CommRingOps F] (c : F) (v : List F) : List F :=
  v.map (CommRingOps.mul c)

/-- Componentwise difference `a - b` of two vectors of equal length. -/
def subVec {F : Type} [CommRingOps F] : List F → List F → List F
  | [], _ => []
  | _, [] => []
  | a :: as, b :: bs => CommRingOps.sub a b :: subVec as bs

/-- Remove element at index `p` from a list. -/
def dropIdx {α : Type} : Nat → List α → List α
  | _, [] => []
  | 0, _ :: xs => xs
  | p + 1, x :: xs => x :: dropIdx p xs

/-- Insert `val` at index `p` in a list. -/
def insertIdxVal {α : Type} : Nat → α → List α → List α
  | 0, val, xs => val :: xs
  | _ + 1, val, [] => [val]
  | p + 1, val, x :: xs => x :: insertIdxVal p val xs

/-- Constructive search for the first non-zero coordinate index in `r : List F`. -/
def findNonzeroIdx {F : Type} [CommRingOps F] [DecidableEq F] : List F → Option Nat
  | [] => none
  | x :: xs =>
    if x = CommRingOps.zero then
      (findNonzeroIdx xs).map (· + 1)
    else
      some 0

/-- Primitive-recursive homogeneous Gaussian pivot solver over `[LawfulField F] [DecidableEq F]`
    (`0` `WellFounded.fix`, `0` classical choice). Given `N` variables and `rows.length < N` equations
    of length `N`, returns a non-zero vector `v` of length `N` orthogonal to every row in `rows`. -/
def solveHomogeneous {F : Type} [LawfulField F] [DecidableEq F] :
    Nat → List (List F) → List F
  | 0, _ => []
  | n + 1, [] => CommRingOps.one :: List.replicate n CommRingOps.zero
  | n + 1, r :: rs =>
    match findNonzeroIdx r with
    | none =>
      CommRingOps.zero :: solveHomogeneous n (rs.map List.tail)
    | some p =>
      let rp := r.getD p CommRingOps.zero
      let invRp := LawfulField.inv rp
      let rDrop := dropIdx p r
      let rs' := rs.map (fun row =>
        let coef := CommRingOps.mul (row.getD p CommRingOps.zero) invRp
        subVec (dropIdx p row) (scaleVec coef rDrop))
      let v' := solveHomogeneous n rs'
      let vp := CommRingOps.neg (CommRingOps.mul invRp (dotVec rDrop v'))
      insertIdxVal p vp v'

private theorem dropIdx_length {α : Type} :
    ∀ (p : Nat) (xs : List α), p < xs.length → (dropIdx p xs).length + 1 = xs.length
  | _, [], h => by simp at h
  | 0, _ :: xs, _ => by simp [dropIdx]
  | p + 1, _ :: xs, h => by
    simp only [List.length_cons] at h ⊢
    have ih := dropIdx_length p xs (by omega)
    simp only [dropIdx, List.length_cons]
    omega

private theorem subVec_length {F : Type} [CommRingOps F] :
    ∀ (a b : List F), a.length = b.length → (subVec a b).length = a.length
  | [], [], _ => rfl
  | _ :: as, _ :: bs, h => by
    simp only [List.length_cons] at h
    simp [subVec, subVec_length as bs (by omega)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

private theorem insertIdxVal_length {α : Type} :
    ∀ (p : Nat) (val : α) (xs : List α), p ≤ xs.length →
      (insertIdxVal p val xs).length = xs.length + 1
  | 0, _, xs, _ => by simp [insertIdxVal]
  | p + 1, val, [], h => by simp at h
  | p + 1, val, x :: xs, h => by
    simp only [List.length_cons] at h
    simp [insertIdxVal, insertIdxVal_length p val xs (by omega)]

private theorem mem_insertIdxVal_of_mem {α : Type} :
    ∀ (p : Nat) (val : α) {z : α} {xs : List α}, z ∈ xs → z ∈ insertIdxVal p val xs
  | 0, _, _, _, hz => .tail _ hz
  | _ + 1, _, _, [], hz => by cases hz
  | p + 1, val, _, _ :: xs, hz => by
    simp only [insertIdxVal]
    cases hz with
    | head => exact .head _
    | tail _ hm => exact .tail _ (mem_insertIdxVal_of_mem p val hm)

private theorem findNonzeroIdx_none {F : Type} [CommRingOps F] [DecidableEq F] :
    ∀ {r : List F}, findNonzeroIdx r = none → ∀ x ∈ r, x = CommRingOps.zero
  | [], _, _, hx => by cases hx
  | x :: xs, h, y, hy => by
    simp only [findNonzeroIdx] at h
    if hx0 : x = CommRingOps.zero then
      rw [if_pos hx0, Option.map_eq_none_iff] at h
      cases hy with
      | head => exact hx0
      | tail _ hm => exact findNonzeroIdx_none h y hm
    else
      rw [if_neg hx0] at h
      cases h

private theorem findNonzeroIdx_some {F : Type} [CommRingOps F] [DecidableEq F] :
    ∀ {r : List F} {p : Nat}, findNonzeroIdx r = some p →
      p < r.length ∧ r.getD p CommRingOps.zero ≠ CommRingOps.zero
  | [], _, h => by cases h
  | x :: xs, p, h => by
    simp only [findNonzeroIdx] at h
    if hx0 : x = CommRingOps.zero then
      rw [if_pos hx0, Option.map_eq_some_iff] at h
      rcases h with ⟨q, hq, rfl⟩
      rcases findNonzeroIdx_some hq with ⟨hqLt, hqNe⟩
      refine ⟨by simp; omega, ?_⟩
      simpa [List.getD] using hqNe
    else
      rw [if_neg hx0] at h
      cases h
      exact ⟨by simp, by simpa [List.getD] using hx0⟩

private theorem dotVec_all_zero {F : Type} [LawfulCommRing F] :
    ∀ (r v : List F), (∀ x ∈ r, x = CommRingOps.zero) → dotVec r v = CommRingOps.zero
  | [], _, _ => rfl
  | _, [], _ => by cases ‹List F› <;> rfl
  | x :: xs, y :: ys, hall => by
    simp only [dotVec, hall x (.head _), LawfulCommRing.zero_mul, LawfulCommRing.zero_add]
    exact dotVec_all_zero xs ys (fun z hz => hall z (.tail _ hz))

private theorem dotVec_scaleVec {F : Type} [LawfulCommRing F] (c : F) :
    ∀ (a v : List F), dotVec (scaleVec c a) v = CommRingOps.mul c (dotVec a v)
  | [], _ => by simp [scaleVec, dotVec, LawfulCommRing.mul_zero]
  | _ :: _, [] => by simp [scaleVec, dotVec, LawfulCommRing.mul_zero]
  | a :: as, b :: bs => by
    simp only [scaleVec, List.map, dotVec]
    rw [dotVec_scaleVec c as bs, LawfulCommRing.mul_assoc, ← LawfulCommRing.left_distrib]

private theorem dotVec_subVec {F : Type} [LawfulCommRing F] :
    ∀ (a b v : List F), a.length = b.length →
      dotVec (subVec a b) v = CommRingOps.sub (dotVec a v) (dotVec b v)
  | [], [], _ => by simp [subVec, dotVec, LawfulCommRing.sub_self]
  | _ :: _, _ :: _, [] => by simp [subVec, dotVec, LawfulCommRing.sub_self]
  | a :: as, b :: bs, x :: xs => fun hlen => by
    simp only [List.length_cons] at hlen
    simp only [subVec, dotVec, dotVec_subVec as bs xs (by omega), LawfulCommRing.sub_mul]
    -- `(a*x - b*x) + (dotA - dotB) = (a*x + dotA) - (b*x + dotB)`
    apply LawfulCommRing.add_left_cancel
      (a := CommRingOps.add (CommRingOps.mul b x) (dotVec bs xs))
    rw [LawfulCommRing.add_sub_cancel_left,
        ← LawfulCommRing.add_assoc,
        LawfulCommRing.add_assoc (CommRingOps.mul b x) (dotVec bs xs) _,
        LawfulCommRing.add_comm (dotVec bs xs) (CommRingOps.sub _ _),
        ← LawfulCommRing.add_assoc (CommRingOps.mul b x),
        LawfulCommRing.add_sub_cancel_left,
        LawfulCommRing.add_assoc,
        LawfulCommRing.add_comm (dotVec bs xs) _,
        LawfulCommRing.add_sub_cancel_left]
  | [], _ :: _, _ => fun h => by simp at h
  | _ :: _, [], _ => fun h => by simp at h

private theorem dotVec_insertIdxVal {F : Type} [LawfulCommRing F] :
    ∀ (p : Nat) (row v : List F) (vp : F),
      row.length = v.length + 1 →
      p < row.length →
      dotVec row (insertIdxVal p vp v) =
        CommRingOps.add (CommRingOps.mul (row.getD p CommRingOps.zero) vp)
          (dotVec (dropIdx p row) v)
  | 0, [], _, _, _, hp => by simp at hp
  | 0, r0 :: rs, v, vp, _, _ => by
    simp [insertIdxVal, dropIdx, dotVec, List.getD]
  | p + 1, [], _, _, _, hp => by simp at hp
  | p + 1, _ :: _, [], _, hlen, hp => by simp at hlen hp; omega
  | p + 1, r0 :: rs, w0 :: ws, vp, hlen, hp => by
    simp only [List.length_cons] at hlen hp
    have ih := dotVec_insertIdxVal p rs ws vp (by omega) (by omega)
    simp only [insertIdxVal, dropIdx, dotVec, ih]
    have hget : (r0 :: rs).getD (p + 1) CommRingOps.zero = rs.getD p CommRingOps.zero := by
      simp [List.getD]
    rw [hget, ← LawfulCommRing.add_assoc,
        LawfulCommRing.add_comm (CommRingOps.mul r0 w0) _,
        LawfulCommRing.add_assoc]

private theorem any_true_of_mem {α : Type} {pred : α → Bool} :
    ∀ {xs : List α} {z : α}, z ∈ xs → pred z = true → xs.any pred = true
  | [], _, hz, _ => by cases hz
  | x :: xs, z, hz, hp => by
    simp only [List.any_cons, Bool.or_eq_true]
    cases hz with
    | head => exact .inl hp
    | tail _ hm => exact .inr (any_true_of_mem hm hp)

private theorem mem_of_any_true {α : Type} {pred : α → Bool} :
    ∀ {xs : List α}, xs.any pred = true → ∃ z ∈ xs, pred z = true
  | [], h => by simp at h
  | x :: xs, h => by
    simp only [List.any_cons, Bool.or_eq_true] at h
    rcases h with hx | hxs
    · exact ⟨x, .head _, hx⟩
    · rcases mem_of_any_true hxs with ⟨z, hz, hp⟩
      exact ⟨z, .tail _ hz, hp⟩

/-- **Constructive Homogeneous Underdetermined Linear Solver (`gauss_nullspace_witness`)**:
    Over ANY `[LawfulField F] [DecidableEq F]`, for any `N` unknowns and `rows.length < N`
    homogeneous linear equations of length `N`, `solveHomogeneous N rows` produces a vector `v`
    of length `N` that has a strictly non-zero entry (`any ≠ 0`) and annihilates every row (`0` choice). -/
theorem gauss_nullspace_witness
    {F : Type} [LawfulField F] [DecidableEq F] :
    ∀ (N : Nat) (rows : List (List F)),
      rows.length < N →
      (∀ row ∈ rows, row.length = N) →
      let v := solveHomogeneous N rows
      v.length = N ∧
      (v.any (fun x => !(decide (x = CommRingOps.zero)))) = true ∧
      ∀ row ∈ rows, dotVec row v = CommRingOps.zero
  | 0, _, hlt, _ => by omega
  | n + 1, [], _, _ => by
    dsimp [solveHomogeneous]
    refine ⟨by simp, ?_, by intro _ h; cases h⟩
    simp [LawfulField.one_ne_zero]
  | n + 1, r :: rs, hlt, hlen => by
    simp only [List.length_cons] at hlt
    have hrLen : r.length = n + 1 := hlen r (.head _)
    have hrsLen : ∀ row ∈ rs, row.length = n + 1 := fun row h => hlen row (.tail _ h)
    dsimp only [solveHomogeneous]
    cases hFind : findNonzeroIdx r with
    | none =>
      dsimp only
      let rsTail := rs.map List.tail
      have hTailLt : rsTail.length < n := by simp [rsTail]; omega
      have hTailLen : ∀ row' ∈ rsTail, row'.length = n := by
        intro row' hmem
        rw [List.mem_map] at hmem
        rcases hmem with ⟨row, hrow, rfl⟩
        have hl := hrsLen row hrow
        cases row with
        | nil => simp at hl
        | cons _ tl => simp at hl ⊢; exact hl
      rcases gauss_nullspace_witness n rsTail hTailLt hTailLen with ⟨hvLen, hvAny, hvZero⟩
      refine ⟨by simp [hvLen], ?_, ?_⟩
      · simp only [List.any_cons, hvAny, Bool.or_true]
      · intro row hrow
        cases hrow with
        | head =>
          exact dotVec_all_zero r _ (findNonzeroIdx_none hFind)
        | tail _ hm =>
          have hl := hrsLen row hm
          cases row with
          | nil => simp at hl
          | cons c cs =>
            simp only [dotVec, LawfulCommRing.mul_zero, LawfulCommRing.zero_add]
            exact hvZero cs (List.mem_map.mpr ⟨c :: cs, hm, rfl⟩)
    | some p =>
      dsimp only
      rcases findNonzeroIdx_some hFind with ⟨hpLt, hrpNe⟩
      let rp := r.getD p CommRingOps.zero
      let invRp := LawfulField.inv rp
      let rDrop := dropIdx p r
      have hrDropLen : rDrop.length = n := by
        have h := dropIdx_length p r hpLt
        omega
      let elimRow := fun (row : List F) =>
        subVec (dropIdx p row) (scaleVec (CommRingOps.mul (row.getD p CommRingOps.zero) invRp) rDrop)
      let rs' := rs.map elimRow
      have hrs'Lt : rs'.length < n := by simp [rs']; omega
      have hrs'Len : ∀ row' ∈ rs', row'.length = n := by
        intro row' hmem
        rw [List.mem_map] at hmem
        rcases hmem with ⟨row, hrow, rfl⟩
        have hl := hrsLen row hrow
        have hd : (dropIdx p row).length = n := by
          have h := dropIdx_length p row (by omega)
          omega
        dsimp [elimRow]
        rw [subVec_length]
        · exact hd
        · simp [scaleVec, hd, hrDropLen]
      rcases gauss_nullspace_witness n rs' hrs'Lt hrs'Len with ⟨hvLen, hvAny, hvZero⟩
      let v' := solveHomogeneous n rs'
      let vp := CommRingOps.neg (CommRingOps.mul invRp (dotVec rDrop v'))
      have hpLe : p ≤ v'.length := by rw [hvLen]; omega
      refine ⟨?_, ?_, ?_⟩
      · rw [insertIdxVal_length p vp v' hpLe, hvLen]
      · rcases mem_of_any_true hvAny with ⟨z, hzMem, hzPred⟩
        exact any_true_of_mem (mem_insertIdxVal_of_mem p vp hzMem) hzPred
      · intro row hrow
        have hrowLen : row.length = n + 1 := hlen row hrow
        rw [dotVec_insertIdxVal p row v' vp (by omega) (by omega)]
        cases hrow with
        | head =>
          -- Pivot row `r`: `rp * (-invRp * dot(rDrop, v')) + dot(rDrop, v') = 0`
          change CommRingOps.add (CommRingOps.mul rp vp) (dotVec rDrop v') = CommRingOps.zero
          dsimp [vp]
          rw [LawfulCommRing.mul_neg, ← LawfulCommRing.mul_assoc,
              LawfulField.mul_inv_cancel hrpNe, LawfulCommRing.one_mul,
              LawfulCommRing.add_left_neg]
        | tail _ hm =>
          -- Eliminated row `row ∈ rs`:
          have hElimZero : dotVec (elimRow row) v' = CommRingOps.zero :=
            hvZero (elimRow row) (List.mem_map.mpr ⟨row, hm, rfl⟩)
          have hdLen : (dropIdx p row).length = n := by
            have h := dropIdx_length p row (by omega)
            omega
          dsimp [elimRow] at hElimZero
          rw [dotVec_subVec _ _ v' (by simp [scaleVec, hdLen, hrDropLen]),
              dotVec_scaleVec] at hElimZero
          have hEqDrop : dotVec (dropIdx p row) v' =
              CommRingOps.mul (CommRingOps.mul (row.getD p CommRingOps.zero) invRp)
                (dotVec rDrop v') :=
            LawfulCommRing.sub_eq_zero_iff.mp hElimZero
          rw [hEqDrop]
          dsimp [vp]
          rw [LawfulCommRing.mul_neg, LawfulCommRing.mul_assoc,
              LawfulCommRing.add_left_neg]

/-- Geometric power vector `[1, z, z^2, ..., z^(m-1)]` connecting `dotVec` directly to `evalCoeffs`. -/
def geomVec {F : Type} [CommRingOps F] (z : F) : Nat → List F
  | 0 => []
  | k + 1 => CommRingOps.one :: (geomVec z k).map (CommRingOps.mul z)

theorem geomVec_length {F : Type} [CommRingOps F] (z : F) :
    ∀ (m : Nat), (geomVec z m).length = m
  | 0 => rfl
  | k + 1 => by simp [geomVec, geomVec_length z k]

theorem dotVec_geomVec_eq_evalCoeffs {F : Type} [LawfulCommRing F] (z : F) :
    ∀ (m : Nat) (coeffs : List F),
      coeffs.length = m →
      dotVec (geomVec z m) coeffs = RoundPoly.evalCoeffs coeffs z
  | 0, [], _ => rfl
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], h => by simp at h
  | k + 1, c :: cs, h => by
    simp only [List.length_cons] at h
    have hcs : cs.length = k := by omega
    have hscale : dotVec ((geomVec z k).map (CommRingOps.mul z)) cs =
        CommRingOps.mul z (dotVec (geomVec z k) cs) :=
      dotVec_scaleVec z (geomVec z k) cs
    simp only [geomVec, dotVec, LawfulCommRing.one_mul, hscale,
               dotVec_geomVec_eq_evalCoeffs z k cs hcs, RoundPoly.evalCoeffs]

theorem dotVec_append_eq {F : Type} [LawfulCommRing F] :
    ∀ (a b x y : List F), a.length = x.length →
      dotVec (a ++ b) (x ++ y) = CommRingOps.add (dotVec a x) (dotVec b y)
  | [], b, [], y, _ => by simp [dotVec, LawfulCommRing.zero_add]
  | a0 :: as, b, x0 :: xs, y, h => by
    simp only [List.length_cons] at h
    simp only [List.cons_append, dotVec, dotVec_append_eq as b xs y (by omega),
               LawfulCommRing.add_assoc]
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h

theorem dotVec_replicate_zero {F : Type} [LawfulCommRing F] :
    ∀ (m : Nat) (v : List F), dotVec (List.replicate m CommRingOps.zero) v = CommRingOps.zero
  | 0, _ => rfl
  | m + 1, [] => rfl
  | m + 1, _ :: vs => by
    simp [List.replicate, dotVec, LawfulCommRing.zero_mul, LawfulCommRing.zero_add,
          dotVec_replicate_zero m vs]
