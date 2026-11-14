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

4. **Bivariate list-decoding algebra**:
   - `guruswami_sudan_interpolation`: weighted monomial coordinates, formal binomial Hasse
     derivatives, and a nonzero Gaussian-elimination witness for arbitrary multiplicity.
   - `GsUniPoly`: canonical constructive integral domain `F[X]`; `gs_formal_root_bound` uses
     nonzero coefficients, including polynomials that vanish everywhere on a finite field.
   - `guruswami_sudan_polynomial_list_bound`: at most D distinct formal polynomial roots of
     a nonzero Y-degree-at-most-D polynomial; `sudan_factor_and_list_bound` supplies the
     weighted-degree/agreement factor argument for multiplicity one.
   - `guruswami_sudan_factor` / `guruswami_sudan_factor_and_list_bound` /
     `guruswami_sudan_agreement_list_bound`: the factor theorem and list bound at ARBITRARY
     multiplicity `m`, for an interpolant in the ideal power `(X - x, Y - y)^m` at each point
     (`GsMultiplicity`, stated through the synthetic-division Taylor shift `gsTaylor`).
   - `hem_gs_constructive_interpolation` applies interpolation to all 46 deployed rows.
     OPEN: the interpolation output is a coefficient vector whose binomial Hasse evaluations
     (`gsHasseEval`) vanish; that this vector, assembled into `List (GsUniPoly F)`, satisfies
     `GsMultiplicity` (binomial Hasse derivative = Taylor coefficient, plus the flat-to-nested
     coefficient bookkeeping) is not proved here, so the `≤ D` list bound is established for
     every interpolant of that shape rather than unconditionally per row. The trivariate
     affine explainer theorem (`[CWYZ26]` Theorem 4.8) is a further separate obligation.

5. **§5. Finite `Theorem 4.8 + Theorem 5.1` Witness Verifier Bound to the Deployed `Hem` WHIR Schedule**:
   - `hemStageGeometry` / `hemJohnsonMinQueries` mirror `pcs.rs::stage_geometry` and
     `WhirSecurityRegime::minimum_queries`; `hemJohnsonQromWitnessTable` is the verbatim
     `affine_schedule.rs::WITNESSES` table (`B = A - 1`).
   - `checkWhirAffineWitness` checks the paper's side conditions (`m, D ≥ 1`,
     `M = min {D, ⌊(mA - D - 1)/d⌋} ≥ 1`, exact Equation `(4.5)`, `B^2 > n (d + 1)`,
     `(A - 1)^2 > n d`) and the exact distinct-fiber query bound
     `affineFallingFactorial (A + s_i) q_i * 2^bits < affineFallingFactorial n q_i`.
   - `hem_johnson_qrom_witnesses_cover_every_canonical_stage` kernel-decides the Rust coverage test
     for every `num_vars ∈ 2..=24`.
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
  zero_ne_one : (CommRingOps.zero : F) ≠ (CommRingOps.one : F)
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
@[instance_reducible] def toNoZeroDivisors (F : Type) [LawfulField F] [DecidableEq F] : NoZeroDivisors F where
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
  | 0, m, d, _, hd => by simpa [affineFoldDegreeIter] using hd
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
    affineFoldDegreeIter s (2 ^ ℓ - 1) ≤ 2 ^ (ℓ - s) + 1 := by
  have hpos : 0 < 2 ^ ℓ := Nat.two_pow_pos ℓ
  exact affineFoldDegreeIter_le_of_le s ℓ (2 ^ ℓ - 1) hs (by omega)

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
  have cancel_alpha : ∀ a x y : F,
      CommRingOps.sub (CommRingOps.add a x) (CommRingOps.add a y) = CommRingOps.sub x y := by
    intro a x y
    apply LawfulCommRing.add_left_cancel (a := CommRingOps.add a y)
    rw [LawfulCommRing.add_sub_cancel_left,
        LawfulCommRing.add_assoc a y (CommRingOps.sub x y),
        LawfulCommRing.add_sub_cancel_left]
  rw [cancel_alpha α₁, cancel_alpha α₂,
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
    rw [LawfulCommRing.add_comm (CommRingOps.sub y₀ y₁) y₁,
        LawfulCommRing.add_sub_cancel_left,
        ← hDiff, LawfulCommRing.mul_sub,
        ← LawfulCommRing.add_assoc
            (CommRingOps.sub (CommRingOps.mul β' z₀) (CommRingOps.mul β' z₁)) α'
            (CommRingOps.mul β' z₁),
        LawfulCommRing.add_comm
            (CommRingOps.sub (CommRingOps.mul β' z₀) (CommRingOps.mul β' z₁)) α',
        LawfulCommRing.add_assoc α'
            (CommRingOps.sub (CommRingOps.mul β' z₀) (CommRingOps.mul β' z₁))
            (CommRingOps.mul β' z₁),
        LawfulCommRing.add_comm
            (CommRingOps.sub (CommRingOps.mul β' z₀) (CommRingOps.mul β' z₁))
            (CommRingOps.mul β' z₁),
        LawfulCommRing.add_sub_cancel_left,
        h₀']
  rcases affine_line_unique_of_two_points hz (h₀.trans h₀'.symm) (h₁.trans h₁'.symm) with ⟨rfl, rfl⟩
  rfl

/-- Cartesian product challenge pool `S × S` preserving duplicate-freedom. -/
@[expose] def prodPool {α : Type} (S : List α) : List (α × α) :=
  S.flatMap (fun a => S.map (fun b => (a, b)))

theorem prodPool_length {α : Type} (S : List α) :
    (prodPool S).length = S.length * S.length := by
  unfold prodPool
  have hrec : ∀ (xs B : List α),
      (xs.flatMap (fun x => B.map (fun b => (x, b)))).length = xs.length * B.length := by
    intro xs B
    induction xs with
    | nil => simp
    | cons _ rest ihr =>
      simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons]
      rw [ihr, Nat.add_mul, Nat.one_mul, Nat.add_comm]
  exact hrec S S

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
    exact hnot b hb' rfl

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
      simp only [hxy, ↓reduceIte]
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
      simp
    else
      simp only [hx, decide_false]
      exact filter_eq_max_one_of_nodup target hnd

private theorem filter_sub_length_le {α : Type} (p q : α → Bool) (hpq : ∀ x, p x = true → q x = true) :
    ∀ (xs : List α), (xs.filter p).length ≤ (xs.filter q).length
  | [] => Nat.le_refl 0
  | x :: xs => by
    have ih := filter_sub_length_le p q hpq xs
    simp only [List.filter]
    cases hpx : p x
    · cases hqx : q x <;> simp <;> omega
    · rw [hpq x hpx]
      simp only [List.length_cons]
      exact Nat.succ_le_succ ih

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
    · intro a haS
      let target := CommRingOps.neg
        (CommRingOps.mul (CommRingOps.add Δ₀ (CommRingOps.mul a Δ₁)) (LawfulField.inv Δ₂))
      have hmap : ((S.map (fun b => (a, b))).filter
          (fun p => decide (evalAffineDuet Δ₀ Δ₁ Δ₂ p.1 p.2 = CommRingOps.zero))).length =
          (S.filter (fun b => decide (evalAffineDuet Δ₀ Δ₁ Δ₂ a b = CommRingOps.zero))).length := by
        clear haS hS
        induction S with
        | nil => rfl
        | cons b bs ih =>
          simp only [List.map, List.filter]
          cases decide (evalAffineDuet Δ₀ Δ₁ Δ₂ a b = CommRingOps.zero) <;>
            simp only [List.length_cons, ih]
      rw [hmap]
      have hsub := filter_sub_length_le
        (fun b => decide (evalAffineDuet Δ₀ Δ₁ Δ₂ a b = CommRingOps.zero))
        (fun b => decide (b = target))
        (fun b hb => by
          have hev : evalAffineDuet Δ₀ Δ₁ Δ₂ a b = CommRingOps.zero := of_decide_eq_true hb
          unfold evalAffineDuet at hev
          rw [← LawfulCommRing.add_assoc Δ₀ (CommRingOps.mul a Δ₁) (CommRingOps.mul b Δ₂)] at hev
          have hmul0 : CommRingOps.mul b Δ₂ =
              CommRingOps.neg (CommRingOps.add Δ₀ (CommRingOps.mul a Δ₁)) := by
            apply LawfulCommRing.add_left_cancel
              (a := CommRingOps.add Δ₀ (CommRingOps.mul a Δ₁))
            rw [LawfulCommRing.add_right_neg]
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
    simp only [unorderedPairs, List.length_append, List.length_map, List.length_cons,
               Nat.add_sub_cancel]
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
    · dsimp only
      exact fun heq => hnot x (heq ▸ hy) rfl
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
      injection h with hxEq htlEq
      subst hxEq
      have hz₁InFilt : z₁ ∈ xs.filter pred := by rw [htlEq]; exact .head _
      have hz₁InXs : z₁ ∈ xs := (List.mem_filter.mp hz₁InFilt).1
      simp only [unorderedPairs, List.mem_append, List.mem_map]
      exact .inl ⟨z₁, hz₁InXs, rfl⟩

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
    rw [LawfulCommRing.add_assoc (RoundPoly.evalCoeffs F_poly z)
          (CommRingOps.mul (CommRingOps.add α (CommRingOps.mul β z)) (g z)) _,
        LawfulCommRing.add_sub_cancel_left,
        hEq,
        LawfulCommRing.add_comm (RoundPoly.evalCoeffs F_poly z)
          (CommRingOps.mul (CommRingOps.add α (CommRingOps.mul β z)) (g z)),
        LawfulCommRing.add_assoc
          (CommRingOps.mul (CommRingOps.add α (CommRingOps.mul β z)) (g z))
          (RoundPoly.evalCoeffs F_poly z) _,
        LawfulCommRing.add_sub_cancel_left,
        LawfulCommRing.add_comm (f z) _]
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
    exact Nat.max_eq_left (by omega)

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
  | [_], _ :: _, _, _, hlt => by simp at hlt
  | c₀ :: c₁ :: cs, [], _, hlast, _ => by
    have hpos : 0 < (c₁ :: cs).length := by simp
    have ih := last_subCoeffs_vanishingPoly (c₁ :: cs) [] hpos hlast (by simp)
    simpa [RoundPoly.subCoeffs] using ih
  | c₀ :: c₁ :: cs, g₀ :: gs, _, hlast, hlt => by
    have hpos : 0 < (c₁ :: cs).length := by simp
    have hlt' : gs.length < (c₁ :: cs).length := by simp at hlt ⊢; omega
    have ih := last_subCoeffs_vanishingPoly (c₁ :: cs) gs hpos hlast hlt'
    simpa [RoundPoly.subCoeffs] using ih

private theorem vanishingPoly_last_one
    {F : Type} [LawfulField F] :
    ∀ (C : List F), (vanishingPoly C).getD C.length CommRingOps.zero = CommRingOps.one
  | [] => rfl
  | c :: cs => by
    have hcsLen : (vanishingPoly cs).length = cs.length + 1 := vanishingPoly_length cs
    have h0Last : (CommRingOps.zero :: vanishingPoly cs).getD
        ((CommRingOps.zero :: vanishingPoly cs).length - 1) CommRingOps.zero =
        CommRingOps.one := by
      simp only [List.length_cons, Nat.add_sub_cancel, hcsLen]
      simpa [List.getD] using vanishingPoly_last_one cs
    have hmapLt : ((vanishingPoly cs).map (CommRingOps.mul c)).length <
        (CommRingOps.zero :: vanishingPoly cs).length := by simp [hcsLen]
    have h := last_subCoeffs_vanishingPoly
      (CommRingOps.zero :: vanishingPoly cs)
      ((vanishingPoly cs).map (CommRingOps.mul c))
      (by simp) h0Last hmapLt
    simpa [vanishingPoly, hcsLen] using h

private theorem lt_length_of_getElem?_eq_some {α : Type} :
    ∀ {xs : List α} {i : Nat} {x : α}, xs[i]? = some x → i < xs.length
  | [], _, _, h => by simp at h
  | _ :: _, 0, _, _ => by simp
  | _ :: xs, i + 1, _, h =>
    Nat.succ_lt_succ (lt_length_of_getElem?_eq_some (by simpa using h))

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
  | 0, _ :: _ :: _, _, hlen, _, _, _ => by cases hlen
  | k + 1, p, [], _, _, _, hU => by cases hU
  | k + 1, p, u :: us, hlen, hlast, .cons hnot hnd, hU => by
    if hev : RoundPoly.evalCoeffs p u = CommRingOps.zero then
      let q := RoundPoly.quotLinear p u
      have hqLen : q.length = k + 1 := by
        dsimp [q]; rw [RoundPoly.quotLinear_length, hlen]; rfl
      have hqLast : q.getD k CommRingOps.zero = CommRingOps.one := by
        have aux : ∀ (m : Nat) (xs : List F),
            xs.length = m + 2 →
            (RoundPoly.quotLinear xs u).getD m CommRingOps.zero =
              xs.getD (m + 1) CommRingOps.zero := by
          intro m xs hxs
          induction m generalizing xs with
          | zero =>
            rcases xs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
            · cases hxs
            · cases hxs
            · simp [RoundPoly.quotLinear, RoundPoly.evalCoeffs,
                    LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
            · cases hxs
          | succ m' ihm =>
            rcases xs with _ | ⟨a, _ | ⟨b, tl⟩⟩
            · cases hxs
            · cases hxs
            · have htl : (b :: tl).length = m' + 2 := Nat.succ.inj hxs
              simpa [RoundPoly.quotLinear] using ihm (b :: tl) htl
        rw [aux k p hlen, hlast]
      have hUsLen : k + 1 ≤ us.length := Nat.le_of_succ_le_succ hU
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
  termination_by structural k => k

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

private theorem getElem_inj_of_nodup {α : Type} :
    ∀ {xs : List α}, xs.Nodup → ∀ (i j : Nat) (hi : i < xs.length) (hj : j < xs.length),
      xs[i] = xs[j] → i = j
  | [], _, _, _, hi, _, _ => by simp at hi
  | _ :: _, _, 0, 0, _, _, _ => rfl
  | _ :: xs, .cons hnot _, 0, j + 1, _, hj, heq => by
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
    have hj' : j < xs.length := by simp at hj; omega
    exact False.elim (hnot (xs[j]'hj') (List.getElem_mem hj') heq)
  | _ :: xs, .cons hnot _, i + 1, 0, hi, _, heq => by
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
    have hi' : i < xs.length := by simp at hi; omega
    exact False.elim (hnot (xs[i]'hi') (List.getElem_mem hi') heq.symm)
  | _ :: xs, .cons _ hnd, i + 1, j + 1, hi, hj, heq => by
    simp only [List.getElem_cons_succ] at heq
    exact congrArg (· + 1) (getElem_inj_of_nodup hnd i j
      (by simp at hi; omega) (by simp at hj; omega) heq)

/-- **`#tooth` Proposition 6.1 (`tooth_scalar_combiner_linear_n_over_q_floor`)**:
    For ANY degree `d`, loss `s`, threshold `A` (`d + s + 1 < A`, `A ≤ D.length`), and ANY list
    `gammas` of `1 + (D.length - A) / (s + 1)` distinct non-zero challenges in `S`:
    every `γ ∈ gammas` is a pairwise-distinct non-zero challenge making `f + γ g` vanish on
    **at least `A` points of `D`** (`P = 0`), yet **NO polynomial `G_poly` of degree `≤ d`** agrees
    with `g` on `≥ A - s` of those points — proving scalar combiners incur
    `≥ (1 + ⌊(n - A)/(s + 1)⌋) / |S| = Ω(n/q)` error even for `s ≥ 1`! -/
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
    (∀ i j : Fin gammas.length, i ≠ j → gammas[i] ≠ gammas[j]) ∧
    ∀ r : Fin gammas.length,
      let γ := gammas[r]
      let S_γ := D.filter (fun z =>
        decide (CommRingOps.add (f z) (CommRingOps.mul γ (g z)) = CommRingOps.zero))
      γ ≠ CommRingOps.zero ∧
      A ≤ S_γ.length ∧
      ∀ G_poly : List F, G_poly.length ≤ d + 1 →
        (S_γ.filter (fun z => decide (RoundPoly.evalCoeffs G_poly z = g z))).length < A - s := by
  dsimp only
  refine ⟨fun i j hij heq => hij (Fin.ext (getElem_inj_of_nodup hGammas i.1 j.1 i.2 j.2 heq)), ?_⟩
  intro r
  let cLen := A - s - 1
  have hcLen : cLen = A - s - 1 := rfl
  let C := D.take cLen
  let blkStart := cLen + r.1 * (s + 1)
  have hblkStart : blkStart = cLen + r.1 * (s + 1) := rfl
  let T := (D.drop blkStart).take (s + 1)
  let fg := scalarFloorWords D gammas A s
  have hBlockFit : cLen + (r.1 + 1) * (s + 1) ≤ D.length := by
    have hrLt : r.1 < 1 + (D.length - A) / (s + 1) := by omega
    have hrLe : r.1 ≤ (D.length - A) / (s + 1) := by omega
    have hmul := Nat.mul_le_mul_right (s + 1) hrLe
    have hdiv := Nat.div_mul_le_self (D.length - A) (s + 1)
    have hexp : (r.1 + 1) * (s + 1) = r.1 * (s + 1) + (s + 1) := Nat.add_one_mul r.1 (s + 1)
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
      rcases List.getElem?_of_mem hzC with ⟨i, hi⟩
      have hiLt : i < cLen := by
        have hlt := lt_length_of_getElem?_eq_some hi
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
    · rcases List.getElem?_of_mem hzT with ⟨j, hj⟩
      have hjLt : j < s + 1 := by
        have hlt := lt_length_of_getElem?_eq_some hj
        rw [List.length_take] at hlt
        omega
      rw [List.getElem?_take_of_lt hjLt, List.getElem?_drop] at hj
      have hzD : z ∈ D := List.mem_of_getElem? hj
      have hidx := indexOf?_of_getElem? hD hj
      have hgeC : ¬ (blkStart + j < cLen) := by omega
      have hblkEq : (blkStart + j - cLen) / (s + 1) = r.1 := by
        have h1 : blkStart + j - cLen = j + r.1 * (s + 1) := by omega
        rw [h1, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hjLt, Nat.zero_add]
      have hgetGamma : gammas.getD r.1 CommRingOps.zero = gammas[r] := by
        simp [List.getD, r.2]
      have hfVal : fg.1 z = CommRingOps.neg (CommRingOps.mul gammas[r] (fg.2 z)) := by
        dsimp [fg, scalarFloorWords]
        rw [hidx]
        simp only [cLen, hgeC, ↓reduceIte, hblkEq, r.2, hBlockFit, and_self, hgetGamma]
        rfl
      rw [List.mem_filter]
      refine ⟨hzD, decide_eq_true ?_⟩
      rw [hfVal, LawfulCommRing.add_left_neg]
  have hndCT : (C ++ T).Nodup := by
    have hSubD : List.Sublist (C ++ T) (D.take cLen ++ D.drop cLen) := by
      apply List.Sublist.append (List.Sublist.refl _)
      have h1 : T = ((D.drop cLen).drop (r.1 * (s + 1))).take (s + 1) := by
        dsimp [T, blkStart]
        rw [List.drop_drop, Nat.add_comm cLen]
      rw [h1]
      exact List.Sublist.trans (List.take_sublist _ _) (List.drop_sublist _ _)
    rw [List.take_append_drop] at hSubD
    exact hSubD.nodup hD
  have hLenC : C.length = cLen := List.length_take_of_le (by omega)
  have hLenT : T.length = s + 1 := by
    dsimp [T]
    apply List.length_take_of_le
    rw [List.length_drop]
    have hexp : (r.1 + 1) * (s + 1) = r.1 * (s + 1) + (s + 1) := Nat.add_one_mul r.1 (s + 1)
    omega
  have hLenCT : (C ++ T).length = A := by
    rw [List.length_append, hLenC, hLenT]
    omega
  refine ⟨hGammasNz gammas[r] (List.getElem_mem r.2), ?_, ?_⟩
  · have hle := nodup_length_le_of_subset hndCT hSubCT
    rw [hLenCT] at hle
    exact hle
  · intro G_poly hGLen
    let S_γ := D.filter (fun z =>
      decide (CommRingOps.add (fg.1 z) (CommRingOps.mul gammas[r] (fg.2 z)) = CommRingOps.zero))
    let diff := RoundPoly.subCoeffs (vanishingPoly C) G_poly
    have hpLen : (vanishingPoly C).length = cLen + 1 := by
      rw [vanishingPoly_length, hLenC]
    have hGLtP : G_poly.length < (vanishingPoly C).length := by rw [hpLen]; omega
    have hDiffLen : diff.length = cLen + 1 := by
      dsimp [diff]
      rw [RoundPoly.subCoeffs_length, hpLen]
      exact Nat.max_eq_left (by omega)
    have hVanLast : (vanishingPoly C).getD cLen CommRingOps.zero = CommRingOps.one := by
      rw [← hLenC]
      exact vanishingPoly_last_one C
    have hDiffLast : diff.getD cLen CommRingOps.zero = CommRingOps.one := by
      have h := last_subCoeffs_vanishingPoly (vanishingPoly C) G_poly
        (by rw [hpLen]; omega) (by rwa [hpLen, Nat.add_sub_cancel]) hGLtP
      rwa [hpLen, Nat.add_sub_cancel] at h
    rcases exists_nonroot_of_monic_len cLen diff D hDiffLen hDiffLast hD (by omega)
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
    change (S_γ.filter (fun z => decide (RoundPoly.evalCoeffs G_poly z = fg.2 z))).length < A - s
    omega

private theorem filter_eq_self_of_all {α : Type} (p : α → Bool) :
    ∀ (xs : List α), (∀ x ∈ xs, p x = true) → xs.filter p = xs
  | [], _ => rfl
  | x :: xs, h => by
    simp [List.filter, h x (.head _), filter_eq_self_of_all p xs (fun y hy => h y (.tail _ hy))]

private theorem filter_eq_nil_of_all_false {α : Type} (p : α → Bool) :
    ∀ (xs : List α), (∀ x ∈ xs, p x = false) → xs.filter p = []
  | [], _ => rfl
  | x :: xs, h => by
    simp [List.filter, h x (.head _), filter_eq_nil_of_all_false p xs (fun y hy => h y (.tail _ hy))]

private theorem filter_eq_singleton_of_nodup_iff {α : Type} (p : α → Bool) (z₀ : α) :
    ∀ {xs : List α}, xs.Nodup → z₀ ∈ xs → (∀ x ∈ xs, p x = true ↔ x = z₀) → xs.filter p = [z₀]
  | [], _, hz, _ => by cases hz
  | x :: xs, .cons hnot hnd, hz, hiff => by
    simp only [List.filter]
    cases hpx : p x
    · have hne : z₀ ≠ x := by
        intro heq; subst heq
        have ht := (hiff z₀ (.head _)).mpr rfl
        rw [hpx] at ht; cases ht
      cases hz with
      | head => exact False.elim (hne rfl)
      | tail _ hzs =>
        exact filter_eq_singleton_of_nodup_iff p z₀ hnd hzs (fun y hy => hiff y (.tail _ hy))
    · have hxEq : x = z₀ := (hiff x (.head _)).mp hpx
      subst hxEq
      rw [filter_eq_nil_of_all_false p xs]
      intro y hy
      cases hpy : p y
      · rfl
      · exact False.elim (hnot y hy ((hiff y (.tail _ hy)).mp hpy).symm)

private theorem zeroLossRow_nodup
    {F : Type} [LawfulField F] (z₀ : F) :
    ∀ {bs : List F}, bs.Nodup →
      (bs.map (fun β => (CommRingOps.neg (CommRingOps.mul β z₀), β))).Nodup
  | [], _ => .nil
  | b :: bs, .cons hnb hndb => by
    simp only [List.map]
    refine .cons ?_ (zeroLossRow_nodup z₀ hndb)
    intro q hq heq
    rw [List.mem_map] at hq
    rcases hq with ⟨b', hb', rfl⟩
    have hbEq : b = b' := (Prod.mk.inj heq).2
    exact hnb b' hb' hbEq

private theorem zeroLossBadPairs_nodup
    {F : Type} [LawfulField F] [DecidableEq F]
    {S_nz : List F} (hSnz : S_nz.Nodup) (hSnzNe : ∀ β ∈ S_nz, β ≠ CommRingOps.zero) :
    ∀ {zs : List F}, zs.Nodup →
      (zs.flatMap (fun z₀ => S_nz.map (fun β => (CommRingOps.neg (CommRingOps.mul β z₀), β)))).Nodup
  | [], _ => .nil
  | z₀ :: zs, .cons hnot hnd => by
    simp only [List.flatMap_cons]
    rw [List.nodup_append]
    refine ⟨zeroLossRow_nodup z₀ hSnz, zeroLossBadPairs_nodup hSnz hSnzNe hnd, ?_⟩
    intro p₁ hp₁ p₂ hp₂ heq
    subst heq
    rw [List.mem_map] at hp₁
    rw [List.mem_flatMap] at hp₂
    rcases hp₁ with ⟨β₁, hβ₁Mem, rfl⟩
    rcases hp₂ with ⟨z₁, hz₁Mem, hp₂'⟩
    rw [List.mem_map] at hp₂'
    rcases hp₂' with ⟨β₂, _, heq'⟩
    have hβEq : β₂ = β₁ := (Prod.mk.inj heq').2
    subst hβEq
    have hβNe := hSnzNe β₂ hβ₁Mem
    have hmulEq : CommRingOps.mul β₂ z₁ = CommRingOps.mul β₂ z₀ := by
      have hn := congrArg CommRingOps.neg (Prod.mk.inj heq').1
      simpa [LawfulCommRing.neg_neg] using hn
    have hzEq : z₁ = z₀ := by
      have hm := congrArg (CommRingOps.mul (LawfulField.inv β₂)) hmulEq
      simpa [← LawfulCommRing.mul_assoc, LawfulField.inv_mul_cancel hβNe,
             LawfulCommRing.one_mul] using hm
    exact hnot z₁ hz₁Mem hzEq.symm

private theorem exists_nonroot_or_all_roots
    {F : Type} [CommRingOps F] [DecidableEq F] (G : List F) :
    ∀ (C : List F),
      (∃ c ∈ C, RoundPoly.evalCoeffs G c ≠ CommRingOps.zero) ∨
      (∀ c ∈ C, RoundPoly.evalCoeffs G c = CommRingOps.zero)
  | [] => .inr (fun _ h => by cases h)
  | c :: cs =>
    if hc : RoundPoly.evalCoeffs G c = CommRingOps.zero then
      match exists_nonroot_or_all_roots G cs with
      | .inl ⟨x, hx, hne⟩ => .inl ⟨x, .tail _ hx, hne⟩
      | .inr hall => .inr (fun y hy => by
          cases hy with
          | head => exact hc
          | tail _ hm => exact hall y hm)
    else
      .inl ⟨c, .head _, hc⟩

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
  have hBadNodup : badPairs.Nodup := zeroLossBadPairs_nodup hSnz hSnzNe hndRest
  refine ⟨hBadLen, hBadNodup, ?_⟩
  intro p hp
  rw [List.mem_flatMap] at hp
  rcases hp with ⟨z₀, hz₀Rest, hpMap⟩
  rw [List.mem_map] at hpMap
  rcases hpMap with ⟨β, hβMem, rfl⟩
  have hβNe := hSnzNe β hβMem
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
    apply filter_eq_self_of_all predP C
    intro z hzC
    dsimp [predP, fg, zeroLossAffineWords]
    simp [C, hzC, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  have hFiltRest : restD.filter predP = [z₀] := by
    apply filter_eq_singleton_of_nodup_iff predP z₀ hndRest hz₀Rest
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
  have hSpEq : D.filter predP = C ++ [z₀] := by
    have hApp : D = C ++ restD := (List.take_append_drop (A - 1) D).symm
    conv => lhs; rw [hApp]
    rw [List.filter_append, hFiltC, hFiltRest]
  have hLenC : C.length = A - 1 := by
    dsimp [C]; exact List.length_take_of_le (by omega)
  refine ⟨?_, ?_, ?_⟩
  · change A ≤ (D.filter predP).length
    rw [hSpEq, List.length_append, hLenC, List.length_singleton]
    omega
  · intro G_poly hGLen
    change ∃ z ∈ D.filter predP, RoundPoly.evalCoeffs G_poly z ≠ fg.2 z
    rcases exists_nonroot_or_all_roots G_poly C with ⟨c, hcMem, hcNe⟩ | hAllRoots
    · have hgc : fg.2 c = CommRingOps.zero := by
        dsimp [fg, zeroLossAffineWords]; simp [C, hcMem]
      refine ⟨c, by rw [hSpEq, List.mem_append]; exact .inl hcMem, ?_⟩
      rwa [hgc]
    · refine ⟨z₀, by rw [hSpEq, List.mem_append]; exact .inr (.head _), ?_⟩
      have hgz₀ : fg.2 z₀ = CommRingOps.one := by
        dsimp [fg, zeroLossAffineWords]; simp [C, hz₀NotC]
      rw [hgz₀]
      if hz0Eq : RoundPoly.evalCoeffs G_poly z₀ = CommRingOps.zero then
        rw [hz0Eq]
        exact LawfulField.zero_ne_one
      else
        have hFiltAll :
            C.filter (fun c => decide (RoundPoly.evalCoeffs G_poly c = CommRingOps.zero)) = C :=
          filter_eq_self_of_all _ C (fun c hc => decide_eq_true (hAllRoots c hc))
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
  · let lossPred := fun z =>
      !(decide (CommRingOps.zero = fg.1 z) && decide (CommRingOps.zero = fg.2 z))
    change ((D.filter predP).filter lossPred).length ≤ 1
    rw [hSpEq, List.filter_append]
    have hCZero : C.filter lossPred = [] := by
      apply filter_eq_nil_of_all_false lossPred C
      intro z hzC
      dsimp [lossPred, fg, zeroLossAffineWords]
      simp [C, hzC]
    rw [hCZero, List.nil_append]
    simp only [List.filter]
    cases lossPred z₀ <;> simp


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
  | _ :: as, _ :: bs, h => congrArg Nat.succ (subVec_length as bs (Nat.succ.inj h))
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  termination_by structural a => a

private theorem insertIdxVal_length {α : Type} :
    ∀ (p : Nat) (val : α) (xs : List α), p ≤ xs.length →
      (insertIdxVal p val xs).length = xs.length + 1
  | 0, _, _, _ => rfl
  | _ + 1, _, [], h => by cases h
  | p + 1, val, _ :: xs, h =>
    congrArg Nat.succ (insertIdxVal_length p val xs (Nat.le_of_succ_le_succ h))

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
      simp only [hx0, ↓reduceIte, Option.map_eq_none_iff] at h
      cases hy with
      | head => exact hx0
      | tail _ hm => exact findNonzeroIdx_none h y hm
    else
      simp [hx0] at h

private theorem findNonzeroIdx_some {F : Type} [CommRingOps F] [DecidableEq F] :
    ∀ {r : List F} {p : Nat}, findNonzeroIdx r = some p →
      p < r.length ∧ r.getD p CommRingOps.zero ≠ CommRingOps.zero
  | [], _, h => by cases h
  | x :: xs, p, h => by
    simp only [findNonzeroIdx] at h
    if hx0 : x = CommRingOps.zero then
      simp only [hx0, ↓reduceIte, Option.map_eq_some_iff] at h
      rcases h with ⟨q, hq, rfl⟩
      rcases findNonzeroIdx_some hq with ⟨hqLt, hqNe⟩
      refine ⟨by simp; omega, ?_⟩
      simpa [List.getD] using hqNe
    else
      simp only [hx0, ↓reduceIte, Option.some.injEq] at h
      subst h
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
    change CommRingOps.add (CommRingOps.mul (CommRingOps.mul c a) b) (dotVec (scaleVec c as) bs) =
      CommRingOps.mul c (CommRingOps.add (CommRingOps.mul a b) (dotVec as bs))
    rw [dotVec_scaleVec c as bs, LawfulCommRing.mul_assoc, ← LawfulCommRing.left_distrib]

private theorem dotVec_subVec {F : Type} [LawfulCommRing F] :
    ∀ (a b v : List F), a.length = b.length →
      dotVec (subVec a b) v = CommRingOps.sub (dotVec a v) (dotVec b v)
  | [], [], _ => fun _ => by simp [subVec, dotVec, LawfulCommRing.sub_self]
  | _ :: _, _ :: _, [] => fun _ => by simp [subVec, dotVec, LawfulCommRing.sub_self]
  | a :: as, b :: bs, x :: xs => fun hlen => by
    simp only [subVec, dotVec, dotVec_subVec as bs xs (Nat.succ.inj hlen), LawfulCommRing.sub_mul]
    apply LawfulCommRing.add_left_cancel
      (a := CommRingOps.add (CommRingOps.mul b x) (dotVec bs xs))
    rw [LawfulCommRing.add_sub_cancel_left,
        ← LawfulCommRing.add_assoc,
        LawfulCommRing.add_assoc (CommRingOps.mul b x) (dotVec bs xs) _,
        LawfulCommRing.add_comm (dotVec bs xs) (CommRingOps.sub _ _),
        ← LawfulCommRing.add_assoc (CommRingOps.mul b x),
        LawfulCommRing.add_sub_cancel_left,
        LawfulCommRing.add_assoc,
        LawfulCommRing.add_sub_cancel_left]
  | [], _ :: _, _ => fun h => by cases h
  | _ :: _, [], _ => fun h => by cases h
  termination_by structural a => a

private theorem dotVec_insertIdxVal {F : Type} [LawfulCommRing F] :
    ∀ (p : Nat) (row v : List F) (vp : F),
      row.length = v.length + 1 →
      p < row.length →
      dotVec row (insertIdxVal p vp v) =
        CommRingOps.add (CommRingOps.mul (row.getD p CommRingOps.zero) vp)
          (dotVec (dropIdx p row) v)
  | 0, [], _, _, _, hp => by cases hp
  | 0, r0 :: rs, v, vp, _, _ => by
    simp [insertIdxVal, dropIdx, dotVec, List.getD]
  | _ + 1, [], _, _, _, hp => by cases hp
  | p + 1, _ :: tl, [], _, hlen, hp => by
    cases tl with
    | nil => exact False.elim (Nat.not_lt_zero p (Nat.lt_of_succ_lt_succ hp))
    | cons _ _ => cases hlen
  | p + 1, r0 :: rs, w0 :: ws, vp, hlen, hp => by
    have ih := dotVec_insertIdxVal p rs ws vp (Nat.succ.inj hlen) (Nat.lt_of_succ_lt_succ hp)
    simp only [insertIdxVal, dropIdx, dotVec, ih]
    have hget : (r0 :: rs).getD (p + 1) CommRingOps.zero = rs.getD p CommRingOps.zero := by
      simp [List.getD]
    rw [hget, ← LawfulCommRing.add_assoc,
        LawfulCommRing.add_comm (CommRingOps.mul r0 w0) _,
        LawfulCommRing.add_assoc]
  termination_by structural p => p

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
  | 0, _, hlt, _ => by cases hlt
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
      have hTailLt : rsTail.length < n := by
        rw [List.length_map]
        exact Nat.lt_of_succ_lt_succ hlt
      have hTailLen : ∀ row' ∈ rsTail, row'.length = n := by
        intro row' hmem
        rw [List.mem_map] at hmem
        rcases hmem with ⟨row, hrow, rfl⟩
        have hl := hrsLen row hrow
        cases row with
        | nil => cases hl
        | cons _ tl => exact Nat.succ.inj hl
      rcases gauss_nullspace_witness n rsTail hTailLt hTailLen with ⟨hvLen, hvAny, hvZero⟩
      dsimp only [rsTail] at hvLen hvAny hvZero
      refine ⟨by simp [hvLen], ?_, ?_⟩
      · simp only [List.any_cons, hvAny, Bool.or_true]
      · intro row hrow
        cases hrow with
        | head =>
          exact dotVec_all_zero r _ (findNonzeroIdx_none hFind)
        | tail _ hm =>
          have hl := hrsLen row hm
          cases row with
          | nil => cases hl
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
        dsimp only [rDrop]
        have h := dropIdx_length p r hpLt
        rw [hrLen] at h
        exact Nat.succ.inj h
      let elimRow := fun (row : List F) =>
        subVec (dropIdx p row) (scaleVec (CommRingOps.mul (row.getD p CommRingOps.zero) invRp) rDrop)
      let rs' := rs.map elimRow
      have hrs'Lt : rs'.length < n := by
        rw [List.length_map]
        exact Nat.lt_of_succ_lt_succ hlt
      have hrs'Len : ∀ row' ∈ rs', row'.length = n := by
        intro row' hmem
        rw [List.mem_map] at hmem
        rcases hmem with ⟨row, hrow, rfl⟩
        have hl := hrsLen row hrow
        have hpRow : p < row.length := by rw [hl, ← hrLen]; exact hpLt
        have hd : (dropIdx p row).length = n := by
          have h := dropIdx_length p row hpRow
          rw [hl] at h
          exact Nat.succ.inj h
        dsimp [elimRow]
        rw [subVec_length]
        · exact hd
        · simp [scaleVec, hd, hrDropLen]
      rcases gauss_nullspace_witness n rs' hrs'Lt hrs'Len with ⟨hvLen, hvAny, hvZero⟩
      let v' := solveHomogeneous n rs'
      have hv'Len : v'.length = n := hvLen
      let vp := CommRingOps.neg (CommRingOps.mul invRp (dotVec rDrop v'))
      have hpLe : p ≤ v'.length := by
        have hpSucc : p < n + 1 := by rw [← hrLen]; exact hpLt
        rw [hv'Len]
        exact Nat.le_of_lt_succ hpSucc
      refine ⟨?_, ?_, ?_⟩
      · rw [insertIdxVal_length p vp v' hpLe, hv'Len]
      · rcases mem_of_any_true hvAny with ⟨z, hzMem, hzPred⟩
        exact any_true_of_mem (mem_insertIdxVal_of_mem p vp hzMem) hzPred
      · intro row hrow
        have hrowLen : row.length = n + 1 := hlen row hrow
        have hpRow : p < row.length := by rw [hrowLen, ← hrLen]; exact hpLt
        rw [dotVec_insertIdxVal p row v' vp (by rw [hrowLen, hv'Len]) hpRow]
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
            have h := dropIdx_length p row hpRow
            rw [hrowLen] at h
            exact Nat.succ.inj h
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
  termination_by structural N => N

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
  | 0, _ :: _, h => by cases h
  | _ + 1, [], h => by cases h
  | k + 1, c :: cs, h => by
    have hcs : cs.length = k := Nat.succ.inj h
    have hscale : dotVec ((geomVec z k).map (CommRingOps.mul z)) cs =
        CommRingOps.mul z (dotVec (geomVec z k) cs) :=
      dotVec_scaleVec z (geomVec z k) cs
    simp only [geomVec, dotVec, LawfulCommRing.one_mul, hscale,
               dotVec_geomVec_eq_evalCoeffs z k cs hcs, RoundPoly.evalCoeffs]
  termination_by structural m => m

theorem dotVec_append_eq {F : Type} [LawfulCommRing F] :
    ∀ (a b x y : List F), a.length = x.length →
      dotVec (a ++ b) (x ++ y) = CommRingOps.add (dotVec a x) (dotVec b y)
  | [], b, [], y, _ => by simp [dotVec, LawfulCommRing.zero_add]
  | a0 :: as, b, x0 :: xs, y, h => by
    simp only [List.cons_append, dotVec, dotVec_append_eq as b xs y (Nat.succ.inj h),
               LawfulCommRing.add_assoc]
  | [], _, _ :: _, _, h => by cases h
  | _ :: _, _, [], _, h => by cases h
  termination_by structural a => a

theorem dotVec_replicate_zero {F : Type} [LawfulCommRing F] :
    ∀ (m : Nat) (v : List F), dotVec (List.replicate m CommRingOps.zero) v = CommRingOps.zero
  | 0, _ => rfl
  | m + 1, [] => rfl
  | m + 1, _ :: vs => by
    simp [List.replicate, dotVec, LawfulCommRing.zero_mul, LawfulCommRing.zero_add,
          dotVec_replicate_zero m vs]


/-! ## §4. Constructive Euclidean Polynomials & Welch–Berlekamp Affine Proximity Gap (`Tier 1B`) -/

/-- Coefficient of `X^k` in `p : List F` (`0` past `p.length`). -/
def coeffAt {F : Type} [CommRingOps F] (p : List F) (k : Nat) : F :=
  p.getD k CommRingOps.zero

/-- Strip trailing zeros so every non-empty canonical polynomial has a non-zero leading coefficient. -/
def trimPoly {F : Type} [CommRingOps F] [DecidableEq F] : List F → List F
  | [] => []
  | c :: cs =>
    let cs' := trimPoly cs
    if cs' = [] ∧ c = CommRingOps.zero then [] else c :: cs'

/-- Canonical trimmedness predicate. -/
def IsTrimmed {F : Type} [CommRingOps F] [DecidableEq F] (p : List F) : Prop :=
  trimPoly p = p

theorem coeffAt_nil {F : Type} [CommRingOps F] (k : Nat) :
    coeffAt ([] : List F) k = CommRingOps.zero := by
  simp [coeffAt]

theorem coeffAt_cons_zero {F : Type} [CommRingOps F] (c : F) (cs : List F) :
    coeffAt (c :: cs) 0 = c := by
  simp [coeffAt]

theorem coeffAt_cons_succ {F : Type} [CommRingOps F] (c : F) (cs : List F) (k : Nat) :
    coeffAt (c :: cs) (k + 1) = coeffAt cs k := by
  simp [coeffAt]

theorem coeffAt_eq_zero_of_ge {F : Type} [CommRingOps F] :
    ∀ (p : List F) (k : Nat), p.length ≤ k → coeffAt p k = CommRingOps.zero
  | [], _, _ => rfl
  | _ :: _, 0, h => by simp at h
  | _ :: cs, k + 1, h => by
    simp only [List.length_cons] at h
    rw [coeffAt_cons_succ]
    exact coeffAt_eq_zero_of_ge cs k (by omega)

theorem trimPoly_length_le {F : Type} [CommRingOps F] [DecidableEq F] :
    ∀ (p : List F), (trimPoly p).length ≤ p.length
  | [] => Nat.le_refl 0
  | c :: cs => by
    simp only [trimPoly]
    split
    · simp
    · simp only [List.length_cons]
      exact Nat.succ_le_succ (trimPoly_length_le cs)

theorem evalCoeffs_trimPoly {F : Type} [LawfulCommRing F] [DecidableEq F] (x : F) :
    ∀ (p : List F), RoundPoly.evalCoeffs (trimPoly p) x = RoundPoly.evalCoeffs p x
  | [] => rfl
  | c :: cs => by
    simp only [trimPoly]
    split
    · next h =>
      rcases h with ⟨hcs, hc⟩
      have ih := evalCoeffs_trimPoly x cs
      rw [hcs, RoundPoly.evalCoeffs_nil] at ih
      simp [RoundPoly.evalCoeffs, hc, ← ih, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    · simp [RoundPoly.evalCoeffs, evalCoeffs_trimPoly x cs]

theorem coeffAt_trimPoly {F : Type} [CommRingOps F] [DecidableEq F] :
    ∀ (p : List F) (k : Nat), coeffAt (trimPoly p) k = coeffAt p k
  | [], _ => rfl
  | c :: cs, k => by
    simp only [trimPoly]
    split
    · next h =>
      rcases h with ⟨hcs, hc⟩
      cases k with
      | zero => simp [coeffAt, hc]
      | succ k' =>
        have ih := coeffAt_trimPoly cs k'
        rw [hcs, coeffAt_nil] at ih
        rw [coeffAt_nil, coeffAt_cons_succ, ← ih]
    · cases k with
      | zero => rfl
      | succ k' => exact coeffAt_trimPoly cs k'

theorem trimPoly_idem {F : Type} [CommRingOps F] [DecidableEq F] :
    ∀ (p : List F), trimPoly (trimPoly p) = trimPoly p
  | [] => rfl
  | c :: cs => by
    simp only [trimPoly]
    split
    · rfl
    · next h =>
      simp only [trimPoly, trimPoly_idem cs, h, ↓reduceIte]

theorem leadCoeff_ne_zero_of_trimPoly_ne_nil {F : Type} [CommRingOps F] [DecidableEq F] :
    ∀ (p : List F), trimPoly p ≠ [] →
      coeffAt (trimPoly p) ((trimPoly p).length - 1) ≠ CommRingOps.zero
  | [], h => False.elim (h rfl)
  | c :: cs, h => by
    simp only [trimPoly] at h ⊢
    if hcond : trimPoly cs = [] ∧ c = CommRingOps.zero then
      simp [hcond] at h
    else
      simp only [hcond, ↓reduceIte]
      if hcs : trimPoly cs = [] then
        have hc : c ≠ CommRingOps.zero := fun hc0 => hcond ⟨hcs, hc0⟩
        simpa [hcs, coeffAt] using hc
      else
        have ih := leadCoeff_ne_zero_of_trimPoly_ne_nil cs hcs
        cases hq : trimPoly cs with
        | nil => exact False.elim (hcs hq)
        | cons d ds =>
          rw [hq] at ih
          simpa [coeffAt] using ih

private theorem eq_of_isTrimmed_coeffAt {F : Type} [CommRingOps F] [DecidableEq F] :
    ∀ (a b : List F), IsTrimmed a → IsTrimmed b →
      (∀ k : Nat, coeffAt a k = coeffAt b k) → a = b
  | [], [], _, _, _ => rfl
  | [], y :: ys, _, hb, hcoeff => by
    have hne : trimPoly (y :: ys) ≠ [] := by rw [hb]; simp
    have hlead := leadCoeff_ne_zero_of_trimPoly_ne_nil (y :: ys) hne
    rw [hb, ← hcoeff ((y :: ys).length - 1), coeffAt_nil] at hlead
    exact False.elim (hlead rfl)
  | x :: xs, [], ha, _, hcoeff => by
    have hne : trimPoly (x :: xs) ≠ [] := by rw [ha]; simp
    have hlead := leadCoeff_ne_zero_of_trimPoly_ne_nil (x :: xs) hne
    rw [ha, hcoeff ((x :: xs).length - 1), coeffAt_nil] at hlead
    exact False.elim (hlead rfl)
  | x :: xs, y :: ys, ha, hb, hcoeff => by
    have hxy : x = y := by simpa [coeffAt] using hcoeff 0
    subst hxy
    have hxs : IsTrimmed xs := by
      unfold IsTrimmed at ha ⊢
      simp only [trimPoly] at ha
      split at ha
      · cases ha
      · injection ha with _ htl
    have hys : IsTrimmed ys := by
      unfold IsTrimmed at hb ⊢
      simp only [trimPoly] at hb
      split at hb
      · cases hb
      · injection hb with _ htl
    have htl := eq_of_isTrimmed_coeffAt xs ys hxs hys (fun k => by
      simpa [coeffAt_cons_succ] using hcoeff (k + 1))
    rw [htl]

/-- Canonical polynomial equality criterion: `trimPoly p = trimPoly q` iff all coefficients match. -/
theorem trimPoly_eq_iff_coeffAt {F : Type} [CommRingOps F] [DecidableEq F] (p q : List F) :
    trimPoly p = trimPoly q ↔ ∀ k : Nat, coeffAt p k = coeffAt q k := by
  constructor
  · intro heq k
    rw [← coeffAt_trimPoly p k, ← coeffAt_trimPoly q k, heq]
  · intro h
    apply eq_of_isTrimmed_coeffAt (trimPoly p) (trimPoly q) (trimPoly_idem p) (trimPoly_idem q)
    intro k
    rw [coeffAt_trimPoly, coeffAt_trimPoly, h k]

theorem trimPoly_eq_nil_iff {F : Type} [CommRingOps F] [DecidableEq F] (p : List F) :
    trimPoly p = [] ↔ ∀ k : Nat, coeffAt p k = CommRingOps.zero := by
  simpa [trimPoly, coeffAt_nil] using trimPoly_eq_iff_coeffAt p []

theorem length_trimPoly_le_of_coeffAt_zero {F : Type} [CommRingOps F] [DecidableEq F]
    (p : List F) (B : Nat) (h : ∀ k : Nat, B ≤ k → coeffAt p k = CommRingOps.zero) :
    (trimPoly p).length ≤ B := by
  if hnil : trimPoly p = [] then
    rw [hnil]; exact Nat.zero_le B
  else
    have hlead := leadCoeff_ne_zero_of_trimPoly_ne_nil p hnil
    rw [coeffAt_trimPoly] at hlead
    if hle : (trimPoly p).length ≤ B then
      exact hle
    else
      exact False.elim (hlead (h ((trimPoly p).length - 1) (by omega)))

/-- Constructive non-root existence for ANY non-empty trimmed polynomial on a `Nodup` domain `U`
    with `p.length ≤ U.length` (`0` classical axioms). -/
theorem exists_nonroot_of_trim_ne_nil
    {F : Type} [LawfulField F] [DecidableEq F]
    {p U : List F}
    (hpTrim : IsTrimmed p)
    (hpNe : p ≠ [])
    (hU : U.Nodup)
    (hLen : p.length ≤ U.length) :
    ∃ x₀ ∈ U, RoundPoly.evalCoeffs p x₀ ≠ CommRingOps.zero := by
  let k := p.length - 1
  have hk : p.length = k + 1 := by
    cases p with
    | nil => exact False.elim (hpNe rfl)
    | cons _ _ => simp [k]
  have hlcNe : coeffAt p k ≠ CommRingOps.zero := by
    have h := leadCoeff_ne_zero_of_trimPoly_ne_nil p (by rwa [hpTrim])
    rw [hpTrim] at h
    exact h
  let pMonic := p.map (CommRingOps.mul (LawfulField.inv (coeffAt p k)))
  have hMonicLen : pMonic.length = k + 1 := by simp [pMonic, hk]
  have hMonicLast : pMonic.getD k CommRingOps.zero = CommRingOps.one := by
    have hkLt : k < p.length := by omega
    have hget : pMonic.getD k CommRingOps.zero =
        CommRingOps.mul (LawfulField.inv (coeffAt p k)) (coeffAt p k) := by
      simp [pMonic, coeffAt, List.getD, hkLt]
    rw [hget, LawfulField.inv_mul_cancel hlcNe]
  rcases exists_nonroot_of_monic_len k pMonic U hMonicLen hMonicLast hU (by omega) with
    ⟨x₀, hx₀Mem, hx₀Ne⟩
  refine ⟨x₀, hx₀Mem, ?_⟩
  intro hev0
  apply hx₀Ne
  rw [evalCoeffs_map_mul, hev0, LawfulCommRing.mul_zero]

/-- Componentwise polynomial addition & negation on raw `List F` coefficient vectors. -/
def rawAddCoeffs {F : Type} [CommRingOps F] : List F → List F → List F
  | [], b => b
  | a, [] => a
  | c :: cs, d :: ds => CommRingOps.add c d :: rawAddCoeffs cs ds

def rawNegCoeffs {F : Type} [CommRingOps F] (a : List F) : List F :=
  a.map CommRingOps.neg

theorem evalCoeffs_rawAdd {F : Type} [LawfulCommRing F] :
    ∀ (a b : List F) (x : F),
      RoundPoly.evalCoeffs (rawAddCoeffs a b) x =
        CommRingOps.add (RoundPoly.evalCoeffs a x) (RoundPoly.evalCoeffs b x)
  | [], b, x => by simp [rawAddCoeffs, RoundPoly.evalCoeffs, LawfulCommRing.zero_add]
  | a, [], x => by cases a <;> simp [rawAddCoeffs, RoundPoly.evalCoeffs, LawfulCommRing.add_zero]
  | c :: cs, d :: ds, x => by
    simp only [rawAddCoeffs, RoundPoly.evalCoeffs, evalCoeffs_rawAdd cs ds x]
    rw [LawfulCommRing.left_distrib, LawfulCommRing.add_add_add_comm]

/-- Canonical trimmed univariate polynomial operations. -/
def pAdd {F : Type} [CommRingOps F] [DecidableEq F] (a b : List F) : List F :=
  trimPoly (rawAddCoeffs a b)

def pSub {F : Type} [CommRingOps F] [DecidableEq F] (a b : List F) : List F :=
  trimPoly (RoundPoly.subCoeffs a b)

def pNeg {F : Type} [CommRingOps F] [DecidableEq F] (a : List F) : List F :=
  trimPoly (rawNegCoeffs a)

def pScale {F : Type} [CommRingOps F] [DecidableEq F] (c : F) (a : List F) : List F :=
  trimPoly (a.map (CommRingOps.mul c))

def rawMul {F : Type} [CommRingOps F] : List F → List F → List F
  | [], _ => []
  | c :: cs, b => rawAddCoeffs (b.map (CommRingOps.mul c)) (CommRingOps.zero :: rawMul cs b)

def pMul {F : Type} [CommRingOps F] [DecidableEq F] (a b : List F) : List F :=
  trimPoly (rawMul a b)

def monomial {F : Type} [CommRingOps F] (deg : Nat) (c : F) : List F :=
  List.replicate deg CommRingOps.zero ++ [c]

private theorem coeffAt_addCoeffs {F : Type} [LawfulCommRing F] :
    ∀ (a b : List F) (k : Nat),
      coeffAt (rawAddCoeffs a b) k = CommRingOps.add (coeffAt a k) (coeffAt b k)
  | [], b, k => by simp [rawAddCoeffs, coeffAt_nil, LawfulCommRing.zero_add]
  | a, [], k => by
    cases a <;> simp [rawAddCoeffs, coeffAt_nil, LawfulCommRing.add_zero]
  | _ :: _, _ :: _, 0 => by simp [rawAddCoeffs, coeffAt]
  | _ :: as, _ :: bs, k + 1 => by
    simp only [rawAddCoeffs, coeffAt_cons_succ, coeffAt_addCoeffs as bs k]

private theorem coeffAt_negCoeffs {F : Type} [LawfulCommRing F] :
    ∀ (a : List F) (k : Nat),
      coeffAt (rawNegCoeffs a) k = CommRingOps.neg (coeffAt a k)
  | [], _ => by simp [rawNegCoeffs, coeffAt_nil, LawfulCommRing.neg_zero]
  | _ :: _, 0 => by simp [rawNegCoeffs, coeffAt]
  | c :: as, k + 1 => by
    change coeffAt (CommRingOps.neg c :: rawNegCoeffs as) (k + 1) =
      CommRingOps.neg (coeffAt (c :: as) (k + 1))
    rw [coeffAt_cons_succ, coeffAt_cons_succ, coeffAt_negCoeffs as k]

private theorem coeffAt_subCoeffs {F : Type} [LawfulCommRing F] :
    ∀ (a b : List F) (k : Nat),
      coeffAt (RoundPoly.subCoeffs a b) k = CommRingOps.sub (coeffAt a k) (coeffAt b k)
  | [], [], k => by simp [RoundPoly.subCoeffs, coeffAt_nil, LawfulCommRing.sub_self]
  | c :: cs, [], 0 => by simp [RoundPoly.subCoeffs, coeffAt, LawfulCommRing.sub_zero]
  | c :: cs, [], k + 1 => by
    simp only [RoundPoly.subCoeffs, coeffAt_cons_succ, coeffAt_subCoeffs cs [] k, coeffAt_nil]
  | [], d :: ds, 0 => by
    simp [RoundPoly.subCoeffs, coeffAt, LawfulCommRing.sub_eq_add_neg, LawfulCommRing.zero_add]
  | [], d :: ds, k + 1 => by
    simp only [RoundPoly.subCoeffs, coeffAt_cons_succ, coeffAt_subCoeffs [] ds k, coeffAt_nil]
  | _ :: _, _ :: _, 0 => by simp [RoundPoly.subCoeffs, coeffAt]
  | _ :: as, _ :: bs, k + 1 => by
    simp only [RoundPoly.subCoeffs, coeffAt_cons_succ, coeffAt_subCoeffs as bs k]

private theorem coeffAt_map_mul {F : Type} [LawfulCommRing F] (c : F) :
    ∀ (a : List F) (k : Nat),
      coeffAt (a.map (CommRingOps.mul c)) k = CommRingOps.mul c (coeffAt a k)
  | [], _ => by simp [coeffAt_nil, LawfulCommRing.mul_zero]
  | _ :: _, 0 => by simp [coeffAt]
  | _ :: as, k + 1 => by simp [coeffAt_cons_succ, coeffAt_map_mul c as k]

theorem coeffAt_pAdd {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) (k : Nat) :
    coeffAt (pAdd a b) k = CommRingOps.add (coeffAt a k) (coeffAt b k) := by
  rw [pAdd, coeffAt_trimPoly, coeffAt_addCoeffs]

theorem coeffAt_pSub {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) (k : Nat) :
    coeffAt (pSub a b) k = CommRingOps.sub (coeffAt a k) (coeffAt b k) := by
  rw [pSub, coeffAt_trimPoly, coeffAt_subCoeffs]

theorem coeffAt_pNeg {F : Type} [LawfulCommRing F] [DecidableEq F] (a : List F) (k : Nat) :
    coeffAt (pNeg a) k = CommRingOps.neg (coeffAt a k) := by
  rw [pNeg, coeffAt_trimPoly, coeffAt_negCoeffs]

theorem coeffAt_pScale {F : Type} [LawfulCommRing F] [DecidableEq F] (c : F) (a : List F) (k : Nat) :
    coeffAt (pScale c a) k = CommRingOps.mul c (coeffAt a k) := by
  rw [pScale, coeffAt_trimPoly, coeffAt_map_mul]

theorem evalCoeffs_rawMul {F : Type} [LawfulCommRing F] (x : F) :
    ∀ (a b : List F), RoundPoly.evalCoeffs (rawMul a b) x =
      CommRingOps.mul (RoundPoly.evalCoeffs a x) (RoundPoly.evalCoeffs b x)
  | [], _ => by simp [rawMul, RoundPoly.evalCoeffs, LawfulCommRing.zero_mul]
  | c :: cs, b => by
    simp only [rawMul, evalCoeffs_rawAdd, evalCoeffs_map_mul, RoundPoly.evalCoeffs_cons,
               LawfulCommRing.zero_add, evalCoeffs_rawMul x cs b]
    rw [LawfulCommRing.right_distrib, LawfulCommRing.mul_assoc]

theorem evalCoeffs_pAdd {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) (x : F) :
    RoundPoly.evalCoeffs (pAdd a b) x =
      CommRingOps.add (RoundPoly.evalCoeffs a x) (RoundPoly.evalCoeffs b x) := by
  rw [pAdd, evalCoeffs_trimPoly, evalCoeffs_rawAdd]

theorem evalCoeffs_pSub {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) (x : F) :
    RoundPoly.evalCoeffs (pSub a b) x =
      CommRingOps.sub (RoundPoly.evalCoeffs a x) (RoundPoly.evalCoeffs b x) := by
  rw [pSub, evalCoeffs_trimPoly, RoundPoly.evalCoeffs_sub]

theorem evalCoeffs_pScale {F : Type} [LawfulCommRing F] [DecidableEq F] (c : F) (a : List F) (x : F) :
    RoundPoly.evalCoeffs (pScale c a) x = CommRingOps.mul c (RoundPoly.evalCoeffs a x) := by
  rw [pScale, evalCoeffs_trimPoly, evalCoeffs_map_mul]

theorem evalCoeffs_pMul {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) (x : F) :
    RoundPoly.evalCoeffs (pMul a b) x =
      CommRingOps.mul (RoundPoly.evalCoeffs a x) (RoundPoly.evalCoeffs b x) := by
  rw [pMul, evalCoeffs_trimPoly, evalCoeffs_rawMul]

private theorem coeffAt_rawMul_zero_left {F : Type} [LawfulCommRing F] (b : List F) :
    ∀ (a : List F), (∀ i, coeffAt a i = CommRingOps.zero) →
      ∀ k, coeffAt (rawMul a b) k = CommRingOps.zero
  | [], _, k => by simp [rawMul, coeffAt_nil]
  | c :: cs, ha, k => by
    have hc : c = CommRingOps.zero := ha 0
    have hcs : ∀ i, coeffAt cs i = CommRingOps.zero := fun i => ha (i + 1)
    simp only [rawMul, coeffAt_addCoeffs, coeffAt_map_mul, hc, LawfulCommRing.zero_mul,
               LawfulCommRing.zero_add]
    cases k with
    | zero => rfl
    | succ k' => exact coeffAt_rawMul_zero_left b cs hcs k'

private theorem coeffAt_rawMul_zero_right {F : Type} [LawfulCommRing F] :
    ∀ (a b : List F), (∀ j, coeffAt b j = CommRingOps.zero) →
      ∀ k, coeffAt (rawMul a b) k = CommRingOps.zero
  | [], _, _, k => by simp [rawMul, coeffAt_nil]
  | c :: cs, b, hb, k => by
    simp only [rawMul, coeffAt_addCoeffs, coeffAt_map_mul, hb k, LawfulCommRing.mul_zero,
               LawfulCommRing.zero_add]
    cases k with
    | zero => rfl
    | succ k' => exact coeffAt_rawMul_zero_right cs b hb k'

private theorem coeffAt_rawMul_high {F : Type} [LawfulCommRing F] (b : List F) (db : Nat)
    (hb : ∀ j, db < j → coeffAt b j = CommRingOps.zero) :
    ∀ (da : Nat) (a : List F),
      (∀ i, da < i → coeffAt a i = CommRingOps.zero) →
      (∀ k, da + db < k → coeffAt (rawMul a b) k = CommRingOps.zero) ∧
      coeffAt (rawMul a b) (da + db) = CommRingOps.mul (coeffAt a da) (coeffAt b db)
  | 0, [], _ => by
    refine ⟨fun k _ => by simp [rawMul, coeffAt_nil], ?_⟩
    simp [rawMul, coeffAt_nil, LawfulCommRing.zero_mul]
  | 0, a0 :: as, ha => by
    have has0 : ∀ i, coeffAt as i = CommRingOps.zero := fun i => by
      simpa [coeffAt_cons_succ] using ha (i + 1) (Nat.zero_lt_succ i)
    have htail : ∀ k, coeffAt (CommRingOps.zero :: rawMul as b) k = CommRingOps.zero := by
      intro k
      cases k with
      | zero => rfl
      | succ k' => exact coeffAt_rawMul_zero_left b as has0 k'
    refine ⟨fun k hk => ?_, ?_⟩
    · simp only [rawMul, coeffAt_addCoeffs, coeffAt_map_mul, htail k, LawfulCommRing.add_zero]
      rw [hb k (by simpa [Nat.zero_add] using hk), LawfulCommRing.mul_zero]
    · simp only [Nat.zero_add, rawMul, coeffAt_addCoeffs, coeffAt_map_mul, htail db,
                 LawfulCommRing.add_zero, coeffAt_cons_zero]
  | da + 1, [], _ => by
    refine ⟨fun k _ => by simp [rawMul, coeffAt_nil], ?_⟩
    simp [rawMul, coeffAt_nil, LawfulCommRing.zero_mul]
  | da + 1, a0 :: as, ha => by
    have has : ∀ i, da < i → coeffAt as i = CommRingOps.zero := fun i hi => by
      simpa [coeffAt_cons_succ] using ha (i + 1) (Nat.succ_lt_succ hi)
    rcases coeffAt_rawMul_high b db hb da as has with ⟨ihHigh, ihTop⟩
    refine ⟨fun k hk => ?_, ?_⟩
    · cases k with
      | zero => cases hk
      | succ k' =>
        simp only [rawMul, coeffAt_addCoeffs, coeffAt_map_mul, coeffAt_cons_succ]
        have hk1 : db < k' + 1 := Nat.lt_of_le_of_lt (Nat.le_add_left db (da + 1)) hk
        have hk2 : da + db < k' := Nat.lt_of_succ_lt_succ (by rwa [Nat.succ_add] at hk)
        rw [hb (k' + 1) hk1, ihHigh k' hk2,
            LawfulCommRing.mul_zero, LawfulCommRing.zero_add]
    · have hidx : da + 1 + db = (da + db) + 1 := Nat.succ_add da db
      rw [hidx]
      simp only [rawMul, coeffAt_addCoeffs, coeffAt_map_mul, coeffAt_cons_succ]
      have htopLt : db < (da + db) + 1 := Nat.lt_succ_of_le (Nat.le_add_left db da)
      rw [hb ((da + db) + 1) htopLt, LawfulCommRing.mul_zero, LawfulCommRing.zero_add, ihTop]
  termination_by structural da => da

private theorem coeffAt_rawMul_add_left {F : Type} [LawfulCommRing F] (b : List F) :
    ∀ (a1 a2 : List F) (k : Nat),
      coeffAt (rawMul (rawAddCoeffs a1 a2) b) k =
        CommRingOps.add (coeffAt (rawMul a1 b) k) (coeffAt (rawMul a2 b) k)
  | [], a2, k => by simp [rawAddCoeffs, rawMul, coeffAt_nil, LawfulCommRing.zero_add]
  | a1, [], k => by
    cases a1 <;> simp [rawAddCoeffs, rawMul, coeffAt_nil, LawfulCommRing.add_zero]
  | x :: xs, y :: ys, k => by
    simp only [rawAddCoeffs, rawMul, coeffAt_addCoeffs, coeffAt_map_mul,
               LawfulCommRing.right_distrib]
    cases k with
    | zero =>
      simp [coeffAt, LawfulCommRing.add_zero]
    | succ k' =>
      simp only [coeffAt_cons_succ, coeffAt_rawMul_add_left b xs ys k']
      rw [← LawfulCommRing.add_assoc,
          LawfulCommRing.add_assoc (CommRingOps.mul x _) (CommRingOps.mul y _) _,
          LawfulCommRing.add_comm (CommRingOps.mul y _) (coeffAt (rawMul xs b) k'),
          ← LawfulCommRing.add_assoc,
          LawfulCommRing.add_assoc]

private theorem coeffAt_rawMul_add_right {F : Type} [LawfulCommRing F] :
    ∀ (a b1 b2 : List F) (k : Nat),
      coeffAt (rawMul a (rawAddCoeffs b1 b2)) k =
        CommRingOps.add (coeffAt (rawMul a b1) k) (coeffAt (rawMul a b2) k)
  | [], _, _, _ => by simp [rawMul, coeffAt_nil, LawfulCommRing.zero_add]
  | c :: cs, b1, b2, k => by
    simp only [rawMul, coeffAt_addCoeffs, coeffAt_map_mul, LawfulCommRing.left_distrib]
    cases k with
    | zero => simp [coeffAt, LawfulCommRing.add_zero]
    | succ k' =>
      simp only [coeffAt_cons_succ, coeffAt_rawMul_add_right cs b1 b2 k']
      rw [← LawfulCommRing.add_assoc,
          LawfulCommRing.add_assoc (CommRingOps.mul c _) (CommRingOps.mul c _) _,
          LawfulCommRing.add_comm (CommRingOps.mul c (coeffAt b2 (k' + 1))) _,
          ← LawfulCommRing.add_assoc,
          LawfulCommRing.add_assoc]

private theorem coeffAt_rawMul_shift_right {F : Type} [LawfulCommRing F] :
    ∀ (a b : List F) (k : Nat),
      coeffAt (rawMul a (CommRingOps.zero :: b)) k =
        coeffAt (CommRingOps.zero :: rawMul a b) k
  | [], _, k => by cases k <;> simp [rawMul, coeffAt]
  | c :: cs, b, 0 => by
    simp only [rawMul, coeffAt_addCoeffs, coeffAt_map_mul, coeffAt_cons_zero,
               LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | c :: cs, b, k + 1 => by
    simp [rawMul, coeffAt_addCoeffs, coeffAt_map_mul, coeffAt_cons_succ,
          coeffAt_rawMul_shift_right cs b k]

private theorem coeffAt_rawMul_scale_left {F : Type} [LawfulCommRing F] (s : F) (b : List F) :
    ∀ (a : List F) (k : Nat),
      coeffAt (rawMul (a.map (CommRingOps.mul s)) b) k =
        CommRingOps.mul s (coeffAt (rawMul a b) k)
  | [], _ => by simp [rawMul, coeffAt_nil, LawfulCommRing.mul_zero]
  | c :: cs, 0 => by
    simp only [List.map, rawMul, coeffAt_addCoeffs, coeffAt_map_mul, coeffAt_cons_zero,
               LawfulCommRing.add_zero, LawfulCommRing.mul_assoc]
  | c :: cs, k + 1 => by
    simp [rawMul, coeffAt_addCoeffs, coeffAt_map_mul, coeffAt_cons_succ,
          coeffAt_rawMul_scale_left s b cs k,
          LawfulCommRing.left_distrib, LawfulCommRing.mul_assoc]

private theorem coeffAt_rawMul_scale_right {F : Type} [LawfulCommRing F] (s : F) :
    ∀ (a b : List F) (k : Nat),
      coeffAt (rawMul a (b.map (CommRingOps.mul s))) k =
        CommRingOps.mul s (coeffAt (rawMul a b) k)
  | [], _, _ => by simp [rawMul, coeffAt_nil, LawfulCommRing.mul_zero]
  | c :: cs, b, k => by
    simp only [rawMul, coeffAt_addCoeffs, coeffAt_map_mul]
    have hcomm : CommRingOps.mul c (CommRingOps.mul s (coeffAt b k)) =
        CommRingOps.mul s (CommRingOps.mul c (coeffAt b k)) := by
      rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm c s, LawfulCommRing.mul_assoc]
    rw [hcomm]
    cases k with
    | zero => simp only [coeffAt_cons_zero, LawfulCommRing.add_zero]
    | succ k' =>
      simp [coeffAt_cons_succ, coeffAt_rawMul_scale_right s cs b k', LawfulCommRing.left_distrib]

private theorem coeffAt_rawMul_congr {F : Type} [LawfulCommRing F] :
    ∀ (a1 a2 b1 b2 : List F),
      (∀ i, coeffAt a1 i = coeffAt a2 i) →
      (∀ j, coeffAt b1 j = coeffAt b2 j) →
      ∀ k, coeffAt (rawMul a1 b1) k = coeffAt (rawMul a2 b2) k
  | [], [], _, _, _, _, _ => rfl
  | [], c :: cs, b1, b2, ha, _, k => by
    have h0 : ∀ i, coeffAt (c :: cs) i = CommRingOps.zero := fun i => by
      simpa [coeffAt_nil] using (ha i).symm
    rw [show rawMul ([] : List F) b1 = [] from rfl, coeffAt_nil,
        coeffAt_rawMul_zero_left b2 (c :: cs) h0 k]
  | c :: cs, [], b1, b2, ha, _, k => by
    have h0 : ∀ i, coeffAt (c :: cs) i = CommRingOps.zero := fun i => by
      simpa [coeffAt_nil] using ha i
    rw [show rawMul ([] : List F) b2 = [] from rfl, coeffAt_nil,
        coeffAt_rawMul_zero_left b1 (c :: cs) h0 k]
  | x :: xs, y :: ys, b1, b2, ha, hb, k => by
    have hxy : x = y := by simpa [coeffAt] using ha 0
    subst hxy
    simp only [rawMul, coeffAt_addCoeffs, coeffAt_map_mul, hb k]
    cases k with
    | zero => rfl
    | succ k' =>
      simp only [coeffAt_cons_succ]
      rw [coeffAt_rawMul_congr xs ys b1 b2
        (fun i => by simpa [coeffAt_cons_succ] using ha (i + 1)) hb k']

theorem pMul_trimPoly_left {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) :
    pMul (trimPoly a) b = pMul a b := by
  unfold pMul
  rw [trimPoly_eq_iff_coeffAt]
  exact coeffAt_rawMul_congr (trimPoly a) a b b (coeffAt_trimPoly a) (fun _ => rfl)

theorem pMul_trimPoly_right {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) :
    pMul a (trimPoly b) = pMul a b := by
  unfold pMul
  rw [trimPoly_eq_iff_coeffAt]
  exact coeffAt_rawMul_congr a a (trimPoly b) b (fun _ => rfl) (coeffAt_trimPoly b)

theorem pAdd_comm {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) :
    pAdd a b = pAdd b a := by
  unfold pAdd; rw [trimPoly_eq_iff_coeffAt]; intro k
  simp [coeffAt_addCoeffs, LawfulCommRing.add_comm]

theorem pAdd_assoc {F : Type} [LawfulCommRing F] [DecidableEq F] (a b c : List F) :
    pAdd (pAdd a b) c = pAdd a (pAdd b c) := by
  unfold pAdd; rw [trimPoly_eq_iff_coeffAt]; intro k
  simp [coeffAt_addCoeffs, coeffAt_trimPoly, LawfulCommRing.add_assoc]

theorem pAdd_nil_right {F : Type} [LawfulCommRing F] [DecidableEq F] (a : List F) :
    pAdd a [] = trimPoly a := by
  unfold pAdd; rw [trimPoly_eq_iff_coeffAt]; intro k
  simp [coeffAt_addCoeffs, coeffAt_nil, LawfulCommRing.add_zero]

theorem pAdd_nil_left {F : Type} [LawfulCommRing F] [DecidableEq F] (a : List F) :
    pAdd [] a = trimPoly a := by
  rw [pAdd_comm, pAdd_nil_right]

theorem pAdd_trimPoly_left {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) :
    pAdd (trimPoly a) b = pAdd a b := by
  unfold pAdd; rw [trimPoly_eq_iff_coeffAt]; intro k
  simp [coeffAt_addCoeffs, coeffAt_trimPoly]

theorem pAdd_trimPoly_right {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) :
    pAdd a (trimPoly b) = pAdd a b := by
  unfold pAdd; rw [trimPoly_eq_iff_coeffAt]; intro k
  simp [coeffAt_addCoeffs, coeffAt_trimPoly]

theorem pSub_eq_pAdd_pNeg {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) :
    pSub a b = pAdd a (pNeg b) := by
  unfold pSub pAdd pNeg; rw [trimPoly_eq_iff_coeffAt]; intro k
  simp [coeffAt_subCoeffs, coeffAt_addCoeffs, coeffAt_trimPoly, coeffAt_negCoeffs,
        LawfulCommRing.sub_eq_add_neg]

theorem pAdd_pSub_cancel {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) :
    pAdd b (pSub a b) = trimPoly a := by
  unfold pAdd pSub; rw [trimPoly_eq_iff_coeffAt]; intro k
  simp [coeffAt_addCoeffs, coeffAt_trimPoly, coeffAt_subCoeffs, LawfulCommRing.add_sub_cancel_left]

theorem pSub_pAdd_cancel_left {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) :
    pSub (pAdd a b) a = trimPoly b := by
  unfold pSub pAdd; rw [trimPoly_eq_iff_coeffAt]; intro k
  rw [coeffAt_subCoeffs, coeffAt_trimPoly, coeffAt_addCoeffs,
      LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_comm (coeffAt a k),
      LawfulCommRing.add_assoc, LawfulCommRing.add_right_neg, LawfulCommRing.add_zero]

theorem pMul_comm {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) :
    pMul a b = pMul b a := by
  unfold pMul
  rw [trimPoly_eq_iff_coeffAt]
  induction a with
  | nil =>
    intro k
    have h0 : ∀ j, coeffAt ([] : List F) j = CommRingOps.zero := coeffAt_nil
    simp [rawMul, coeffAt_nil, coeffAt_rawMul_zero_right b [] h0 k]
  | cons c cs ih =>
    intro k
    have h1 : ∀ j, coeffAt (rawMul b [c]) j = CommRingOps.mul c (coeffAt b j) := by
      clear ih k cs
      induction b with
      | nil => intro j; simp [rawMul, coeffAt_nil, LawfulCommRing.mul_zero]
      | cons d ds ihb =>
        intro j
        cases j with
        | zero =>
          simp only [rawMul, coeffAt_addCoeffs, coeffAt_map_mul, coeffAt_cons_zero,
                     LawfulCommRing.add_zero, LawfulCommRing.mul_comm]
        | succ j' =>
          simp only [rawMul, coeffAt_addCoeffs, List.map, coeffAt_cons_succ, coeffAt_nil,
                     LawfulCommRing.zero_add, ihb j']
    have hsplit : ∀ i, coeffAt (c :: cs) i =
        coeffAt (rawAddCoeffs [c] (CommRingOps.zero :: cs)) i := by
      intro i
      cases i with
      | zero => simp [rawAddCoeffs, coeffAt, LawfulCommRing.add_zero]
      | succ _ => simp [rawAddCoeffs, coeffAt]
    rw [coeffAt_rawMul_congr b b (c :: cs) (rawAddCoeffs [c] (CommRingOps.zero :: cs))
          (fun _ => rfl) hsplit k,
        coeffAt_rawMul_add_right, h1 k, coeffAt_rawMul_shift_right]
    simp only [rawMul, coeffAt_addCoeffs, coeffAt_map_mul]
    cases k with
    | zero => rfl
    | succ k' => simp [coeffAt_cons_succ, ih k']

theorem pMul_assoc {F : Type} [LawfulCommRing F] [DecidableEq F] (a b c : List F) :
    pMul (pMul a b) c = pMul a (pMul b c) := by
  have h1 : pMul (pMul a b) c = pMul (rawMul a b) c := pMul_trimPoly_left (rawMul a b) c
  have h2 : pMul a (pMul b c) = pMul a (rawMul b c) := pMul_trimPoly_right a (rawMul b c)
  rw [h1, h2]
  clear h1 h2
  unfold pMul
  rw [trimPoly_eq_iff_coeffAt]
  have hshiftLeft : ∀ (u v : List F) (k : Nat),
      coeffAt (rawMul (CommRingOps.zero :: u) v) k =
        coeffAt (CommRingOps.zero :: rawMul u v) k := by
    intro u v k
    simp [rawMul, coeffAt_addCoeffs, coeffAt_map_mul, LawfulCommRing.zero_mul, LawfulCommRing.zero_add]
  induction a with
  | nil => intro k; rfl
  | cons x xs ih =>
    intro k
    simp only [rawMul]
    rw [coeffAt_rawMul_add_left, coeffAt_rawMul_scale_left, hshiftLeft,
        coeffAt_addCoeffs, coeffAt_map_mul]
    cases k with
    | zero => simp only [coeffAt_cons_zero, LawfulCommRing.add_zero]
    | succ k' => simp only [coeffAt_cons_succ, ih k']

theorem pMul_pAdd_left {F : Type} [LawfulCommRing F] [DecidableEq F] (a1 a2 b : List F) :
    pMul (pAdd a1 a2) b = pAdd (pMul a1 b) (pMul a2 b) := by
  rw [show pAdd a1 a2 = trimPoly (rawAddCoeffs a1 a2) from rfl, pMul_trimPoly_left,
      show pMul a1 b = trimPoly (rawMul a1 b) from rfl,
      show pMul a2 b = trimPoly (rawMul a2 b) from rfl,
      pAdd_trimPoly_left, pAdd_trimPoly_right]
  unfold pMul pAdd; rw [trimPoly_eq_iff_coeffAt]
  intro k
  rw [coeffAt_rawMul_add_left, coeffAt_addCoeffs]

theorem pMul_pAdd_right {F : Type} [LawfulCommRing F] [DecidableEq F] (a b1 b2 : List F) :
    pMul a (pAdd b1 b2) = pAdd (pMul a b1) (pMul a b2) := by
  rw [pMul_comm a _, pMul_pAdd_left, pMul_comm b1 a, pMul_comm b2 a]

theorem pMul_pNeg_right {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) :
    pMul a (pNeg b) = pNeg (pMul a b) := by
  have heq : pNeg b = pScale (CommRingOps.neg CommRingOps.one) b := by
    unfold pNeg pScale; rw [trimPoly_eq_iff_coeffAt]; intro k
    rw [coeffAt_negCoeffs, coeffAt_map_mul, LawfulCommRing.neg_mul, LawfulCommRing.one_mul]
  have heq2 : pNeg (pMul a b) = pScale (CommRingOps.neg CommRingOps.one) (pMul a b) := by
    unfold pNeg pScale; rw [trimPoly_eq_iff_coeffAt]; intro k
    rw [coeffAt_negCoeffs, coeffAt_map_mul, LawfulCommRing.neg_mul, LawfulCommRing.one_mul]
  rw [heq, heq2]
  unfold pScale
  rw [pMul_trimPoly_right]
  unfold pMul
  rw [trimPoly_eq_iff_coeffAt]
  intro k
  rw [coeffAt_rawMul_scale_right, coeffAt_map_mul, coeffAt_trimPoly]

theorem pMul_pSub_right {F : Type} [LawfulCommRing F] [DecidableEq F] (a b1 b2 : List F) :
    pMul a (pSub b1 b2) = pSub (pMul a b1) (pMul a b2) := by
  rw [pSub_eq_pAdd_pNeg, pSub_eq_pAdd_pNeg, pMul_pAdd_right, pMul_pNeg_right]

theorem pMul_pScale_right {F : Type} [LawfulCommRing F] [DecidableEq F] (c : F) (a b : List F) :
    pMul a (pScale c b) = pScale c (pMul a b) := by
  unfold pScale; rw [pMul_trimPoly_right]
  unfold pMul; rw [trimPoly_eq_iff_coeffAt]; intro k
  rw [coeffAt_rawMul_scale_right, coeffAt_map_mul, coeffAt_trimPoly]

theorem pMul_one_right {F : Type} [LawfulCommRing F] [DecidableEq F] (a : List F) :
    pMul a [CommRingOps.one] = trimPoly a := by
  rw [pMul_comm]
  unfold pMul; rw [trimPoly_eq_iff_coeffAt]; intro k
  simp [rawMul, coeffAt_addCoeffs, coeffAt_map_mul, LawfulCommRing.one_mul]
  cases k <;> simp [coeffAt, LawfulCommRing.add_zero]

/-- Degree-additivity & integral-domain law for canonical polynomials over `[LawfulField F]`:
    for non-empty trimmed `a, b`, `(pMul a b).length = a.length + b.length - 1` and `pMul a b ≠ []`. -/
theorem pMul_length_of_trimmed_ne_nil
    {F : Type} [LawfulField F] [DecidableEq F]
    {a b : List F}
    (haTrim : IsTrimmed a) (hbTrim : IsTrimmed b)
    (haNe : a ≠ []) (hbNe : b ≠ []) :
    (pMul a b).length = a.length + b.length - 1 ∧ pMul a b ≠ [] := by
  let da := a.length - 1
  let db := b.length - 1
  have haLen : a.length = da + 1 := by cases a with | nil => contradiction | cons _ _ => simp [da]
  have hbLen : b.length = db + 1 := by cases b with | nil => contradiction | cons _ _ => simp [db]
  have haHigh : ∀ i, da < i → coeffAt a i = CommRingOps.zero :=
    fun i hi => coeffAt_eq_zero_of_ge a i (by omega)
  have hbHigh : ∀ j, db < j → coeffAt b j = CommRingOps.zero :=
    fun j hj => coeffAt_eq_zero_of_ge b j (by omega)
  rcases coeffAt_rawMul_high b db hbHigh da a haHigh with ⟨hHigh, hTop⟩
  have hlaNe : coeffAt a da ≠ CommRingOps.zero := by
    have h := leadCoeff_ne_zero_of_trimPoly_ne_nil a (by rwa [haTrim])
    rw [haTrim] at h
    exact h
  have hlbNe : coeffAt b db ≠ CommRingOps.zero := by
    have h := leadCoeff_ne_zero_of_trimPoly_ne_nil b (by rwa [hbTrim])
    rw [hbTrim] at h
    exact h
  have hTopNe : coeffAt (rawMul a b) (da + db) ≠ CommRingOps.zero := by
    rw [hTop]
    intro h0
    rcases LawfulField.mul_eq_zero h0 with h1 | h2
    · exact hlaNe h1
    · exact hlbNe h2
  have hpNe : pMul a b ≠ [] := by
    intro hnil
    have h0 := (trimPoly_eq_nil_iff (rawMul a b)).mp hnil (da + db)
    exact hTopNe h0
  have hle : (pMul a b).length ≤ da + db + 1 :=
    length_trimPoly_le_of_coeffAt_zero (rawMul a b) (da + db + 1)
      (fun k hk => hHigh k (by omega))
  have hge : da + db + 1 ≤ (pMul a b).length := by
    if hlt : (pMul a b).length < da + db + 1 then
      have h0 : coeffAt (pMul a b) (da + db) = CommRingOps.zero :=
        coeffAt_eq_zero_of_ge (pMul a b) (da + db) (by omega)
      rw [pMul, coeffAt_trimPoly] at h0
      exact False.elim (hTopNe h0)
    else
      omega
  refine ⟨by omega, hpNe⟩

theorem pMul_eq_nil_iff {F : Type} [LawfulField F] [DecidableEq F] (a b : List F) :
    pMul a b = [] ↔ trimPoly a = [] ∨ trimPoly b = [] := by
  constructor
  · intro h
    if ha : trimPoly a = [] then
      exact .inl ha
    else if hb : trimPoly b = [] then
      exact .inr hb
    else
      rw [← pMul_trimPoly_left, ← pMul_trimPoly_right (trimPoly a) b] at h
      have hne := (pMul_length_of_trimmed_ne_nil (trimPoly_idem a) (trimPoly_idem b) ha hb).2
      exact False.elim (hne h)
  · rintro (ha | hb)
    · rw [← pMul_trimPoly_left, ha]; rfl
    · rw [← pMul_trimPoly_right, hb, pMul_comm]; rfl

theorem pAdd_length_le {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) (B : Nat)
    (ha : a.length ≤ B) (hb : b.length ≤ B) :
    (pAdd a b).length ≤ B := by
  apply length_trimPoly_le_of_coeffAt_zero _ B
  intro k hk
  rw [coeffAt_addCoeffs, coeffAt_eq_zero_of_ge a k (by omega),
      coeffAt_eq_zero_of_ge b k (by omega), LawfulCommRing.add_zero]

theorem pMul_length_le {F : Type} [LawfulField F] [DecidableEq F] (a b : List F) (ka kb : Nat)
    (ha : a.length ≤ ka + 1) (hb : b.length ≤ kb + 1) :
    (pMul a b).length ≤ ka + kb + 1 := by
  if ha0 : trimPoly a = [] then
    rw [(pMul_eq_nil_iff a b).mpr (.inl ha0)]; simp
  else if hb0 : trimPoly b = [] then
    rw [(pMul_eq_nil_iff a b).mpr (.inr hb0)]; simp
  else
    rw [← pMul_trimPoly_left, ← pMul_trimPoly_right (trimPoly a) b]
    have hlen := (pMul_length_of_trimmed_ne_nil (trimPoly_idem a) (trimPoly_idem b) ha0 hb0).1
    have haL := trimPoly_length_le a
    have hbL := trimPoly_length_le b
    omega

private theorem coeffAt_monomial {F : Type} [CommRingOps F] :
    ∀ (deg k : Nat) (c : F),
      coeffAt (monomial deg c) k = if k = deg then c else CommRingOps.zero
  | 0, 0, _ => rfl
  | 0, k + 1, _ => by
    have hne : k + 1 ≠ 0 := Nat.succ_ne_zero k
    simp only [hne, ↓reduceIte]; rfl
  | deg + 1, 0, _ => by
    have hne : (0 : Nat) ≠ deg + 1 := (Nat.succ_ne_zero deg).symm
    simp only [hne, ↓reduceIte]; rfl
  | deg + 1, k + 1, c => by
    have hcons : monomial (deg + 1) c = CommRingOps.zero :: monomial deg c := rfl
    have heq : (k + 1 = deg + 1) ↔ (k = deg) := ⟨Nat.succ.inj, congrArg Nat.succ⟩
    rw [hcons, coeffAt_cons_succ, coeffAt_monomial deg k c]
    simp only [heq]
  termination_by structural deg => deg

/-- Fuel-bounded constructive Euclidean polynomial division (`0` `WellFounded.fix`, `0` choice). -/
def polyDivModFuel {F : Type} [LawfulField F] [DecidableEq F] :
    Nat → List F → List F → List F × List F
  | 0, a, _ => ([], trimPoly a)
  | fuel + 1, a, b =>
    let a' := trimPoly a
    let b' := trimPoly b
    if b' = [] ∨ a'.length < b'.length then
      ([], a')
    else
      let da := a'.length - 1
      let db := b'.length - 1
      let coef := CommRingOps.mul (coeffAt a' da) (LawfulField.inv (coeffAt b' db))
      let stepQ := monomial (da - db) coef
      let rem1 := pSub a' (pMul stepQ b')
      let qr := polyDivModFuel fuel rem1 b'
      (pAdd stepQ qr.1, qr.2)

/-- Constructive univariate Euclidean division `polyDivMod a b = (q, r)`. -/
def polyDivMod {F : Type} [LawfulField F] [DecidableEq F] (a b : List F) : List F × List F :=
  polyDivModFuel (trimPoly a).length a b

private theorem polyDivModFuel_spec
    {F : Type} [LawfulField F] [DecidableEq F] :
    ∀ (fuel : Nat) (a b : List F),
      trimPoly b ≠ [] →
      (trimPoly a).length ≤ fuel →
      let (q, r) := polyDivModFuel fuel a b
      IsTrimmed q ∧ IsTrimmed r ∧
      trimPoly a = pAdd (pMul q b) r ∧
      r.length < (trimPoly b).length
  | 0, a, b, hbNe, hfuel => by
    have haNil : trimPoly a = [] := by
      cases h : trimPoly a with
      | nil => rfl
      | cons _ _ => rw [h] at hfuel; simp at hfuel
    have hbPos : 0 < (trimPoly b).length := by
      cases h : trimPoly b with
      | nil => exact False.elim (hbNe h)
      | cons _ _ => simp
    dsimp [polyDivModFuel]
    refine ⟨rfl, trimPoly_idem a, ?_, by rw [haNil]; exact hbPos⟩
    rw [haNil]
    have hmul0 : pMul ([] : List F) b = [] := (pMul_eq_nil_iff [] b).mpr (.inl rfl)
    rw [hmul0, pAdd_nil_left]; rfl
  | fuel + 1, a, b, hbNe, hfuel => by
    dsimp only [polyDivModFuel]
    if hstop : trimPoly b = [] ∨ (trimPoly a).length < (trimPoly b).length then
      simp only [hstop, ↓reduceIte]
      rcases hstop with hb0 | hlt
      · exact False.elim (hbNe hb0)
      · refine ⟨rfl, trimPoly_idem a, ?_, hlt⟩
        have hmul0 : pMul ([] : List F) b = [] := (pMul_eq_nil_iff [] b).mpr (.inl rfl)
        rw [hmul0, pAdd_nil_left, trimPoly_idem]
    else
      simp only [hstop, ↓reduceIte]
      have hge : (trimPoly b).length ≤ (trimPoly a).length := by omega
      let a' := trimPoly a
      let b' := trimPoly b
      have hbPos : 1 ≤ b'.length := by
        cases h : b' with
        | nil => exact False.elim (hbNe h)
        | cons _ _ => simp
      have haPos : 1 ≤ a'.length := by dsimp only [a', b'] at hbPos ⊢; omega
      let da := a'.length - 1
      let db := b'.length - 1
      have hlbNe : coeffAt b' db ≠ CommRingOps.zero := by
        have h := leadCoeff_ne_zero_of_trimPoly_ne_nil b hbNe
        simpa [b', db] using h
      let coef := CommRingOps.mul (coeffAt a' da) (LawfulField.inv (coeffAt b' db))
      let stepQ := monomial (da - db) coef
      let rem1 := pSub a' (pMul stepQ b')
      have hStepHigh : ∀ i, da - db < i → coeffAt stepQ i = CommRingOps.zero := by
        intro i hi
        rw [coeffAt_monomial]
        simp [show i ≠ da - db by omega]
      have hbHigh : ∀ j, db < j → coeffAt b' j = CommRingOps.zero :=
        fun j hj => coeffAt_eq_zero_of_ge b' j (by omega)
      rcases coeffAt_rawMul_high b' db hbHigh (da - db) stepQ hStepHigh with ⟨hMulHigh, hMulTop⟩
      have hdaEq : da - db + db = da := by dsimp only [a', b', da, db]; omega
      rw [hdaEq] at hMulHigh hMulTop
      have hRemLen : rem1.length ≤ da := by
        apply length_trimPoly_le_of_coeffAt_zero _ da
        intro k hk
        rw [coeffAt_subCoeffs, pMul, coeffAt_trimPoly (rawMul stepQ b') k]
        if hkEq : k = da then
          subst hkEq
          rw [hMulTop, coeffAt_monomial]
          simp only [↓reduceIte]
          dsimp [coef]
          rw [LawfulCommRing.mul_assoc, LawfulField.inv_mul_cancel hlbNe,
              LawfulCommRing.mul_one, LawfulCommRing.sub_self]
        else
          rw [coeffAt_eq_zero_of_ge a' k (by dsimp only [da] at hk hkEq; omega),
              hMulHigh k (by omega),
              LawfulCommRing.sub_self]
      have hRemTrim : IsTrimmed rem1 := trimPoly_idem _
      have hRemFuel : (trimPoly rem1).length ≤ fuel := by
        rw [hRemTrim]
        dsimp only [a', da] at hRemLen
        omega
      have hb'Ne : trimPoly b' ≠ [] := by rwa [trimPoly_idem]
      have ih := polyDivModFuel_spec fuel rem1 b' hb'Ne hRemFuel
      let qr := polyDivModFuel fuel rem1 b'
      rcases ih with ⟨hqTrim, hrTrim, hRemDecomp, hrLt⟩
      rw [hRemTrim] at hRemDecomp
      rw [trimPoly_idem] at hrLt
      refine ⟨trimPoly_idem _, hrTrim, ?_, hrLt⟩
      -- `a' = pMul stepQ b' + rem1 = pMul stepQ b + (pMul qr.1 b + qr.2) = pMul (stepQ + qr.1) b + qr.2`
      rw [pMul_pAdd_left, ← pMul_trimPoly_right stepQ b, ← pMul_trimPoly_right qr.1 b,
          pAdd_assoc, ← hRemDecomp]
      have hcancel := pAdd_pSub_cancel a' (pMul stepQ b')
      rw [trimPoly_idem] at hcancel
      exact hcancel.symm
  termination_by structural fuel => fuel

/-- **Constructive Euclidean Division Specification (`polyDivMod_spec`)**:
    For any `a, b : List F` with `trimPoly b ≠ []`, `polyDivMod a b = (q, r)` produces canonical
    trimmed polynomials satisfying `trimPoly a = pAdd (pMul q b) r` and `r.length < (trimPoly b).length`. -/
theorem polyDivMod_spec
    {F : Type} [LawfulField F] [DecidableEq F]
    (a b : List F) (hbNe : trimPoly b ≠ []) :
    let (q, r) := polyDivMod a b
    IsTrimmed q ∧ IsTrimmed r ∧
    trimPoly a = pAdd (pMul q b) r ∧
    r.length < (trimPoly b).length :=
  polyDivModFuel_spec (trimPoly a).length a b hbNe (Nat.le_refl _)

/-- Divisibility relation on canonical trimmed polynomials. -/
def DvdTrim {F : Type} [CommRingOps F] [DecidableEq F] (d a : List F) : Prop :=
  ∃ k : List F, trimPoly a = pMul d k

theorem dvdTrim_refl {F : Type} [LawfulCommRing F] [DecidableEq F] (d : List F) :
    DvdTrim d d :=
  ⟨[CommRingOps.one], (pMul_one_right d).symm⟩

theorem dvdTrim_nil {F : Type} [LawfulField F] [DecidableEq F] (d : List F) :
    DvdTrim d [] :=
  ⟨[], ((pMul_eq_nil_iff d []).mpr (.inr rfl)).symm⟩

theorem dvdTrim_trans {F : Type} [LawfulCommRing F] [DecidableEq F]
    {a b c : List F} (hab : DvdTrim a b) (hbc : DvdTrim b c) : DvdTrim a c := by
  rcases hab with ⟨k1, hk1⟩
  rcases hbc with ⟨k2, hk2⟩
  refine ⟨pMul k1 k2, ?_⟩
  rw [hk2, ← pMul_trimPoly_left b k2, hk1, pMul_assoc]

/-- Constructive exact quotient extraction: if `DvdTrim g a` and `trimPoly g ≠ []`, then
    `polyDivMod a g` has remainder `[]` and its quotient `q = (polyDivMod a g).1` satisfies
    `trimPoly a = pMul g q` (`0` classical choice!). -/
theorem exactDiv_of_dvdTrim
    {F : Type} [LawfulField F] [DecidableEq F]
    (a g : List F) (hgNe : trimPoly g ≠ []) (hdvd : DvdTrim g a) :
    let (q, r) := polyDivMod a g
    IsTrimmed q ∧ r = [] ∧ trimPoly a = pMul g q := by
  have hspec := polyDivMod_spec a g hgNe
  dsimp only at hspec ⊢
  rcases hspec with ⟨hqTrim, hrTrim, hDecomp, hrLt⟩
  rcases hdvd with ⟨k, hk⟩
  have hrEq : trimPoly (polyDivMod a g).2 = pMul (trimPoly g) (pSub k (polyDivMod a g).1) := by
    have h1 := pSub_pAdd_cancel_left (pMul (polyDivMod a g).1 g) (polyDivMod a g).2
    rw [← hDecomp, hk, pMul_comm (polyDivMod a g).1 g, ← pMul_pSub_right,
        ← pMul_trimPoly_left g] at h1
    exact h1.symm
  rw [hrTrim] at hrEq
  have hrNil : (polyDivMod a g).2 = [] := by
    if hrNe : (polyDivMod a g).2 = [] then
      exact hrNe
    else
      have hdiffNe : trimPoly (pSub k (polyDivMod a g).1) ≠ [] := by
        intro h0
        rw [(pMul_eq_nil_iff (trimPoly g) _).mpr (.inr h0)] at hrEq
        exact hrNe hrEq
      rw [← pMul_trimPoly_right (trimPoly g)] at hrEq
      have hlen := (pMul_length_of_trimmed_ne_nil (trimPoly_idem g) (trimPoly_idem _) hgNe hdiffNe).1
      rw [← hrEq] at hlen
      have hpos : 1 ≤ (trimPoly (pSub k (polyDivMod a g).1)).length := by
        cases h : trimPoly (pSub k (polyDivMod a g).1) with
        | nil => exact False.elim (hdiffNe h)
        | cons _ _ => simp
      omega
  refine ⟨hqTrim, hrNil, ?_⟩
  rw [hrNil, pAdd_nil_right, pMul_comm] at hDecomp
  simpa [pMul, trimPoly_idem] using hDecomp

/-- Fuel-bounded constructive Euclidean polynomial GCD (`0` `WellFounded.fix`, `0` choice). -/
def polyGcdFuel {F : Type} [LawfulField F] [DecidableEq F] :
    Nat → List F → List F → List F
  | 0, a, _ => trimPoly a
  | fuel + 1, a, b =>
    let a' := trimPoly a
    let b' := trimPoly b
    if b' = [] then a'
    else
      let r := (polyDivMod a' b').2
      polyGcdFuel fuel b' r

/-- Constructive greatest common divisor `polyGcd a b` on `List F`. -/
def polyGcd {F : Type} [LawfulField F] [DecidableEq F] (a b : List F) : List F :=
  polyGcdFuel ((trimPoly b).length + 1) a b

private theorem polyGcdFuel_spec
    {F : Type} [LawfulField F] [DecidableEq F] :
    ∀ (fuel : Nat) (a b : List F),
      (trimPoly b).length < fuel →
      let g := polyGcdFuel fuel a b
      IsTrimmed g ∧
      DvdTrim g a ∧ DvdTrim g b ∧
      (∀ d : List F, DvdTrim d a → DvdTrim d b → DvdTrim d g)
  | 0, _, _, hlt => by cases hlt
  | fuel + 1, a, b, hlt => by
    dsimp only [polyGcdFuel]
    if hb0 : trimPoly b = [] then
      simp only [hb0, ↓reduceIte]
      refine ⟨trimPoly_idem a, ?_, ?_, ?_⟩
      · refine ⟨[CommRingOps.one], ?_⟩
        rw [pMul_one_right, trimPoly_idem]
      · exact ⟨[], by rw [hb0, (pMul_eq_nil_iff _ []).mpr (.inr rfl)]⟩
      · intro d hda _
        rcases hda with ⟨k, hk⟩
        exact ⟨k, by rwa [trimPoly_idem]⟩
    else
      simp only [hb0, ↓reduceIte]
      have hb'Ne : trimPoly (trimPoly b) ≠ [] := by rwa [trimPoly_idem]
      have hdivSpec := polyDivMod_spec (trimPoly a) (trimPoly b) hb'Ne
      dsimp only at hdivSpec
      rcases hdivSpec with ⟨hqT, hrT, hDecomp, hrLt⟩
      rw [trimPoly_idem] at hDecomp
      rw [trimPoly_idem] at hrLt
      let q := (polyDivMod (trimPoly a) (trimPoly b)).1
      let r := (polyDivMod (trimPoly a) (trimPoly b)).2
      change trimPoly a = pAdd (pMul q (trimPoly b)) r at hDecomp
      have hrFuel : (trimPoly r).length < fuel := by
        rw [hrT]
        exact Nat.lt_of_lt_of_le hrLt (Nat.le_of_lt_succ hlt)
      rcases polyGcdFuel_spec fuel (trimPoly b) r hrFuel with ⟨hgT, hgb, hgr, hgUniv⟩
      let g := polyGcdFuel fuel (trimPoly b) r
      refine ⟨hgT, ?_, ?_, ?_⟩
      · -- `g | b` and `g | r` implies `g | q*b + r = a`
        rcases hgb with ⟨kb, hkb⟩
        rcases hgr with ⟨kr, hkr⟩
        rw [trimPoly_idem] at hkb
        rw [hrT] at hkr
        change trimPoly b = pMul g kb at hkb
        change r = pMul g kr at hkr
        refine ⟨pAdd (pMul kb q) kr, ?_⟩
        calc trimPoly a
            = pAdd (pMul q (trimPoly b)) r := hDecomp
          _ = pAdd (pMul (trimPoly b) q) r := by rw [pMul_comm q (trimPoly b)]
          _ = pAdd (pMul (pMul g kb) q) r := congrArg (fun x => pAdd (pMul x q) r) hkb
          _ = pAdd (pMul (pMul g kb) q) (pMul g kr) := congrArg (pAdd (pMul (pMul g kb) q)) hkr
          _ = pAdd (pMul g (pMul kb q)) (pMul g kr) := by rw [pMul_assoc]
          _ = pMul g (pAdd (pMul kb q) kr) := (pMul_pAdd_right g _ _).symm
      · rcases hgb with ⟨kb, hkb⟩
        rw [trimPoly_idem] at hkb
        exact ⟨kb, hkb⟩
      · intro d hda hdb
        apply hgUniv d
        · rcases hdb with ⟨kb, hkb⟩
          exact ⟨kb, by rwa [trimPoly_idem]⟩
        · -- `d | a` and `d | b` implies `d | a - q*b = r`
          rcases hda with ⟨ka, hka⟩
          rcases hdb with ⟨kb, hkb⟩
          have hrSub := pSub_pAdd_cancel_left (pMul q (trimPoly b)) r
          rw [← hDecomp, hka, pMul_comm q (trimPoly b), hkb,
              pMul_assoc, ← pMul_pSub_right] at hrSub
          exact ⟨pSub ka (pMul kb q), hrSub.symm⟩
  termination_by structural fuel => fuel

/-- **Constructive Polynomial GCD Specification (`polyGcd_spec`)**. -/
theorem polyGcd_spec
    {F : Type} [LawfulField F] [DecidableEq F]
    (a b : List F) :
    let g := polyGcd a b
    IsTrimmed g ∧
    DvdTrim g a ∧ DvdTrim g b ∧
    (∀ d : List F, DvdTrim d a → DvdTrim d b → DvdTrim d g) :=
  polyGcdFuel_spec ((trimPoly b).length + 1) a b (Nat.lt_succ_self _)

/-- `HasAffineWitnessS1 d f g D α β P` holds when there exist polynomials `F_poly` (`deg ≤ d`,
    `length ≤ d + 1`) and `G_poly` (`deg ≤ d - 1`, `length ≤ d`) decomposing
    `P(X) = F_poly(X) + (α + β X) G_poly(X)` with at most `s = 1` disagreement coordinate on the
    agreement domain `S_{α,β}(P) ⊆ D` (`[CWYZ26]` Theorem 1.2 / Proposition 6.2). -/
@[expose] def HasAffineWitnessS1
    {F : Type} [CommRingOps F] [DecidableEq F]
    (d : Nat) (f g : F → F) (D : List F) (α β : F) (P : List F) : Prop :=
  ∃ F_poly G_poly : List F,
    F_poly.length ≤ d + 1 ∧
    G_poly.length ≤ d ∧
    (∀ x : F, RoundPoly.evalCoeffs P x =
      CommRingOps.add (RoundPoly.evalCoeffs F_poly x)
        (CommRingOps.mul (CommRingOps.add α (CommRingOps.mul β x))
          (RoundPoly.evalCoeffs G_poly x))) ∧
    let S_p := D.filter (fun z =>
      decide (RoundPoly.evalCoeffs P z =
        CommRingOps.add (f z)
          (CommRingOps.mul (CommRingOps.add α (CommRingOps.mul β z)) (g z))))
    (S_p.filter (fun z =>
      !(decide (RoundPoly.evalCoeffs F_poly z = f z) &&
        decide (RoundPoly.evalCoeffs G_poly z = g z)))).length ≤ 1

/-- **Constructive Welch–Berlekamp Affine Proximity-Gap Theorem (`welch_berlekamp_affine_proximity_gap`)**:
    Over ANY `[LawfulField F] [DecidableEq F]` (`0` algebraic geometry, `0` classical choice),
    whenever `A ≤ D.length` and `2 * D.length + d + 1 < 3 * A` (`δ < (1 - ρ) / 3`), for ANY received
    words `f, g : F → F`, ANY duplicate-free challenge list `S`, ANY duplicate-free subset
    `badPairs ⊆ prodPool S`, and ANY candidate map `P_of : F × F → List F` where every `p = (α, β) ∈ badPairs`
    has `(P_of p).length ≤ d + 1`, `A ≤ |S_{α,β}(P_of p)|`, and `¬ HasAffineWitnessS1 d f g D α β (P_of p)`:
    **`badPairs.length ≤ Nat.max S.length (D.length * (D.length - 1) / 2)`**! -/
theorem welch_berlekamp_affine_proximity_gap
    {F : Type} [LawfulField F] [DecidableEq F]
    (f g : F → F) (D S : List F) (d A : Nat)
    (badPairs : List (F × F)) (P_of : F × F → List F)
    (hD : D.Nodup) (hS : S.Nodup)
    (hAD : A ≤ D.length)
    (hWB : 2 * D.length + d + 1 < 3 * A)
    (hBadNd : badPairs.Nodup)
    (hBadSub : ∀ p ∈ badPairs, p ∈ prodPool S)
    (hBadDeg : ∀ p ∈ badPairs, (P_of p).length ≤ d + 1)
    (hBadAgree : ∀ p ∈ badPairs,
      A ≤ (D.filter (fun z =>
        decide (RoundPoly.evalCoeffs (P_of p) z =
          CommRingOps.add (f z)
            (CommRingOps.mul (CommRingOps.add p.1 (CommRingOps.mul p.2 z)) (g z))))).length)
    (hBadExc : ∀ p ∈ badPairs, ¬ HasAffineWitnessS1 d f g D p.1 p.2 (P_of p)) :
    badPairs.length ≤ Nat.max S.length (D.length * (D.length - 1) / 2) := by
  have hAd2 : d + 2 ≤ A := by omega
  -- 1. Build the `2 * D.length < 3 * A - d - 1` homogeneous WB system `Q(X, Y, Z) = u₀ + u₁ Y + Q₁ Z`:
  let N₀ := A
  let N₁ := A - 1
  let N₂ := A - d
  let N := N₀ + N₁ + N₂
  let rowF := fun (z : F) =>
    geomVec z N₀ ++ List.replicate N₁ CommRingOps.zero ++ (geomVec z N₂).map (CommRingOps.mul (f z))
  let rowG := fun (z : F) =>
    List.replicate N₀ CommRingOps.zero ++ geomVec z N₁ ++ (geomVec z N₂).map (CommRingOps.mul (g z))
  let rows := D.flatMap (fun z => [rowF z, rowG z])
  have hRowsLen : rows.length = 2 * D.length := by
    have aux : ∀ xs : List F, (xs.flatMap (fun z => [rowF z, rowG z])).length = 2 * xs.length := by
      intro xs
      induction xs with
      | nil => rfl
      | cons x tl ih =>
        have hcons : (x :: tl).flatMap (fun z => [rowF z, rowG z]) =
            [rowF x, rowG x] ++ tl.flatMap (fun z => [rowF z, rowG z]) := List.flatMap_cons
        rw [hcons, List.length_append, ih]
        simp
        omega
    exact aux D
  have hRowsLt : rows.length < N := by
    rw [hRowsLen]; dsimp [N, N₀, N₁, N₂]; omega
  have hRowWidth : ∀ row ∈ rows, row.length = N := by
    intro row hmem
    dsimp [rows] at hmem
    rw [List.mem_flatMap] at hmem
    rcases hmem with ⟨z, _, hr⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      · simp [rowF, rowG, List.length_append, geomVec_length, N]
        omega
  rcases gauss_nullspace_witness N rows hRowsLt hRowWidth with ⟨hvLen, hvAny, hvZero⟩
  let v := solveHomogeneous N rows
  have hvLen' : v.length = N₀ + N₁ + N₂ := hvLen
  let u₀ := v.take N₀
  let u₁ := (v.drop N₀).take N₁
  let Q₁ := v.drop (N₀ + N₁)
  have hu₀Len : u₀.length = N₀ := by
    dsimp only [u₀]
    exact List.length_take_of_le (by dsimp only [N₀, N₁, N₂] at hvLen' ⊢; omega)
  have hu₁Len : u₁.length = N₁ := by
    dsimp only [u₁]
    apply List.length_take_of_le
    rw [List.length_drop]
    dsimp only [N₀, N₁, N₂] at hvLen' ⊢
    omega
  have hQ₁Len : Q₁.length = N₂ := by
    dsimp only [Q₁]
    rw [List.length_drop]
    dsimp only [N₀, N₁, N₂] at hvLen' ⊢
    omega
  have hvSplit : v = (u₀ ++ u₁) ++ Q₁ := by
    have h1 : v = v.take N₀ ++ v.drop N₀ := (List.take_append_drop N₀ v).symm
    have h2 : v.drop N₀ = (v.drop N₀).take N₁ ++ (v.drop N₀).drop N₁ :=
      (List.take_append_drop N₁ (v.drop N₀)).symm
    rw [List.drop_drop] at h2
    calc v = u₀ ++ v.drop N₀ := h1
      _ = u₀ ++ (u₁ ++ Q₁) := congrArg (u₀ ++ ·) h2
      _ = (u₀ ++ u₁) ++ Q₁ := (List.append_assoc u₀ u₁ Q₁).symm
  have hInterpF : ∀ z ∈ D,
      CommRingOps.add (RoundPoly.evalCoeffs u₀ z)
        (CommRingOps.mul (f z) (RoundPoly.evalCoeffs Q₁ z)) = CommRingOps.zero := by
    intro z hz
    have h0 : dotVec (rowF z) v = CommRingOps.zero :=
      hvZero (rowF z) (List.mem_flatMap.mpr ⟨z, hz, .head _⟩)
    rw [hvSplit] at h0
    dsimp [rowF] at h0
    rw [dotVec_append_eq _ _ (u₀ ++ u₁) Q₁
          (by simp [List.length_append, geomVec_length, hu₀Len, hu₁Len]),
        dotVec_append_eq _ _ u₀ u₁ (by simp [geomVec_length, hu₀Len]),
        dotVec_geomVec_eq_evalCoeffs z N₀ u₀ hu₀Len,
        dotVec_replicate_zero, LawfulCommRing.add_zero,
        show List.map (CommRingOps.mul (f z)) (geomVec z N₂) = scaleVec (f z) (geomVec z N₂) from rfl,
        dotVec_scaleVec (f z),
        dotVec_geomVec_eq_evalCoeffs z N₂ Q₁ hQ₁Len] at h0
    exact h0
  have hInterpG : ∀ z ∈ D,
      CommRingOps.add (RoundPoly.evalCoeffs u₁ z)
        (CommRingOps.mul (g z) (RoundPoly.evalCoeffs Q₁ z)) = CommRingOps.zero := by
    intro z hz
    have h0 : dotVec (rowG z) v = CommRingOps.zero :=
      hvZero (rowG z) (List.mem_flatMap.mpr ⟨z, hz, .tail _ (.head _)⟩)
    rw [hvSplit] at h0
    dsimp [rowG] at h0
    rw [dotVec_append_eq _ _ (u₀ ++ u₁) Q₁
          (by simp [List.length_append, geomVec_length, hu₀Len, hu₁Len]),
        dotVec_append_eq _ _ u₀ u₁ (by simp [hu₀Len]),
        dotVec_replicate_zero, LawfulCommRing.zero_add,
        dotVec_geomVec_eq_evalCoeffs z N₁ u₁ hu₁Len,
        show List.map (CommRingOps.mul (g z)) (geomVec z N₂) = scaleVec (g z) (geomVec z N₂) from rfl,
        dotVec_scaleVec (g z),
        dotVec_geomVec_eq_evalCoeffs z N₂ Q₁ hQ₁Len] at h0
    exact h0
  have hQ₁Ne : trimPoly Q₁ ≠ [] := by
    intro hQ0
    have hQEval0 : ∀ z, RoundPoly.evalCoeffs Q₁ z = CommRingOps.zero := by
      intro z; rw [← evalCoeffs_trimPoly z Q₁, hQ0]; rfl
    have hu₀Nil : trimPoly u₀ = [] := by
      if hu0 : trimPoly u₀ = [] then exact hu0
      else
        rcases exists_nonroot_of_trim_ne_nil (trimPoly_idem u₀) hu0 hD
          (Nat.le_trans (trimPoly_length_le u₀) (by rw [hu₀Len]; exact hAD)) with ⟨z, hzD, hzNe⟩
        rw [evalCoeffs_trimPoly] at hzNe
        have hf := hInterpF z hzD
        rw [hQEval0 z, LawfulCommRing.mul_zero, LawfulCommRing.add_zero] at hf
        exact False.elim (hzNe hf)
    have hu₁Nil : trimPoly u₁ = [] := by
      if hu1 : trimPoly u₁ = [] then exact hu1
      else
        rcases exists_nonroot_of_trim_ne_nil (trimPoly_idem u₁) hu1 hD
          (Nat.le_trans (trimPoly_length_le u₁) (by rw [hu₁Len]; dsimp only [N₁]; omega)) with ⟨z, hzD, hzNe⟩
        rw [evalCoeffs_trimPoly] at hzNe
        have hg := hInterpG z hzD
        rw [hQEval0 z, LawfulCommRing.mul_zero, LawfulCommRing.add_zero] at hg
        exact False.elim (hzNe hg)
    have hallZero : ∀ w : List F, trimPoly w = [] → ∀ x ∈ w, x = CommRingOps.zero := by
      intro w hw x hx
      rcases List.getElem?_of_mem hx with ⟨idx, hidx⟩
      have hc := (trimPoly_eq_nil_iff w).mp hw idx
      simpa [coeffAt, List.getD, hidx] using hc
    rcases mem_of_any_true hvAny with ⟨x, hxMem, hxPred⟩
    change x ∈ v at hxMem
    rw [hvSplit, List.mem_append, List.mem_append] at hxMem
    have hx0 : x = CommRingOps.zero := by
      rcases hxMem with (hx0 | hx1) | hx2
      · exact hallZero u₀ hu₀Nil x hx0
      · exact hallZero u₁ hu₁Nil x hx1
      · exact hallZero Q₁ hQ0 x hx2
    simp [hx0] at hxPred
  let g12 := polyGcd u₁ Q₁
  let gcdPoly := polyGcd u₀ g12
  have hg12Spec := polyGcd_spec u₁ Q₁
  dsimp only at hg12Spec
  rcases hg12Spec with ⟨hg12Trim, hg12Dvd1, hg12DvdQ, hg12Univ⟩
  have hgcdSpec := polyGcd_spec u₀ g12
  dsimp only at hgcdSpec
  rcases hgcdSpec with ⟨hgcdTrim, hgcdDvd0, hgcdDvd12, hgcdUniv⟩
  change IsTrimmed gcdPoly at hgcdTrim
  have hgcdDvd1 : DvdTrim gcdPoly u₁ := dvdTrim_trans hgcdDvd12 hg12Dvd1
  have hgcdDvdQ : DvdTrim gcdPoly Q₁ := dvdTrim_trans hgcdDvd12 hg12DvdQ
  have hgcdNe : trimPoly gcdPoly ≠ [] := by
    rw [hgcdTrim]
    intro h0
    change gcdPoly = [] at h0
    rcases hgcdDvdQ with ⟨k, hk⟩
    rw [h0, (pMul_eq_nil_iff [] k).mpr (.inl rfl)] at hk
    exact hQ₁Ne hk
  have hex0 := exactDiv_of_dvdTrim u₀ gcdPoly hgcdNe hgcdDvd0
  have hex1 := exactDiv_of_dvdTrim u₁ gcdPoly hgcdNe hgcdDvd1
  have hexQ := exactDiv_of_dvdTrim Q₁ gcdPoly hgcdNe hgcdDvdQ
  dsimp only at hex0 hex1 hexQ
  rcases hex0 with ⟨hu0RedTrim, _, hu₀Fact⟩
  rcases hex1 with ⟨hu1RedTrim, _, hu₁Fact⟩
  rcases hexQ with ⟨hQ1RedTrim, _, hQ₁Fact⟩
  let u0Red := (polyDivMod u₀ gcdPoly).1
  let u1Red := (polyDivMod u₁ gcdPoly).1
  let Q1Red := (polyDivMod Q₁ gcdPoly).1
  have hQ1RedNe : Q1Red ≠ [] := by
    intro h0
    change (polyDivMod Q₁ gcdPoly).1 = [] at h0
    rw [h0, (pMul_eq_nil_iff gcdPoly []).mpr (.inr rfl)] at hQ₁Fact
    exact hQ₁Ne hQ₁Fact
  have hCoprime : ∀ h : List F, IsTrimmed h →
      DvdTrim h u0Red → DvdTrim h u1Red → DvdTrim h Q1Red → h.length ≤ 1 := by
    intro h hhTrim hd0 hd1 hdQ
    if hhNil : h = [] then
      rw [hhNil]; simp
    else
      rcases hd0 with ⟨k0, hk0⟩
      rcases hd1 with ⟨k1, hk1⟩
      rcases hdQ with ⟨kQ, hkQ⟩
      rw [hu0RedTrim] at hk0; rw [hu1RedTrim] at hk1; rw [hQ1RedTrim] at hkQ
      have hdvd0 : DvdTrim (pMul gcdPoly h) u₀ :=
        ⟨k0, by rw [hu₀Fact]; change _ = _; rw [hk0, pMul_assoc]⟩
      have hdvd1 : DvdTrim (pMul gcdPoly h) u₁ :=
        ⟨k1, by rw [hu₁Fact]; change _ = _; rw [hk1, pMul_assoc]⟩
      have hdvdQ : DvdTrim (pMul gcdPoly h) Q₁ :=
        ⟨kQ, by rw [hQ₁Fact]; change _ = _; rw [hkQ, pMul_assoc]⟩
      have hdvdGcd : DvdTrim (pMul gcdPoly h) gcdPoly :=
        hgcdUniv _ hdvd0 (hg12Univ _ hdvd1 hdvdQ)
      rcases hdvdGcd with ⟨m, hm⟩
      change trimPoly gcdPoly = pMul (pMul gcdPoly h) m at hm
      rw [hgcdTrim, pMul_assoc] at hm
      have hhmNe : trimPoly (pMul h m) ≠ [] := by
        intro h0
        have h1 : pMul h m = [] := by
          have ht : trimPoly (pMul h m) = pMul h m := trimPoly_idem _
          rwa [ht] at h0
        rw [h1, (pMul_eq_nil_iff gcdPoly []).mpr (.inr rfl)] at hm
        exact hgcdNe (by rw [hgcdTrim]; exact hm)
      have hgNeRaw : gcdPoly ≠ [] := by rwa [hgcdTrim] at hgcdNe
      have hgPos : 1 ≤ gcdPoly.length := by
        cases hgEq : gcdPoly with
        | nil => exact False.elim (hgNeRaw hgEq)
        | cons _ _ => simp
      have hlen1 := (pMul_length_of_trimmed_ne_nil hgcdTrim (trimPoly_idem _) hgNeRaw
        (by simpa [trimPoly_idem] using hhmNe)).1
      rw [pMul_trimPoly_right, ← hm] at hlen1
      have hptHm : trimPoly (pMul h m) = pMul h m := trimPoly_idem _
      rw [hptHm] at hlen1
      have hmNe : trimPoly m ≠ [] := by
        intro hm0
        rw [(pMul_eq_nil_iff h m).mpr (.inr hm0)] at hhmNe
        exact hhmNe rfl
      have hlen2 := (pMul_length_of_trimmed_ne_nil hhTrim (trimPoly_idem m) hhNil hmNe).1
      rw [pMul_trimPoly_right] at hlen2
      have hmPos : 1 ≤ (trimPoly m).length := by
        cases hmEq : trimPoly m with
        | nil => exact False.elim (hmNe hmEq)
        | cons _ _ => simp
      omega
  have hNegAdd : ∀ (x y : F),
      CommRingOps.add (CommRingOps.neg x) (CommRingOps.neg y) =
        CommRingOps.neg (CommRingOps.add x y) := by
    intro x y
    apply LawfulCommRing.add_left_cancel (a := CommRingOps.add x y)
    rw [LawfulCommRing.add_right_neg,
        LawfulCommRing.add_assoc x y _,
        ← LawfulCommRing.add_assoc y (CommRingOps.neg x) (CommRingOps.neg y),
        LawfulCommRing.add_comm y (CommRingOps.neg x),
        LawfulCommRing.add_assoc (CommRingOps.neg x) y (CommRingOps.neg y),
        LawfulCommRing.add_right_neg, LawfulCommRing.add_zero,
        LawfulCommRing.add_right_neg]
  have hReduced : ∀ p ∈ badPairs,
      pAdd (pAdd u0Red (pMul [p.1, p.2] u1Red)) (pMul Q1Red (P_of p)) = [] := by
    intro p hpMem
    let R := pAdd (pAdd u₀ (pMul [p.1, p.2] u₁)) (pMul Q₁ (P_of p))
    have hRLen : R.length ≤ A := by
      have hL1 : (pMul [p.1, p.2] u₁).length ≤ A := by
        have h := pMul_length_le [p.1, p.2] u₁ 1 (A - 2) (by simp)
          (by rw [hu₁Len]; dsimp only [N₁]; omega)
        omega
      have hL2 : (pMul Q₁ (P_of p)).length ≤ A := by
        have h := pMul_length_le Q₁ (P_of p) (A - d - 1) d
          (by rw [hQ₁Len]; dsimp only [N₂]; omega) (hBadDeg p hpMem)
        omega
      exact pAdd_length_le _ _ A
        (pAdd_length_le _ _ A (by rw [hu₀Len]; exact Nat.le_refl A) hL1) hL2
    let S_p := D.filter (fun z =>
      decide (RoundPoly.evalCoeffs (P_of p) z =
        CommRingOps.add (f z)
          (CommRingOps.mul (CommRingOps.add p.1 (CommRingOps.mul p.2 z)) (g z))))
    have hSpNd : S_p.Nodup := List.Pairwise.filter _ hD
    have hSpLen : A ≤ S_p.length := hBadAgree p hpMem
    have hRZeroOnSp : ∀ z ∈ S_p, RoundPoly.evalCoeffs R z = CommRingOps.zero := by
      intro z hzSp
      rcases List.mem_filter.mp hzSp with ⟨hzD, hzAgDec⟩
      have hzAg : RoundPoly.evalCoeffs (P_of p) z =
          CommRingOps.add (f z)
            (CommRingOps.mul (CommRingOps.add p.1 (CommRingOps.mul p.2 z)) (g z)) :=
        of_decide_eq_true hzAgDec
      have hF0 := hInterpF z hzD
      have hG0 := hInterpG z hzD
      have hu₀Ev : RoundPoly.evalCoeffs u₀ z =
          CommRingOps.neg (CommRingOps.mul (f z) (RoundPoly.evalCoeffs Q₁ z)) := by
        apply LawfulCommRing.add_left_cancel
          (a := CommRingOps.mul (f z) (RoundPoly.evalCoeffs Q₁ z))
        rw [LawfulCommRing.add_right_neg, LawfulCommRing.add_comm]
        exact hF0
      have hu₁Ev : RoundPoly.evalCoeffs u₁ z =
          CommRingOps.neg (CommRingOps.mul (g z) (RoundPoly.evalCoeffs Q₁ z)) := by
        apply LawfulCommRing.add_left_cancel
          (a := CommRingOps.mul (g z) (RoundPoly.evalCoeffs Q₁ z))
        rw [LawfulCommRing.add_right_neg, LawfulCommRing.add_comm]
        exact hG0
      have hLinEv : RoundPoly.evalCoeffs [p.1, p.2] z =
          CommRingOps.add p.1 (CommRingOps.mul p.2 z) := by
        simp [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero,
              LawfulCommRing.mul_comm]
      dsimp [R]
      rw [evalCoeffs_pAdd, evalCoeffs_pAdd, evalCoeffs_pMul, evalCoeffs_pMul,
          hLinEv, hu₀Ev, hu₁Ev, hzAg]
      let lineVal := CommRingOps.add p.1 (CommRingOps.mul p.2 z)
      let qVal := RoundPoly.evalCoeffs Q₁ z
      change CommRingOps.add
        (CommRingOps.add (CommRingOps.neg (CommRingOps.mul (f z) qVal))
          (CommRingOps.mul lineVal (CommRingOps.neg (CommRingOps.mul (g z) qVal))))
        (CommRingOps.mul qVal (CommRingOps.add (f z) (CommRingOps.mul lineVal (g z)))) =
        CommRingOps.zero
      rw [LawfulCommRing.mul_neg, ← LawfulCommRing.mul_assoc lineVal (g z) qVal,
          hNegAdd, LawfulCommRing.left_distrib,
          LawfulCommRing.mul_comm qVal (f z), LawfulCommRing.mul_comm qVal _,
          LawfulCommRing.add_left_neg]
    have hRNil : R = [] := by
      if hRNe : R = [] then exact hRNe
      else
        have hRT : IsTrimmed R := trimPoly_idem _
        rcases exists_nonroot_of_trim_ne_nil hRT hRNe hSpNd (Nat.le_trans hRLen hSpLen) with
          ⟨z, hzSp, hzNe⟩
        exact False.elim (hzNe (hRZeroOnSp z hzSp))
    have hRFact : R = pMul gcdPoly (pAdd (pAdd u0Red (pMul [p.1, p.2] u1Red)) (pMul Q1Red (P_of p))) := by
      dsimp [R, u0Red, u1Red, Q1Red]
      rw [← pAdd_trimPoly_left u₀, hu₀Fact,
          ← pMul_trimPoly_right [p.1, p.2] u₁, hu₁Fact,
          pMul_comm [p.1, p.2] (pMul gcdPoly (polyDivMod u₁ gcdPoly).1),
          pMul_assoc, pMul_comm (polyDivMod u₁ gcdPoly).1 [p.1, p.2],
          ← pMul_pAdd_right,
          ← pMul_trimPoly_left Q₁, hQ₁Fact, pMul_assoc,
          ← pMul_pAdd_right]
    rw [hRNil] at hRFact
    rcases (pMul_eq_nil_iff gcdPoly _).mp hRFact.symm with hg0 | hRed0
    · exact False.elim (hgcdNe hg0)
    · have hRedT : IsTrimmed (pAdd (pAdd u0Red (pMul [p.1, p.2] u1Red)) (pMul Q1Red (P_of p))) :=
        trimPoly_idem _
      rwa [hRedT] at hRed0
  have hLinearMul : ∀ (α β : F) (w : List F),
      pMul [α, β] w = pAdd (pScale α w) (pScale β (CommRingOps.zero :: w)) := by
    intro α β w
    have hz1 : ∀ m, coeffAt ([CommRingOps.zero] : List F) m = CommRingOps.zero := by
      intro m; cases m <;> rfl
    unfold pMul pAdd pScale
    rw [trimPoly_eq_iff_coeffAt]
    intro k
    rw [coeffAt_addCoeffs, coeffAt_trimPoly, coeffAt_trimPoly, coeffAt_map_mul, coeffAt_map_mul]
    simp only [rawMul, coeffAt_addCoeffs, coeffAt_map_mul]
    cases k with
    | zero => simp only [coeffAt_cons_zero, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    | succ k' =>
      simp only [coeffAt_cons_succ, coeffAt_addCoeffs, coeffAt_map_mul, hz1,
                 LawfulCommRing.add_zero]
  have hQ1RedPos : 1 ≤ Q1Red.length := by
    cases hEq : Q1Red with
    | nil => exact False.elim (hQ1RedNe hEq)
    | cons _ _ => simp
  if hQ1RedOne : Q1Red.length = 1 then
    have hQ1RedForm : ∃ c : F, Q1Red = [c] ∧ c ≠ CommRingOps.zero := by
      rcases hEqQ : Q1Red with _ | ⟨c, _ | _⟩
      · rw [hEqQ] at hQ1RedOne; cases hQ1RedOne
      · refine ⟨c, rfl, ?_⟩
        intro hc0; subst hc0
        have ht : IsTrimmed Q1Red := hQ1RedTrim
        rw [hEqQ] at ht
        simp [IsTrimmed, trimPoly] at ht
      · rw [hEqQ] at hQ1RedOne; cases hQ1RedOne
    rcases hQ1RedForm with ⟨c, hQ1RedEq, hcNe⟩
    let negInvC := CommRingOps.neg (LawfulField.inv c)
    let F_poly := pScale negInvC u0Red
    let G_poly := pScale negInvC u1Red
    have hFT : IsTrimmed F_poly := trimPoly_idem _
    have hGT : IsTrimmed G_poly := trimPoly_idem _
    have hPEq : ∀ p ∈ badPairs, trimPoly (P_of p) = pAdd F_poly (pMul [p.1, p.2] G_poly) := by
      intro p hpMem
      have hRed := hReduced p hpMem
      have hScaleC : ∀ w, pMul [c] w = pScale c w := by
        intro w; unfold pMul pScale; rw [trimPoly_eq_iff_coeffAt]; intro k
        simp only [rawMul, coeffAt_addCoeffs, coeffAt_map_mul]
        cases k with
        | zero => simp only [coeffAt_cons_zero, LawfulCommRing.add_zero]
        | succ _ => simp only [coeffAt_cons_succ, coeffAt_nil, LawfulCommRing.add_zero]
      rw [hQ1RedEq, hScaleC] at hRed
      apply eq_of_isTrimmed_coeffAt _ _ (trimPoly_idem _) (trimPoly_idem _)
      intro k
      have hc0 : coeffAt (pAdd (pAdd u0Red (pMul [p.1, p.2] u1Red)) (pScale c (P_of p))) k =
          CommRingOps.zero := by
        rw [hRed, coeffAt_nil]
      rw [coeffAt_pAdd, coeffAt_pAdd, coeffAt_pScale] at hc0
      have hmul := congrArg (CommRingOps.mul (LawfulField.inv c)) hc0
      rw [LawfulCommRing.mul_zero, LawfulCommRing.left_distrib, LawfulCommRing.left_distrib,
          ← LawfulCommRing.mul_assoc (LawfulField.inv c) c _,
          LawfulField.inv_mul_cancel hcNe, LawfulCommRing.one_mul] at hmul
      have hPval : coeffAt (P_of p) k =
          CommRingOps.add
            (CommRingOps.mul negInvC (coeffAt u0Red k))
            (CommRingOps.mul negInvC (coeffAt (pMul [p.1, p.2] u1Red) k)) := by
        dsimp [negInvC]
        rw [LawfulCommRing.neg_mul, LawfulCommRing.neg_mul, hNegAdd]
        apply LawfulCommRing.add_left_cancel
          (a := CommRingOps.add (CommRingOps.mul (LawfulField.inv c) (coeffAt u0Red k))
                  (CommRingOps.mul (LawfulField.inv c) (coeffAt (pMul [p.1, p.2] u1Red) k)))
        rw [LawfulCommRing.add_right_neg, hmul]
      rw [coeffAt_trimPoly, hPval]
      change _ = coeffAt (pAdd F_poly (pMul [p.1, p.2] G_poly)) k
      rw [coeffAt_pAdd,
          pMul_pScale_right negInvC [p.1, p.2] u1Red, coeffAt_pScale, coeffAt_pScale]
    if hDegFG : F_poly.length ≤ d + 1 ∧ G_poly.length ≤ d then
      have hSubBad : ∀ p ∈ badPairs,
          p ∈ (prodPool S).filter (fun q =>
            decide (2 ≤ (D.filter (isAccidentalAgreement F_poly G_poly f g q.1 q.2)).length)) := by
        intro p hpMem
        rw [List.mem_filter]
        refine ⟨hBadSub p hpMem, decide_eq_true ?_⟩
        have hPolyEq : ∀ x : F, RoundPoly.evalCoeffs (P_of p) x =
            CommRingOps.add (RoundPoly.evalCoeffs F_poly x)
              (CommRingOps.mul (CommRingOps.add p.1 (CommRingOps.mul p.2 x))
                (RoundPoly.evalCoeffs G_poly x)) := by
          intro x
          rw [← evalCoeffs_trimPoly x (P_of p), hPEq p hpMem, evalCoeffs_pAdd, evalCoeffs_pMul]
          simp [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero,
                LawfulCommRing.mul_comm]
        let S_p := D.filter (fun z =>
          decide (RoundPoly.evalCoeffs (P_of p) z =
            CommRingOps.add (f z)
              (CommRingOps.mul (CommRingOps.add p.1 (CommRingOps.mul p.2 z)) (g z))))
        let dis := S_p.filter (fun z =>
          !(decide (RoundPoly.evalCoeffs F_poly z = f z) &&
            decide (RoundPoly.evalCoeffs G_poly z = g z)))
        have hDisGe2 : 2 ≤ dis.length := by
          if hle1 : dis.length ≤ 1 then
            exact False.elim (hBadExc p hpMem ⟨F_poly, G_poly, hDegFG.1, hDegFG.2, hPolyEq, hle1⟩)
          else
            exact Nat.lt_of_not_ge hle1
        have hDisNd : dis.Nodup := List.Pairwise.filter _ (List.Pairwise.filter _ hD)
        have hDisSub : ∀ z ∈ dis, z ∈ D.filter (isAccidentalAgreement F_poly G_poly f g p.1 p.2) := by
          intro z hz
          rcases List.mem_filter.mp hz with ⟨hzSp, hzNotBoth⟩
          rcases List.mem_filter.mp hzSp with ⟨hzD, hzAgDec⟩
          have hzAg := of_decide_eq_true hzAgDec
          rw [hPolyEq z] at hzAg
          rw [List.mem_filter]
          refine ⟨hzD, ?_⟩
          unfold isAccidentalAgreement
          simp [hzAg, hzNotBoth]
        exact Nat.le_trans hDisGe2 (nodup_length_le_of_subset hDisNd hDisSub)
      have hle := Nat.le_trans
        (nodup_length_le_of_subset hBadNd hSubBad)
        (committed_polynomial_pair_bad_lines_le_choose2 F_poly G_poly f g D S hD hS)
      exact Nat.le_trans hle (Nat.le_max_right _ _)
    else
      let mTop := Nat.max (F_poly.length - 1) G_poly.length
      have hmTopGe : d + 1 ≤ mTop := by
        if h1 : F_poly.length ≤ d + 1 then
          if h2 : G_poly.length ≤ d then
            exact False.elim (hDegFG ⟨h1, h2⟩)
          else
            exact Nat.le_trans (Nat.lt_of_not_ge h2) (Nat.le_max_right _ _)
        else
          have h2 : d + 1 ≤ F_poly.length - 1 := Nat.sub_le_sub_right (Nat.lt_of_not_ge h1) 1
          exact Nat.le_trans h2 (Nat.le_max_left _ _)
      have hmTopPos : 1 ≤ mTop := Nat.le_trans (Nat.le_add_left 1 d) hmTopGe
      let Δ₀ := coeffAt F_poly mTop
      let Δ₁ := coeffAt G_poly mTop
      let Δ₂ := coeffAt G_poly (mTop - 1)
      have hΔNz : Δ₀ ≠ CommRingOps.zero ∨ Δ₁ ≠ CommRingOps.zero ∨ Δ₂ ≠ CommRingOps.zero := by
        if hFG : G_poly.length ≤ F_poly.length - 1 then
          have hmEq : mTop = F_poly.length - 1 := Nat.max_eq_left hFG
          have hFNe : F_poly ≠ [] := by
            intro h0; rw [h0] at hmEq; rw [hmEq] at hmTopPos; cases hmTopPos
          have hLead := leadCoeff_ne_zero_of_trimPoly_ne_nil F_poly (by rwa [hFT])
          rw [hFT, ← hmEq] at hLead
          exact .inl hLead
        else
          have hmEq : mTop = G_poly.length :=
            Nat.max_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge hFG))
          have hGNe : G_poly ≠ [] := by
            intro h0; rw [h0] at hmEq; rw [hmEq] at hmTopPos; cases hmTopPos
          have hLead := leadCoeff_ne_zero_of_trimPoly_ne_nil G_poly (by rwa [hGT])
          rw [hGT] at hLead
          have hm1 : mTop - 1 = G_poly.length - 1 := congrArg (· - 1) hmEq
          exact .inr (.inr (by dsimp only [Δ₂]; rwa [hm1]))
      have hSubDuet : ∀ p ∈ badPairs,
          p ∈ (prodPool S).filter (fun q =>
            decide (evalAffineDuet Δ₀ Δ₁ Δ₂ q.1 q.2 = CommRingOps.zero)) := by
        intro p hpMem
        rw [List.mem_filter]
        refine ⟨hBadSub p hpMem, decide_eq_true ?_⟩
        have h0 : coeffAt (trimPoly (P_of p)) mTop = CommRingOps.zero := by
          rw [coeffAt_trimPoly]
          exact coeffAt_eq_zero_of_ge (P_of p) mTop (Nat.le_trans (hBadDeg p hpMem) hmTopGe)
        rw [hPEq p hpMem, hLinearMul, coeffAt_pAdd, coeffAt_pAdd,
            coeffAt_pScale p.1 G_poly, coeffAt_pScale p.2 (CommRingOps.zero :: G_poly)] at h0
        have hShift : coeffAt (CommRingOps.zero :: G_poly) mTop = coeffAt G_poly (mTop - 1) := by
          cases hm : mTop with
          | zero => rw [hm] at hmTopPos; cases hmTopPos
          | succ m' => simp [coeffAt_cons_succ]
        rw [hShift] at h0
        simpa [evalAffineDuet, Δ₀, Δ₁, Δ₂] using h0
      have hle := Nat.le_trans
        (nodup_length_le_of_subset hBadNd hSubDuet)
        (affine_duet_roots_le_card Δ₀ Δ₁ Δ₂ S hS hΔNz)
      exact Nat.le_trans hle (Nat.le_max_left _ _)
  else
    have hQ1RedGe2 : 2 ≤ Q1Red.length := by
      if hle1 : Q1Red.length ≤ 1 then
        exact False.elim (hQ1RedOne (Nat.le_antisymm hle1 hQ1RedPos))
      else
        exact Nat.lt_of_not_ge hle1
    have hQ1RedTrimNe : trimPoly Q1Red ≠ [] := by rwa [hQ1RedTrim]
    have hSp0 := polyDivMod_spec u0Red Q1Red hQ1RedTrimNe
    have hSp1 := polyDivMod_spec u1Red Q1Red hQ1RedTrimNe
    have hSp2 := polyDivMod_spec (CommRingOps.zero :: u1Red) Q1Red hQ1RedTrimNe
    dsimp only at hSp0 hSp1 hSp2
    rcases hSp0 with ⟨_, hr₀T, hDiv0, hr₀Lt⟩
    rcases hSp1 with ⟨_, hr₁T, hDiv1, hr₁Lt⟩
    rcases hSp2 with ⟨_, hr₂T, hDiv2, hr₂Lt⟩
    let q₀ := (polyDivMod u0Red Q1Red).1
    let r₀ := (polyDivMod u0Red Q1Red).2
    let q₁ := (polyDivMod u1Red Q1Red).1
    let r₁ := (polyDivMod u1Red Q1Red).2
    let q₂ := (polyDivMod (CommRingOps.zero :: u1Red) Q1Red).1
    let r₂ := (polyDivMod (CommRingOps.zero :: u1Red) Q1Red).2
    change IsTrimmed r₀ at hr₀T
    change IsTrimmed r₁ at hr₁T
    change IsTrimmed r₂ at hr₂T
    change trimPoly u0Red = pAdd (pMul q₀ Q1Red) r₀ at hDiv0
    change trimPoly u1Red = pAdd (pMul q₁ Q1Red) r₁ at hDiv1
    change trimPoly (CommRingOps.zero :: u1Red) = pAdd (pMul q₂ Q1Red) r₂ at hDiv2
    change r₀.length < (trimPoly Q1Red).length at hr₀Lt
    change r₁.length < (trimPoly Q1Red).length at hr₁Lt
    change r₂.length < (trimPoly Q1Red).length at hr₂Lt
    change IsTrimmed u0Red at hu0RedTrim
    change IsTrimmed u1Red at hu1RedTrim
    change IsTrimmed Q1Red at hQ1RedTrim
    rw [hu0RedTrim] at hDiv0
    rw [hu1RedTrim] at hDiv1
    rw [hQ1RedTrim] at hr₀Lt hr₁Lt hr₂Lt
    have hNotBothNil : ¬ (r₀ = [] ∧ r₁ = []) := by
      rintro ⟨hr0, hr1⟩
      have hd0 : DvdTrim Q1Red u0Red := by
        have h := hDiv0
        rw [hr0, pAdd_nil_right, pMul_comm] at h
        have hpt : trimPoly (pMul Q1Red q₀) = pMul Q1Red q₀ := trimPoly_idem _
        rw [hpt] at h
        exact ⟨q₀, by rw [hu0RedTrim]; exact h⟩
      have hd1 : DvdTrim Q1Red u1Red := by
        have h := hDiv1
        rw [hr1, pAdd_nil_right, pMul_comm] at h
        have hpt : trimPoly (pMul Q1Red q₁) = pMul Q1Red q₁ := trimPoly_idem _
        rw [hpt] at h
        exact ⟨q₁, by rw [hu1RedTrim]; exact h⟩
      have hle1 := hCoprime Q1Red hQ1RedTrim hd0 hd1 (dvdTrim_refl Q1Red)
      omega
    let jIdx := if r₀ = [] then r₁.length - 1 else r₀.length - 1
    let Δ₀ := coeffAt r₀ jIdx
    let Δ₁ := coeffAt r₁ jIdx
    let Δ₂ := coeffAt r₂ jIdx
    have hΔNz : Δ₀ ≠ CommRingOps.zero ∨ Δ₁ ≠ CommRingOps.zero ∨ Δ₂ ≠ CommRingOps.zero := by
      if hr0 : r₀ = [] then
        have hr1Ne : r₁ ≠ [] := fun hr1 => hNotBothNil ⟨hr0, hr1⟩
        have hLead := leadCoeff_ne_zero_of_trimPoly_ne_nil r₁ (by rwa [hr₁T])
        rw [hr₁T] at hLead
        exact .inr (.inl (by simpa [Δ₁, jIdx, hr0] using hLead))
      else
        have hLead := leadCoeff_ne_zero_of_trimPoly_ne_nil r₀ (by rwa [hr₀T])
        rw [hr₀T] at hLead
        exact .inl (by simpa [Δ₀, jIdx, hr0] using hLead)
    have hSubDuet : ∀ p ∈ badPairs,
        p ∈ (prodPool S).filter (fun q =>
          decide (evalAffineDuet Δ₀ Δ₁ Δ₂ q.1 q.2 = CommRingOps.zero)) := by
      intro p hpMem
      rw [List.mem_filter]
      refine ⟨hBadSub p hpMem, decide_eq_true ?_⟩
      have hRed := hReduced p hpMem
      rw [hLinearMul] at hRed
      let rComb := pAdd (pAdd r₀ (pScale p.1 r₁)) (pScale p.2 r₂)
      let qComb := pAdd (pAdd (pAdd q₀ (pScale p.1 q₁)) (pScale p.2 q₂)) (P_of p)
      have hCombLen : rComb.length ≤ Q1Red.length - 1 := by
        have h0L : r₀.length ≤ Q1Red.length - 1 := by omega
        have h1 : (pScale p.1 r₁).length ≤ Q1Red.length - 1 :=
          Nat.le_trans (trimPoly_length_le _) (by rw [List.length_map]; omega)
        have h2 : (pScale p.2 r₂).length ≤ Q1Red.length - 1 :=
          Nat.le_trans (trimPoly_length_le _) (by rw [List.length_map]; omega)
        exact pAdd_length_le _ _ (Q1Red.length - 1)
          (pAdd_length_le _ _ (Q1Red.length - 1) h0L h1) h2
      have hScaleAdd : ∀ (c : F) (x y : List F), pScale c (pAdd x y) = pAdd (pScale c x) (pScale c y) := by
        intro c x y
        unfold pScale pAdd; rw [trimPoly_eq_iff_coeffAt]; intro k
        simp [coeffAt_map_mul, coeffAt_trimPoly, coeffAt_addCoeffs, LawfulCommRing.left_distrib]
      have hScaleTrim : ∀ (c : F) (x : List F), pScale c (trimPoly x) = pScale c x := by
        intro c x
        unfold pScale; rw [trimPoly_eq_iff_coeffAt]; intro k
        simp [coeffAt_map_mul, coeffAt_trimPoly]
      have hScaleMulLeft : ∀ (c : F) (x y : List F), pScale c (pMul x y) = pMul (pScale c x) y := by
        intro c x y
        rw [pMul_comm x y, ← pMul_pScale_right, pMul_comm y (pScale c x)]
      have hSum0 : pAdd (pMul Q1Red qComb) rComb = [] := by
        have hLHS : pAdd (pAdd u0Red (pAdd (pScale p.1 u1Red) (pScale p.2 (CommRingOps.zero :: u1Red))))
            (pMul Q1Red (P_of p)) = pAdd (pMul Q1Red qComb) rComb := by
          rw [← hScaleTrim p.2 (CommRingOps.zero :: u1Red), hDiv2,
              hDiv0, hDiv1, hScaleAdd, hScaleAdd,
              hScaleMulLeft, hScaleMulLeft]
          unfold pAdd
          rw [trimPoly_eq_iff_coeffAt]
          intro k
          simp only [coeffAt_addCoeffs, coeffAt_trimPoly, qComb, rComb, pAdd]
          have hqExpand : coeffAt (pMul Q1Red (trimPoly (rawAddCoeffs
              (trimPoly (rawAddCoeffs
                (trimPoly (rawAddCoeffs q₀ (pScale p.1 q₁))) (pScale p.2 q₂)))
              (P_of p)))) k =
              CommRingOps.add
                (CommRingOps.add
                  (CommRingOps.add (coeffAt (pMul q₀ Q1Red) k) (coeffAt (pMul (pScale p.1 q₁) Q1Red) k))
                  (coeffAt (pMul (pScale p.2 q₂) Q1Red) k))
                (coeffAt (pMul Q1Red (P_of p)) k) := by
            change coeffAt (pMul Q1Red qComb) k = _
            dsimp [qComb]
            rw [pMul_pAdd_right, pMul_pAdd_right, pMul_pAdd_right,
                coeffAt_pAdd, coeffAt_pAdd, coeffAt_pAdd,
                pMul_comm Q1Red q₀, pMul_comm Q1Red (pScale p.1 q₁), pMul_comm Q1Red (pScale p.2 q₂)]
          rw [hqExpand]
          let A0 := coeffAt (pMul q₀ Q1Red) k
          let R0 := coeffAt r₀ k
          let A1 := coeffAt (pMul (pScale p.1 q₁) Q1Red) k
          let R1 := coeffAt (pScale p.1 r₁) k
          let A2 := coeffAt (pMul (pScale p.2 q₂) Q1Red) k
          let R2 := coeffAt (pScale p.2 r₂) k
          let A3 := coeffAt (pMul Q1Red (P_of p)) k
          change CommRingOps.add (CommRingOps.add (CommRingOps.add A0 R0)
              (CommRingOps.add (CommRingOps.add A1 R1) (CommRingOps.add A2 R2))) A3 =
            CommRingOps.add (CommRingOps.add (CommRingOps.add (CommRingOps.add A0 A1) A2) A3)
              (CommRingOps.add (CommRingOps.add R0 R1) R2)
          have mid : CommRingOps.add (CommRingOps.add A1 R1) (CommRingOps.add A2 R2) =
              CommRingOps.add (CommRingOps.add A1 A2) (CommRingOps.add R1 R2) := by
            rw [LawfulCommRing.add_assoc A1 R1 _,
                ← LawfulCommRing.add_assoc R1 A2 R2,
                LawfulCommRing.add_comm R1 A2,
                LawfulCommRing.add_assoc A2 R1 R2,
                ← LawfulCommRing.add_assoc A1 A2 _]
          rw [mid]
          have left2 : CommRingOps.add (CommRingOps.add A0 R0)
              (CommRingOps.add (CommRingOps.add A1 A2) (CommRingOps.add R1 R2)) =
              CommRingOps.add (CommRingOps.add (CommRingOps.add A0 A1) A2)
                (CommRingOps.add (CommRingOps.add R0 R1) R2) := by
            rw [LawfulCommRing.add_assoc A0 R0 _,
                ← LawfulCommRing.add_assoc R0 (CommRingOps.add A1 A2) _,
                LawfulCommRing.add_comm R0 (CommRingOps.add A1 A2),
                LawfulCommRing.add_assoc (CommRingOps.add A1 A2) R0 _,
                ← LawfulCommRing.add_assoc A0 (CommRingOps.add A1 A2) _,
                ← LawfulCommRing.add_assoc A0 A1 A2,
                ← LawfulCommRing.add_assoc R0 R1 R2]
          rw [left2, LawfulCommRing.add_assoc _ _ A3,
              LawfulCommRing.add_comm (CommRingOps.add (CommRingOps.add R0 R1) R2) A3,
              ← LawfulCommRing.add_assoc]
        rw [← hLHS, hRed]
      have hrCombEq : rComb = pMul Q1Red (pNeg qComb) := by
        have hsub := pSub_pAdd_cancel_left (pMul Q1Red qComb) rComb
        have hrt : trimPoly rComb = rComb := trimPoly_idem _
        rw [hSum0, hrt] at hsub
        have hpt : trimPoly (pNeg (pMul Q1Red qComb)) = pNeg (pMul Q1Red qComb) := trimPoly_idem _
        rw [← hsub, pSub_eq_pAdd_pNeg, pAdd_nil_left, hpt, ← pMul_pNeg_right]
      have hrCombNil : rComb = [] := by
        if hrNe : rComb = [] then exact hrNe
        else
          have hqNe : trimPoly (pNeg qComb) ≠ [] := by
            intro h0
            rw [← pMul_trimPoly_right Q1Red, h0, (pMul_eq_nil_iff Q1Red []).mpr (.inr rfl)] at hrCombEq
            exact hrNe hrCombEq
          rw [← pMul_trimPoly_right Q1Red] at hrCombEq
          have hlen := (pMul_length_of_trimmed_ne_nil hQ1RedTrim (trimPoly_idem _) hQ1RedNe hqNe).1
          rw [← hrCombEq] at hlen
          have hpos : 1 ≤ (trimPoly (pNeg qComb)).length := by
            cases h : trimPoly (pNeg qComb) with
            | nil => exact False.elim (hqNe h)
            | cons _ _ => simp
          omega
      have hc0 : coeffAt rComb jIdx = CommRingOps.zero := by rw [hrCombNil, coeffAt_nil]
      dsimp [rComb] at hc0
      rw [coeffAt_pAdd, coeffAt_pAdd, coeffAt_pScale p.1 r₁, coeffAt_pScale p.2 r₂,
          LawfulCommRing.add_assoc] at hc0
      exact hc0
    have hle := Nat.le_trans
      (nodup_length_le_of_subset hBadNd hSubDuet)
      (affine_duet_roots_le_card Δ₀ Δ₁ Δ₂ S hS hΔNz)
    exact Nat.le_trans hle (Nat.le_max_left _ _)

/-- **Non-Vacuous Inhabitedness Witness (`inhabited_affine_proximity_gaps`)**:
    Instantiates `welch_berlekamp_affine_proximity_gap` over `Goldilocks` with `d = 1, A = 5`,
    `D = [0, 1, 2, 3, 4, 5]` (`n = 6`, `2 * 6 + 1 + 1 = 14 < 15 = 3 * 5`), `S = [0, 1, 2, 3, 4, 5, 6]`,
    and a **strictly non-empty** exceptional list `badPairs = [(0, 1)]` (`P = 0`) where two accidental
    agreements at `z = 4` (`f(4) = -4, g(4) = 1`) and `z = 5` (`f(5) = -5, g(5) = 1`) genuinely
    defeat every `s = 1` witness (`¬ HasAffineWitnessS1`) while satisfying the proximity-gap bound! -/
theorem inhabited_affine_proximity_gaps :
    let g0 := Goldilocks.ofNat 0
    let g1 := Goldilocks.ofNat 1
    let g2 := Goldilocks.ofNat 2
    let g3 := Goldilocks.ofNat 3
    let g4 := Goldilocks.ofNat 4
    let g5 := Goldilocks.ofNat 5
    let g6 := Goldilocks.ofNat 6
    let D : List Goldilocks := [g0, g1, g2, g3, g4, g5]
    let S : List Goldilocks := [g0, g1, g2, g3, g4, g5, g6]
    let f : Goldilocks → Goldilocks := fun z =>
      if z = g4 then CommRingOps.neg g4
      else if z = g5 then CommRingOps.neg g5
      else g0
    let g : Goldilocks → Goldilocks := fun z =>
      if z = g4 ∨ z = g5 then g1 else g0
    let badPairs : List (Goldilocks × Goldilocks) := [(g0, g1)]
    0 < badPairs.length ∧
    (∀ p ∈ badPairs, ¬ HasAffineWitnessS1 1 f g D p.1 p.2 []) ∧
    badPairs.length ≤ Nat.max S.length (D.length * (D.length - 1) / 2) := by
  dsimp only
  let g0 := Goldilocks.ofNat 0
  let g1 := Goldilocks.ofNat 1
  let g2 := Goldilocks.ofNat 2
  let g3 := Goldilocks.ofNat 3
  let g4 := Goldilocks.ofNat 4
  let g5 := Goldilocks.ofNat 5
  let g6 := Goldilocks.ofNat 6
  let D : List Goldilocks := [g0, g1, g2, g3, g4, g5]
  let S : List Goldilocks := [g0, g1, g2, g3, g4, g5, g6]
  let f : Goldilocks → Goldilocks := fun z =>
    if z = g4 then CommRingOps.neg g4
    else if z = g5 then CommRingOps.neg g5
    else g0
  let g : Goldilocks → Goldilocks := fun z =>
    if z = g4 ∨ z = g5 then g1 else g0
  have hExc01 : ¬ HasAffineWitnessS1 1 f g D g0 g1 [] := by
    rintro ⟨F_poly, G_poly, _, hGLen, _, hLoss⟩
    have hGConst : ∀ x y : Goldilocks,
        RoundPoly.evalCoeffs G_poly x = RoundPoly.evalCoeffs G_poly y := by
      rcases G_poly with _ | ⟨c, _ | _⟩
      · intro _ _; rfl
      · intro _ _; simp [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero]
      · simp at hGLen
    have hSpEq : D.filter (fun z =>
        decide (RoundPoly.evalCoeffs ([] : List Goldilocks) z =
          CommRingOps.add (f z)
            (CommRingOps.mul (CommRingOps.add g0 (CommRingOps.mul g1 z)) (g z)))) = D := by
      decide
    rw [hSpEq] at hLoss
    if hc0 : RoundPoly.evalCoeffs G_poly g0 = g0 then
      have h4 : RoundPoly.evalCoeffs G_poly g4 = g0 := (hGConst g4 g0).trans hc0
      have h5 : RoundPoly.evalCoeffs G_poly g5 = g0 := (hGConst g5 g0).trans hc0
      have hg4 : g g4 = g1 := by decide
      have hg5 : g g5 = g1 := by decide
      have h10 : g0 ≠ g1 := by decide
      have hSub : ∀ z ∈ ([g4, g5] : List Goldilocks),
          z ∈ D.filter (fun w =>
            !(decide (RoundPoly.evalCoeffs F_poly w = f w) &&
              decide (RoundPoly.evalCoeffs G_poly w = g w))) := by
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · rw [List.mem_filter]; refine ⟨by decide, ?_⟩; simp [h4, hg4, h10]
        · rw [List.mem_filter]; refine ⟨by decide, ?_⟩; simp [h5, hg5, h10]
      have hge2 := nodup_length_le_of_subset (L := ([g4, g5] : List Goldilocks)) (by decide) hSub
      simp only [List.length_cons, List.length_nil] at hge2; omega
    else
      have h1 : RoundPoly.evalCoeffs G_poly g1 = RoundPoly.evalCoeffs G_poly g0 := hGConst g1 g0
      have hg0 : g g0 = g0 := by decide
      have hg1 : g g1 = g0 := by decide
      have hSub : ∀ z ∈ ([g0, g1] : List Goldilocks),
          z ∈ D.filter (fun w =>
            !(decide (RoundPoly.evalCoeffs F_poly w = f w) &&
              decide (RoundPoly.evalCoeffs G_poly w = g w))) := by
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · rw [List.mem_filter]; refine ⟨by decide, ?_⟩; simp [hg0, hc0]
        · rw [List.mem_filter]; refine ⟨by decide, ?_⟩; simp [hg1, h1, hc0]
      have hge2 := nodup_length_le_of_subset (L := ([g0, g1] : List Goldilocks)) (by decide) hSub
      simp only [List.length_cons, List.length_nil] at hge2; omega
  have hExcAll : ∀ p ∈ ([(g0, g1)] : List (Goldilocks × Goldilocks)),
      ¬ HasAffineWitnessS1 1 f g D p.1 p.2 [] := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    exact hExc01
  refine ⟨by decide, hExcAll, ?_⟩
  exact welch_berlekamp_affine_proximity_gap f g D S 1 5 [(g0, g1)] (fun _ => [])
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro p hp; simp at hp; subst hp; decide)
    (by intro _ _; simp)
    (by intro p hp; simp at hp; subst hp; decide)
    hExcAll


open RoundPoly

/-- A formally nonzero coefficient list remains nonzero after synthetic division by a root.
    This uses coefficients rather than a nonzero evaluation, so it also works over finite fields. -/
private theorem gs_all_zero_of_quotLinear {R : Type} [LawfulCommRing R] :
    ∀ (cs : List R) (r : R),
    (∀ c ∈ quotLinear cs r, c = CommRingOps.zero) →
    evalCoeffs cs r = CommRingOps.zero → ∀ c ∈ cs, c = CommRingOps.zero
  | [], _, _, _, _, hc => by cases hc
  | [a], r, _, he, c, hc => by
    have ha : a = CommRingOps.zero := by
      simpa only [evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero] using he
    exact (List.mem_singleton.mp hc).trans ha
  | a :: b :: bs, r, hq, he, c, hc => by
    have ht : evalCoeffs (b :: bs) r = CommRingOps.zero := hq _ (.head _)
    have htail := gs_all_zero_of_quotLinear (b :: bs) r
      (fun x hx => hq x (.tail _ hx)) ht
    have ha : a = CommRingOps.zero := by
      change CommRingOps.add a (CommRingOps.mul r (evalCoeffs (b :: bs) r)) = _ at he
      simpa only [ht, LawfulCommRing.mul_zero, LawfulCommRing.add_zero] using he
    cases hc with
    | head => exact ha
    | tail _ h => exact htail c h

/-- Formal root bound over any decidable integral domain. Unlike an evaluation-based nonzero
    premise, the nonzero-coefficient premise covers polynomials such as `X^q-X` over `F_q`. -/
theorem gs_formal_root_bound {R : Type} [LawfulCommRing R] [DecidableEq R] [NoZeroDivisors R] :
    ∀ (d : Nat) (cs : List R) (roots : List R),
    cs.length ≤ d + 1 → (∃ c ∈ cs, c ≠ CommRingOps.zero) →
    roots.Nodup → (∀ r ∈ roots, evalCoeffs cs r = CommRingOps.zero) → roots.length ≤ d
  | _, _, [], _, _, _, _ => Nat.zero_le _
  | 0, cs, r :: rs, hlen, hnz, _, hr => by
    cases cs with
    | nil => obtain ⟨c, hc, _⟩ := hnz; cases hc
    | cons c cs =>
      have ht : cs = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hlen; omega)
      subst cs
      have he := hr r (.head _)
      have hz : c = CommRingOps.zero := by
        simpa only [evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero] using he
      obtain ⟨a, ha, hne⟩ := hnz
      exact False.elim (hne ((List.mem_singleton.mp ha).trans hz))
  | d + 1, cs, r :: rs, hlen, hnz, hnd, hr => by
    have hroot := hr r (.head _)
    have hqnz : ∃ c ∈ quotLinear cs r, c ≠ CommRingOps.zero := by
      cases htest : (quotLinear cs r).any (fun c => decide (c ≠ CommRingOps.zero)) with
      | true =>
        obtain ⟨c, hc, he⟩ := List.any_eq_true.mp htest
        exact ⟨c, hc, of_decide_eq_true he⟩
      | false =>
        have hzero : ∀ c ∈ quotLinear cs r, c = CommRingOps.zero := by
          intro c hc
          have he := List.any_eq_false.mp htest c hc
          simpa only [decide_eq_true_eq, Decidable.not_not] using he
        obtain ⟨c, hc, hne⟩ := hnz
        exact False.elim (hne (gs_all_zero_of_quotLinear cs r hzero hroot c hc))
    have hrest : ∀ x ∈ rs, evalCoeffs (quotLinear cs r) x = CommRingOps.zero := by
      intro x hx
      have hfac := evalCoeffs_eq_mul_quotLinear_add cs r x
      rw [hr x (.tail _ hx), hroot, LawfulCommRing.add_zero] at hfac
      cases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hfac.symm with
      | inl hsub =>
        have heq := LawfulCommRing.sub_eq_zero_iff.mp hsub
        exact False.elim ((List.pairwise_cons.mp hnd).1 x hx heq.symm)
      | inr hq => exact hq
    have ih := gs_formal_root_bound d (quotLinear cs r) rs
      (by rw [quotLinear_length]; omega) hqnz (List.pairwise_cons.mp hnd).2 hrest
    simpa only [List.length_cons] using Nat.succ_le_succ ih

/-- Canonical univariate polynomials, with decidable equality on coefficient vectors. -/
abbrev GsUniPoly (F : Type) [CommRingOps F] [DecidableEq F] :=
  {p : List F // trimPoly p = p}

namespace GsUniPoly

variable {F : Type} [LawfulField F] [DecidableEq F]

/-- Canonicalize a coefficient list without any quotient representative choice. -/
def ofCoeffs (p : List F) : GsUniPoly F := ⟨trimPoly p, trimPoly_idem p⟩

instance : LawfulCommRing (GsUniPoly F) where
  zero := ⟨[], by simp [trimPoly]⟩
  one := ⟨[CommRingOps.one], by simp [trimPoly, LawfulField.one_ne_zero]⟩
  add a b := ⟨pAdd a.val b.val, by unfold pAdd; exact trimPoly_idem _⟩
  mul a b := ⟨pMul a.val b.val, by unfold pMul; exact trimPoly_idem _⟩
  neg a := ⟨pNeg a.val, by unfold pNeg; exact trimPoly_idem _⟩
  sub a b := ⟨pSub a.val b.val, by unfold pSub; exact trimPoly_idem _⟩
  add_assoc a b c := Subtype.ext (pAdd_assoc a.val b.val c.val)
  add_comm a b := Subtype.ext (pAdd_comm a.val b.val)
  zero_add a := Subtype.ext ((pAdd_nil_left a.val).trans a.property)
  add_zero a := Subtype.ext ((pAdd_nil_right a.val).trans a.property)
  add_left_neg a := by
    apply Subtype.ext
    apply eq_of_isTrimmed_coeffAt _ _ (by unfold IsTrimmed pAdd; exact trimPoly_idem _) (by simp [IsTrimmed, trimPoly])
    intro k
    rw [coeffAt_pAdd, coeffAt_pNeg, LawfulCommRing.add_left_neg, coeffAt_nil]
  sub_eq_add_neg a b := Subtype.ext (pSub_eq_pAdd_pNeg a.val b.val)
  mul_assoc a b c := Subtype.ext (pMul_assoc a.val b.val c.val)
  mul_comm a b := Subtype.ext (pMul_comm a.val b.val)
  one_mul a := Subtype.ext ((pMul_comm [CommRingOps.one] a.val).trans
    ((pMul_one_right a.val).trans a.property))
  mul_one a := Subtype.ext ((pMul_one_right a.val).trans a.property)
  left_distrib a b c := Subtype.ext (pMul_pAdd_right a.val b.val c.val)
  right_distrib a b c := Subtype.ext (pMul_pAdd_left a.val b.val c.val)

instance : NoZeroDivisors (GsUniPoly F) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b h
    have hz : pMul a.val b.val = [] := congrArg Subtype.val h
    cases (pMul_eq_nil_iff a.val b.val).mp hz with
    | inl ha => exact .inl (Subtype.ext (a.property.symm.trans ha))
    | inr hb => exact .inr (Subtype.ext (b.property.symm.trans hb))

end GsUniPoly

/-- A nonzero bivariate polynomial of Y-degree at most D has at most D distinct polynomial
    roots. Synthetic division works directly in the integral domain `F[X]`; a fraction-field
    construction is unnecessary. Equality here is formal polynomial equality, not pointwise
    equality as functions on a finite field. -/
theorem guruswami_sudan_polynomial_list_bound {F : Type} [LawfulField F] [DecidableEq F]
    (D : Nat) (Q : List (GsUniPoly F)) (polys : List (GsUniPoly F))
    (hdeg : Q.length ≤ D + 1)
    (hnz : ∃ c ∈ Q, c ≠ CommRingOps.zero)
    (hDistinct : polys.Nodup)
    (hRoots : ∀ P ∈ polys, evalCoeffs Q P = CommRingOps.zero) :
    polys.length ≤ D :=
  gs_formal_root_bound D Q polys hdeg hnz hDistinct hRoots

/-- Formal weighted-degree condition on the coefficient polynomials of `Q(X,Y)`. -/
def GsWeightedDegree {F : Type} [LawfulField F] [DecidableEq F]
    (Q : List (GsUniPoly F)) (d B : Nat) : Prop :=
  ∀ (j : Nat) (c : GsUniPoly F), Q[j]? = some c → c.val.length ≤ B - j * d

/-- Substitution of a degree-at-most-d polynomial into a bivariate polynomial of weighted
    degree below B has formal univariate degree below B, including all zero-polynomial cases. -/
theorem gs_substitution_length {F : Type} [LawfulField F] [DecidableEq F]
    (P : GsUniPoly F) (d : Nat) (hP : P.val.length ≤ d + 1) :
    ∀ (Q : List (GsUniPoly F)) (B : Nat), GsWeightedDegree Q d B →
      (evalCoeffs Q P).val.length ≤ B
  | [], _, _ => Nat.zero_le _
  | c :: cs, B, hW => by
    have hc : c.val.length ≤ B := by
      have h := hW 0 c rfl
      simpa only [Nat.zero_mul, Nat.sub_zero] using h
    have ht : GsWeightedDegree cs d (B - d) := by
      intro j a ha
      have h := hW (j + 1) a ha
      simpa only [Nat.add_mul, Nat.one_mul, Nat.sub_sub, Nat.add_comm] using h
    have hi := gs_substitution_length P d hP cs (B - d) ht
    change (pAdd c.val (pMul P.val (evalCoeffs cs P).val)).length ≤ B
    apply pAdd_length_le _ _ B hc
    if hz : B ≤ d then
      have he : (evalCoeffs cs P).val = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [he, pMul_comm]
      exact Nat.zero_le _
    else
      have hm := pMul_length_le P.val (evalCoeffs cs P).val d (B - d - 1)
        hP (by omega)
      omega

/-- Evaluation commutes with bivariate substitution. -/
theorem gs_eval_substitution {F : Type} [LawfulField F] [DecidableEq F]
    (P : GsUniPoly F) (x : F) : ∀ (Q : List (GsUniPoly F)),
    evalCoeffs (evalCoeffs Q P).val x =
      evalCoeffs (Q.map (fun c => evalCoeffs c.val x)) (evalCoeffs P.val x)
  | [] => rfl
  | c :: cs => by
    change evalCoeffs (pAdd c.val (pMul P.val (evalCoeffs cs P).val)) x = _
    rw [evalCoeffs_pAdd, evalCoeffs_pMul, gs_eval_substitution P x cs]
    rfl

/-- Sudan's multiplicity-one factor theorem, beyond the unique-decoding radius. All
    agreement points are distinct, and their number reaches the weighted-degree threshold. -/
theorem sudan_factor {F : Type} [LawfulField F] [DecidableEq F]
    (Q : List (GsUniPoly F)) (P : GsUniPoly F) (d B : Nat)
    (hP : P.val.length ≤ d + 1) (hW : GsWeightedDegree Q d B)
    (xs : List F) (ys : F → F) (hDistinct : xs.Nodup) (hCount : B ≤ xs.length)
    (hAgree : ∀ x ∈ xs, evalCoeffs P.val x = ys x)
    (hZero : ∀ x ∈ xs, evalCoeffs (Q.map (fun c => evalCoeffs c.val x)) (ys x) = CommRingOps.zero) :
    evalCoeffs Q P = CommRingOps.zero := by
  letI : NoZeroDivisors F := LawfulField.toNoZeroDivisors F
  have hlen := gs_substitution_length P d hP Q B hW
  let g := (evalCoeffs Q P).val
  have hRoots : ∀ x ∈ xs, evalCoeffs g x = CommRingOps.zero := by
    intro x hx
    rw [gs_eval_substitution, hAgree x hx]
    exact hZero x hx
  have hz : trimPoly g = [] := by
    if he : trimPoly g = [] then exact he else
      have hNonzero : ∃ c ∈ g, c ≠ CommRingOps.zero := by
        cases ht : g.any (fun c => decide (c ≠ CommRingOps.zero)) with
        | true =>
          obtain ⟨c, hc, hn⟩ := List.any_eq_true.mp ht
          exact ⟨c, hc, of_decide_eq_true hn⟩
        | false =>
          have hall : ∀ c ∈ g, c = CommRingOps.zero := by
            intro c hc
            have h := List.any_eq_false.mp ht c hc
            simpa only [decide_eq_true_eq, Decidable.not_not] using h
          have hallcoeff : ∀ k, coeffAt g k = CommRingOps.zero := by
            intro k
            unfold coeffAt
            rw [List.getD_eq_getElem?_getD]
            cases hk : g[k]? with
            | none => rfl
            | some c => exact hall c (List.mem_of_getElem? hk)
          exact False.elim (he ((trimPoly_eq_nil_iff g).mpr hallcoeff))
      have hpos : 0 < B := by
        obtain ⟨c, hc, _⟩ := hNonzero
        have := List.length_pos_of_mem hc
        change g.length ≤ B at hlen
        omega
      have hbound := gs_formal_root_bound (B - 1) g xs (by dsimp [g]; omega)
        hNonzero hDistinct hRoots
      omega
  apply Subtype.ext
  exact (evalCoeffs Q P).property.symm.trans hz

/-- Sudan factor and list bound for an arbitrary list of distinct candidate polynomials.
    Candidate-specific agreement sets need not be supplied in the protocol transcript. -/
theorem sudan_factor_and_list_bound {F : Type} [LawfulField F] [DecidableEq F]
    (Q : List (GsUniPoly F)) (polys : List (GsUniPoly F)) (d B D : Nat)
    (hQ : Q.length ≤ D + 1) (hnz : ∃ c ∈ Q, c ≠ CommRingOps.zero)
    (hW : GsWeightedDegree Q d B) (hDistinct : polys.Nodup)
    (ys : F → F)
    (hCandidates : ∀ P ∈ polys, P.val.length ≤ d + 1 ∧
      ∃ xs : List F, xs.Nodup ∧ B ≤ xs.length ∧
        (∀ x ∈ xs, evalCoeffs P.val x = ys x) ∧
        (∀ x ∈ xs, evalCoeffs (Q.map (fun c => evalCoeffs c.val x)) (ys x) = CommRingOps.zero)) :
    (∀ P ∈ polys, evalCoeffs Q P = CommRingOps.zero) ∧ polys.length ≤ D := by
  have hf : ∀ P ∈ polys, evalCoeffs Q P = CommRingOps.zero := by
    intro P hP
    obtain ⟨hdeg, xs, hxs, hcount, hagree, hzero⟩ := hCandidates P hP
    exact sudan_factor Q P d B hdeg hW xs ys hxs hcount hagree hzero
  exact ⟨hf, guruswami_sudan_polynomial_list_bound D Q polys hQ hnz hDistinct hf⟩

/-! ## Constructive bivariate Hasse interpolation -/

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

/-- Distinct monomial positions of `(1,d)`-weighted degree strictly below `B`, with Y degree ≤ D. -/
def gsMonomials (B d D : Nat) : List (Nat × Nat) :=
  (List.range (D + 1)).flatMap (fun j => (List.range (B - j * d)).map (fun i => (i, j)))

/-- Exact interpolation dimension, including empty columns. -/
def gsMonomialCount (B d D : Nat) : Nat :=
  ((List.range (D + 1)).map (fun j => B - j * d)).sum

theorem gsMonomials_length (B d D : Nat) :
    (gsMonomials B d D).length = gsMonomialCount B d D := by
  simp [gsMonomials, gsMonomialCount, List.length_flatMap]

theorem gsMonomials_weight (B d D : Nat) (e : Nat × Nat)
    (he : e ∈ gsMonomials B d D) : e.1 + e.2 * d < B ∧ e.2 ≤ D := by
  obtain ⟨j, hj, he⟩ := List.mem_flatMap.mp he
  obtain ⟨i, hi, heq⟩ := List.mem_map.mp he
  have hjlt := List.mem_range.mp hj
  have hilt := List.mem_range.mp hi
  cases heq
  exact ⟨Nat.add_lt_of_lt_sub hilt, Nat.le_of_lt_succ hjlt⟩

theorem gsMonomials_nodup (B d D : Nat) : (gsMonomials B d D).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro j _
    apply List.pairwise_map.mpr
    exact (Qsag.Constructive.nodup_range _).imp (fun h he => h (congrArg Prod.fst he))
  · apply (Qsag.Constructive.nodup_range _).imp
    intro a b hab x hx y hy heq
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hy
    exact hab (congrArg Prod.snd heq)

/-- Hasse orders of total degree strictly below `m`. -/
def gsHasseOrders : Nat → List (Nat × Nat)
  | 0 => []
  | m + 1 => (List.range (m + 1)).map (fun s => (0, s)) ++
      (gsHasseOrders m).map (fun e => (e.1 + 1, e.2))

theorem gsHasseOrders_length : ∀ m : Nat,
    2 * (gsHasseOrders m).length = m * (m + 1)
  | 0 => rfl
  | m + 1 => by
    simp only [gsHasseOrders, List.length_append, List.length_map, List.length_range,
      Nat.mul_add, gsHasseOrders_length m, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega

theorem gsHasseOrders_mem : ∀ (m : Nat) (e : Nat × Nat),
    e ∈ gsHasseOrders m ↔ e.1 + e.2 < m
  | 0, e => by simp [gsHasseOrders]
  | m + 1, (0, s) => by
    simp [gsHasseOrders, List.mem_map, List.mem_range]
  | m + 1, (r + 1, s) => by
    simp only [gsHasseOrders, List.mem_append, List.mem_map, Prod.mk.injEq,
      Nat.zero_ne_add_one, false_and, and_false, exists_false, false_or]
    constructor
    · intro h
      obtain ⟨⟨a, b⟩, he, hab⟩ := h
      have := (gsHasseOrders_mem m (a, b)).mp he
      dsimp at this
      omega
    · intro h
      exact ⟨(r, s), (gsHasseOrders_mem m (r, s)).mpr (by dsimp; omega), rfl, rfl⟩

/-- Coefficients indexed by the distinct weighted monomials. Hasse evaluation is linear in
    these coefficients and therefore exactly the row used by Gaussian elimination. -/
def gsHasseEval {F : Type} [CommRingOps F] (B d D : Nat)
    (coeffs : List F) (order : Nat × Nat) (point : F × F) : F :=
  dotVec ((gsMonomials B d D).map (fun e => gsHasseMonomial e order point)) coeffs

/-- The entire homogeneous Hasse system; each point contributes `m(m+1)/2` equations. -/
def gsInterpolationRows {F : Type} [CommRingOps F] (B d D m : Nat)
    (points : List (F × F)) : List (List F) :=
  points.flatMap (fun p => (gsHasseOrders m).map (fun order =>
    (gsMonomials B d D).map (fun e => gsHasseMonomial e order p)))

theorem gsInterpolationRows_length {F : Type} [CommRingOps F]
    (B d D m : Nat) (points : List (F × F)) :
    (gsInterpolationRows B d D m points).length = points.length * (m * (m + 1) / 2) := by
  have hc : (gsHasseOrders m).length = m * (m + 1) / 2 := by
    have := gsHasseOrders_length m
    omega
  induction points with
  | nil => simp [gsInterpolationRows]
  | cons p ps ih =>
    simp only [gsInterpolationRows, List.flatMap_cons, List.length_append, List.length_map,
      List.length_cons, Nat.add_mul, Nat.one_mul] at ih ⊢
    rw [ih, hc, Nat.add_comm]

/-- Constructive Guruswami–Sudan interpolation for arbitrary decidable fields. The returned
    coefficient vector has a nonzero coordinate and all formal Hasse derivatives of total order
    below `m` vanish at every input point. The witness is the executable Gaussian solver. -/
theorem guruswami_sudan_interpolation {F : Type} [LawfulField F] [DecidableEq F]
    (B d D m : Nat) (points : List (F × F))
    (hDim : points.length * (m * (m + 1) / 2) < gsMonomialCount B d D) :
    let coeffs := solveHomogeneous (gsMonomialCount B d D) (gsInterpolationRows B d D m points)
    coeffs.length = gsMonomialCount B d D ∧
    coeffs.any (fun c => !(decide (c = CommRingOps.zero))) = true ∧
    ∀ p ∈ points, ∀ r s, r + s < m → gsHasseEval B d D coeffs (r, s) p = CommRingOps.zero := by
  have h := gauss_nullspace_witness (gsMonomialCount B d D)
    (gsInterpolationRows B d D m points)
    (by rw [gsInterpolationRows_length]; exact hDim) (by
      intro row hr
      obtain ⟨p, _, hr⟩ := List.mem_flatMap.mp hr
      obtain ⟨order, _, rfl⟩ := List.mem_map.mp hr
      simp only [List.length_map, gsMonomials_length])
  refine ⟨h.1, h.2.1, ?_⟩
  intro p hp r s hrs
  apply h.2.2
  apply List.mem_flatMap.mpr
  refine ⟨p, hp, ?_⟩
  exact List.mem_map.mpr ⟨(r, s), (gsHasseOrders_mem m (r, s)).mpr hrs, rfl⟩

/-! ## Guruswami–Sudan factor theorem at arbitrary multiplicity -/

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

private theorem gsPow_zero_mul {R : Type} [LawfulCommRing R] (t w : R) :
    CommRingOps.mul (gsPow t 0) w = w :=
  LawfulCommRing.one_mul w

private theorem gsPow_succ_mul {R : Type} [LawfulCommRing R] (t : R) (k : Nat) (w : R) :
    CommRingOps.mul (gsPow t (k + 1)) w = CommRingOps.mul t (CommRingOps.mul (gsPow t k) w) :=
  LawfulCommRing.mul_assoc t (gsPow t k) w

private theorem gs_mul_mul_mul_comm {R : Type} [LawfulCommRing R] (a b c d : R) :
    CommRingOps.mul (CommRingOps.mul a b) (CommRingOps.mul c d) =
      CommRingOps.mul (CommRingOps.mul a c) (CommRingOps.mul b d) := by
  rw [LawfulCommRing.mul_assoc a b, ← LawfulCommRing.mul_assoc b c d,
    LawfulCommRing.mul_comm b c, LawfulCommRing.mul_assoc c b d, ← LawfulCommRing.mul_assoc a c]

/-- If the coefficient of `Y^s` is divisible by `t^(m - s)` for every `s < m`, then substituting
    `Y := t * u` gives a value divisible by `t^m`. -/
private theorem gs_low_order_divisible {R : Type} [LawfulCommRing R] (t u : R) :
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

private theorem gsLinear_trimmed {F : Type} [LawfulField F] [DecidableEq F] (a : F) :
    trimPoly [CommRingOps.neg a, CommRingOps.one] = [CommRingOps.neg a, CommRingOps.one] := by
  simp [trimPoly, LawfulField.one_ne_zero]

/-- The monic linear polynomial `X - a` as a canonical element of `F[X]`. -/
def gsLinear {F : Type} [LawfulField F] [DecidableEq F] (a : F) : GsUniPoly F :=
  ⟨[CommRingOps.neg a, CommRingOps.one], gsLinear_trimmed a⟩

/-- The constant polynomial `b` as a canonical element of `F[X]`. -/
def gsConst {F : Type} [LawfulField F] [DecidableEq F] (b : F) : GsUniPoly F :=
  GsUniPoly.ofCoeffs [b]

/-- `Q ∈ (X - a, Y - b)^m`. After the Taylor shift `Y ↦ Y - b` (coefficients
    `gsTaylor Q.length Q (gsConst b)`, the Hasse derivatives of `Q` in `Y` at `b`), the
    coefficient of `(Y - b)^s` is divisible by `(X - a)^(m - s)` for every `s < m`; equivalently
    every mixed Hasse derivative of total order below `m` vanishes at `(a, b)`. The condition
    mentions no candidate polynomial. -/
def GsMultiplicity {F : Type} [LawfulField F] [DecidableEq F]
    (Q : List (GsUniPoly F)) (m : Nat) (a b : F) : Prop :=
  ∀ s : Nat, s < m → ∃ h : GsUniPoly F,
    coeffAt (gsTaylor Q.length Q (gsConst b)) s =
      CommRingOps.mul (gsPow (gsLinear a) (m - s)) h

/-- `GsMultiplicity` is inhabited at every multiplicity by the nonzero polynomial `(X - a)^m`. -/
theorem gsMultiplicity_linear_power {F : Type} [LawfulField F] [DecidableEq F]
    (m : Nat) (a b : F) : GsMultiplicity [gsPow (gsLinear a) m] m a b := by
  unfold GsMultiplicity
  intro s _
  have hT : gsTaylor [gsPow (gsLinear a) m].length [gsPow (gsLinear a) m] (gsConst b) =
      [evalCoeffs [gsPow (gsLinear a) m] (gsConst b)] := rfl
  rw [hT]
  cases s with
  | zero =>
    refine ⟨CommRingOps.one, ?_⟩
    rw [coeffAt_cons_zero, Nat.sub_zero, LawfulCommRing.mul_one]
    simp only [evalCoeffs_cons, evalCoeffs_nil, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | succ _ =>
    refine ⟨CommRingOps.zero, ?_⟩
    rw [coeffAt_cons_succ, coeffAt_nil, LawfulCommRing.mul_zero]

private theorem gsLinear_eval {F : Type} [LawfulField F] [DecidableEq F] (a c : F) :
    evalCoeffs (gsLinear a).val c = CommRingOps.sub c a := by
  show evalCoeffs [CommRingOps.neg a, CommRingOps.one] c = CommRingOps.sub c a
  rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_comm c (CommRingOps.neg a)]
  simp only [evalCoeffs_cons, evalCoeffs_nil, LawfulCommRing.mul_zero, LawfulCommRing.add_zero,
    LawfulCommRing.mul_one]

/-- Formal factor theorem in `F[X]`: a polynomial vanishing at `a` is `(X - a)` times a
    polynomial, with the quotient produced by `polyDivMod`. -/
private theorem gsLinear_factor {F : Type} [LawfulField F] [DecidableEq F] (a : F)
    (c : GsUniPoly F) (hroot : evalCoeffs c.val a = CommRingOps.zero) :
    ∃ u : GsUniPoly F, c = CommRingOps.mul (gsLinear a) u := by
  have hLne : trimPoly [CommRingOps.neg a, CommRingOps.one] ≠ [] := by
    rw [gsLinear_trimmed]
    exact List.cons_ne_nil _ _
  have hspec := polyDivMod_spec c.val [CommRingOps.neg a, CommRingOps.one] hLne
  dsimp only at hspec
  rcases hspec with ⟨hqTrim, hrTrim, hDecomp, hrLt⟩
  rw [gsLinear_trimmed] at hrLt
  have hLeval : evalCoeffs [CommRingOps.neg a, CommRingOps.one] a = CommRingOps.zero :=
    (gsLinear_eval a a).trans (LawfulCommRing.sub_self a)
  have hEv : evalCoeffs (polyDivMod c.val [CommRingOps.neg a, CommRingOps.one]).2 a =
      CommRingOps.zero := by
    have h1 : evalCoeffs (trimPoly c.val) a = evalCoeffs _ a :=
      congrArg (fun p => evalCoeffs p a) hDecomp
    rw [evalCoeffs_trimPoly, hroot, evalCoeffs_pAdd, evalCoeffs_pMul, hLeval,
      LawfulCommRing.mul_zero, LawfulCommRing.zero_add] at h1
    exact h1.symm
  have hrNil : (polyDivMod c.val [CommRingOps.neg a, CommRingOps.one]).2 = [] := by
    cases hr : (polyDivMod c.val [CommRingOps.neg a, CommRingOps.one]).2 with
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
  exact ⟨⟨(polyDivMod c.val [CommRingOps.neg a, CommRingOps.one]).1, hqTrim⟩,
    Subtype.ext (c.property.symm.trans (hDecomp.trans
      ((trimPoly_idem (rawMul (polyDivMod c.val [CommRingOps.neg a, CommRingOps.one]).1
          [CommRingOps.neg a, CommRingOps.one])).trans
        (pMul_comm (polyDivMod c.val [CommRingOps.neg a, CommRingOps.one]).1
          [CommRingOps.neg a, CommRingOps.one]))))⟩

private theorem gsLinear_mul_cancel {F : Type} [LawfulField F] [DecidableEq F] (c : F)
    (x y : GsUniPoly F)
    (h : CommRingOps.mul (gsLinear c) x = CommRingOps.mul (gsLinear c) y) : x = y := by
  have hz : CommRingOps.mul (gsLinear c) (CommRingOps.sub x y) = CommRingOps.zero := by
    rw [LawfulCommRing.mul_sub, h, LawfulCommRing.sub_self]
  cases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hz with
  | inl hT =>
    exact absurd (show ([CommRingOps.neg c, CommRingOps.one] : List F) = [] from
      congrArg Subtype.val hT) (List.cons_ne_nil _ _)
  | inr hs => exact LawfulCommRing.sub_eq_zero_iff.mp hs

/-- Distinct linear factors are coprime: `(X - c)^k ∣ (X - a) · v` with `c ≠ a` forces
    `(X - c)^k ∣ v`. Evaluation at `c` and the formal factor theorem replace Bézout. -/
private theorem gsLinear_coprime_cancel_one {F : Type} [LawfulField F] [DecidableEq F]
    (c a : F) (hne : c ≠ a) :
    ∀ (k : Nat) (w v : GsUniPoly F),
      CommRingOps.mul (gsPow (gsLinear c) k) w = CommRingOps.mul (gsLinear a) v →
      ∃ w' : GsUniPoly F, v = CommRingOps.mul (gsPow (gsLinear c) k) w'
  | 0, _, v, _ => ⟨v, (gsPow_zero_mul (gsLinear c) v).symm⟩
  | k + 1, w, v, h => by
    letI : NoZeroDivisors F := LawfulField.toNoZeroDivisors F
    have hstep := gsPow_succ_mul (gsLinear c) k w
    have hL : evalCoeffs (CommRingOps.mul (gsPow (gsLinear c) (k + 1)) w).val c =
        CommRingOps.zero := by
      rw [hstep]
      show evalCoeffs (pMul (gsLinear c).val
        (CommRingOps.mul (gsPow (gsLinear c) k) w).val) c = CommRingOps.zero
      rw [evalCoeffs_pMul, gsLinear_eval, LawfulCommRing.sub_self, LawfulCommRing.zero_mul]
    have hR : evalCoeffs (CommRingOps.mul (gsLinear a) v).val c =
        CommRingOps.mul (CommRingOps.sub c a) (evalCoeffs v.val c) := by
      show evalCoeffs (pMul (gsLinear a).val v.val) c =
        CommRingOps.mul (CommRingOps.sub c a) (evalCoeffs v.val c)
      rw [evalCoeffs_pMul, gsLinear_eval]
    have hev : evalCoeffs (CommRingOps.mul (gsPow (gsLinear c) (k + 1)) w).val c =
        evalCoeffs (CommRingOps.mul (gsLinear a) v).val c := by rw [h]
    have hv0 : evalCoeffs v.val c = CommRingOps.zero := by
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

private theorem gsLinear_pow_coprime_cancel {F : Type} [LawfulField F] [DecidableEq F]
    (c a : F) (hne : c ≠ a) (k : Nat) :
    ∀ (e : Nat) (w v : GsUniPoly F),
      CommRingOps.mul (gsPow (gsLinear c) k) w = CommRingOps.mul (gsPow (gsLinear a) e) v →
      ∃ w' : GsUniPoly F, v = CommRingOps.mul (gsPow (gsLinear c) k) w'
  | 0, w, v, h => ⟨w, (gsPow_zero_mul (gsLinear a) v).symm.trans h.symm⟩
  | e + 1, w, v, h => by
    obtain ⟨w1, hw1⟩ := gsLinear_coprime_cancel_one c a hne k w
      (CommRingOps.mul (gsPow (gsLinear a) e) v) (h.trans (gsPow_succ_mul (gsLinear a) e v))
    exact gsLinear_pow_coprime_cancel c a hne k e w1 v hw1.symm

private theorem gsLinear_mul_length {F : Type} [LawfulField F] [DecidableEq F] (x : F)
    (h : GsUniPoly F) (hh : h.val ≠ []) :
    (CommRingOps.mul (gsLinear x) h).val.length = h.val.length + 1 ∧
      (CommRingOps.mul (gsLinear x) h).val ≠ [] := by
  have hl := pMul_length_of_trimmed_ne_nil (a := [CommRingOps.neg x, CommRingOps.one])
    (b := h.val) (gsLinear_trimmed x) h.property (List.cons_ne_nil _ _) hh
  have h2 : ([CommRingOps.neg x, CommRingOps.one] : List F).length = 2 := rfl
  rw [h2] at hl
  refine ⟨?_, hl.2⟩
  have h1 := hl.1
  show (pMul [CommRingOps.neg x, CommRingOps.one] h.val).length = h.val.length + 1
  omega

private theorem gsLinear_pow_mul_length {F : Type} [LawfulField F] [DecidableEq F] (x : F) :
    ∀ (m : Nat) (h : GsUniPoly F), h.val ≠ [] →
      (CommRingOps.mul (gsPow (gsLinear x) m) h).val.length = m + h.val.length ∧
        (CommRingOps.mul (gsPow (gsLinear x) m) h).val ≠ []
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
private theorem gs_multiplicity_length {F : Type} [LawfulField F] [DecidableEq F] (m : Nat) :
    ∀ (xs : List F) (g : GsUniPoly F), xs.Nodup → g.val ≠ [] →
      (∀ x ∈ xs, ∃ k : GsUniPoly F, g = CommRingOps.mul (gsPow (gsLinear x) m) k) →
      m * xs.length + 1 ≤ g.val.length
  | [], g, _, hg, _ => by
    cases hv : g.val with
    | nil => exact absurd hv hg
    | cons _ _ => simp
  | x :: xs, g, hnd, hg, hdiv => by
    obtain ⟨h, hh⟩ := hdiv x (.head _)
    have hhne : h.val ≠ [] := by
      intro h0
      have hzero : h = CommRingOps.zero := Subtype.ext h0
      have hg0 : g = CommRingOps.zero := by
        rw [hh, hzero]
        exact LawfulCommRing.mul_zero _
      exact hg (congrArg Subtype.val hg0)
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

/-- **Guruswami–Sudan factor theorem at arbitrary multiplicity.** Let `Q(X, Y)` have
    `(1, d)`-weighted degree below `B` and lie in `(X - x, Y - ys x)^m` at each of `A` distinct
    points `x`, with `B ≤ m * A`. Every polynomial `P` of degree at most `d` passing through
    those points satisfies `Q(X, P(X)) = 0` formally. The substitution `Y - ys x = (X - x) · u`
    turns the ideal-power hypothesis into `(X - x)^m ∣ Q(X, P(X))`; distinct linear factors are
    coprime, so the nonzero case would need more than `m * A ≥ B` coefficients. Multiplicity
    one is `sudan_factor`. -/
theorem guruswami_sudan_factor {F : Type} [LawfulField F] [DecidableEq F]
    (Q : List (GsUniPoly F)) (P : GsUniPoly F) (d B m : Nat)
    (hP : P.val.length ≤ d + 1) (hW : GsWeightedDegree Q d B)
    (xs : List F) (ys : F → F) (hDistinct : xs.Nodup) (hCount : B ≤ m * xs.length)
    (hAgree : ∀ x ∈ xs, evalCoeffs P.val x = ys x)
    (hMult : ∀ x ∈ xs, GsMultiplicity Q m x (ys x)) :
    evalCoeffs Q P = CommRingOps.zero := by
  have hlen := gs_substitution_length P d hP Q B hW
  have hdiv : ∀ x ∈ xs, ∃ k : GsUniPoly F,
      evalCoeffs Q P = CommRingOps.mul (gsPow (gsLinear x) m) k := by
    intro x hx
    have hc : evalCoeffs [ys x] x = ys x := by
      simp only [evalCoeffs_cons, evalCoeffs_nil, LawfulCommRing.mul_zero,
        LawfulCommRing.add_zero]
    have hroot : evalCoeffs (CommRingOps.sub P (gsConst (ys x))).val x = CommRingOps.zero := by
      show evalCoeffs (pSub P.val (trimPoly [ys x])) x = CommRingOps.zero
      rw [evalCoeffs_pSub, evalCoeffs_trimPoly, hAgree x hx, hc, LawfulCommRing.sub_self]
    obtain ⟨u, hu⟩ := gsLinear_factor x _ hroot
    rw [gsTaylor_eval (gsConst (ys x)) P Q.length Q (Nat.le_refl _), hu]
    exact gs_low_order_divisible (gsLinear x) u _ m (hMult x hx)
  if hz : (evalCoeffs Q P).val = [] then
    exact Subtype.ext hz
  else
    have hcl := gs_multiplicity_length m xs (evalCoeffs Q P) hDistinct hz hdiv
    exfalso
    omega

/-- Factor theorem and list bound at arbitrary multiplicity, for any list of distinct candidate
    polynomials. Candidate-specific agreement sets are existential, not transcript data. -/
theorem guruswami_sudan_factor_and_list_bound {F : Type} [LawfulField F] [DecidableEq F]
    (Q : List (GsUniPoly F)) (polys : List (GsUniPoly F)) (d B D m : Nat)
    (hQ : Q.length ≤ D + 1) (hnz : ∃ c ∈ Q, c ≠ CommRingOps.zero)
    (hW : GsWeightedDegree Q d B) (hDistinct : polys.Nodup)
    (ys : F → F)
    (hCandidates : ∀ P ∈ polys, P.val.length ≤ d + 1 ∧
      ∃ xs : List F, xs.Nodup ∧ B ≤ m * xs.length ∧
        (∀ x ∈ xs, evalCoeffs P.val x = ys x) ∧
        (∀ x ∈ xs, GsMultiplicity Q m x (ys x))) :
    (∀ P ∈ polys, evalCoeffs Q P = CommRingOps.zero) ∧ polys.length ≤ D := by
  have hf : ∀ P ∈ polys, evalCoeffs Q P = CommRingOps.zero := by
    intro P hP
    obtain ⟨hdeg, xs, hxs, hcount, hagree, hmult⟩ := hCandidates P hP
    exact guruswami_sudan_factor Q P d B m hdeg hW xs ys hxs hcount hagree hmult
  exact ⟨hf, guruswami_sudan_polynomial_list_bound D Q polys hQ hnz hDistinct hf⟩

/-- List-decoding form used by every deployed row (`B = m * A`, `D = gsDeployedYDegree`): a
    nonzero interpolant of `(1, d)`-weighted degree below `m * A` and multiplicity `m` at every
    point of the received word bounds, by its `Y`-degree, the number of distinct polynomials of
    degree at most `d` agreeing with the word on at least `A` domain points. -/
theorem guruswami_sudan_agreement_list_bound {F : Type} [LawfulField F] [DecidableEq F]
    (domain : List F) (word : F → F) (d A D m : Nat)
    (Q : List (GsUniPoly F)) (hQ : Q.length ≤ D + 1) (hnz : ∃ c ∈ Q, c ≠ CommRingOps.zero)
    (hW : GsWeightedDegree Q d (m * A))
    (hMult : ∀ x ∈ domain, GsMultiplicity Q m x (word x))
    (polys : List (GsUniPoly F)) (hDistinct : polys.Nodup)
    (hClose : ∀ P ∈ polys, P.val.length ≤ d + 1 ∧
      ∃ xs : List F, xs.Nodup ∧ A ≤ xs.length ∧
        ∀ x ∈ xs, x ∈ domain ∧ evalCoeffs P.val x = word x) :
    polys.length ≤ D := by
  refine (guruswami_sudan_factor_and_list_bound Q polys d (m * A) D m hQ hnz hW hDistinct
    word ?_).2
  intro P hP
  obtain ⟨hdeg, xs, hxs, hcount, hx⟩ := hClose P hP
  exact ⟨hdeg, xs, hxs, Nat.mul_le_mul_left m hcount, fun x h => (hx x h).2,
    fun x h => hMult x (hx x h).1⟩

/-! ## §5. Finite `Theorem 4.8 + Theorem 5.1` Witness Verifier Bound to the Deployed `Hem` WHIR Schedule -/

/-- Explicit finite witness for `[CWYZ26]` Theorem 4.8 (finite MCA bound) + Theorem 5.1 (`Eq. 5.7`
    equal-degree affine folding with linear evaluation claims across `sFolds` binary folds). -/
structure WhirAffineWitness where
  /-- Number of coset fibers of the stage oracle (`n = blowup * 2^rem`, the folded evaluation
      domain the proximity gap is applied on; `rem` = variables left after the stage's folds). -/
  n : Nat
  /-- Folded univariate degree bound `d = n / blowup + 2` (carrying the `+2` overflow monomials). -/
  d : Nat
  /-- Number of binary affine folds `s_i` executed in this WHIR stage (= agreement loss). -/
  sFolds : Nat
  /-- Agreement threshold `A` (`|S_{θ,α,β}(P)| ≥ A`). -/
  A : Nat
  /-- Intermediate persistent-agreement threshold `B` (`n * (d + 1) < B^2`, `B < A`). -/
  B : Nat
  /-- Multiplicity parameter `m ≥ 1` in `[CWYZ26]` Lemma 4.2 / Theorem 4.8. -/
  m : Nat
  /-- Total `(Y, Z)`-degree bound `D ≥ 1` of the explainer polynomial `Q(X, Y, Z)`. -/
  D : Nat
  /-- Stage query count `q_i` (distinct fibers, sampled without replacement). -/
  queries : Nat
  /-- Pure query soundness target bits (`128` classical, `256` QROM Grover pre-square-root). -/
  queryTargetBits : Nat
  deriving Repr, DecidableEq

/-- Primitive-recursive accumulator for the unknown count `∑_{j=0}^M (m A - D - d j) (D - j + 1)`
    in `[CWYZ26]` Equation `(4.5)` (`0` `WellFounded.fix`). -/
def interpUnknownsAux (mA_sub_D d D : Nat) : Nat → Nat
  | 0 => mA_sub_D * (D + 1)
  | j + 1 => interpUnknownsAux mA_sub_D d D j + (mA_sub_D - d * (j + 1)) * (D - (j + 1) + 1)

/-- Primitive-recursive accumulator for the per-point equation count
    `∑_{s=0}^K (m - s) (D - s + 1)` in `[CWYZ26]` Equation `(4.2)` / `(4.5)`. -/
def interpEquationsAux (m D : Nat) : Nat → Nat
  | 0 => m * (D + 1)
  | s + 1 => interpEquationsAux m D s + (m - (s + 1)) * (D - (s + 1) + 1)

/-- Exact ceiling `⌈a / b⌉` for `b > 0`. -/
def natCeilDiv (a b : Nat) : Nat :=
  (a + b - 1) / b

/-- Exact falling factorial `a (a - 1) ⋯ (a - k + 1)`: `affineFallingFactorial A q / affineFallingFactorial n q`
    is the exact probability that `q` DISTINCT uniformly sampled fibers (the `BTreeSet` sampling of
    `pcs.rs::sample_stage_queries`) all land inside a fixed set of `A` out of `n` fibers. -/
def affineFallingFactorial (a : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => (a - k) * affineFallingFactorial a k

theorem affineFallingFactorial_pos (a : Nat) : ∀ k : Nat, k ≤ a → 0 < affineFallingFactorial a k
  | 0, _ => Nat.zero_lt_one
  | k + 1, h => by
    show 0 < (a - k) * affineFallingFactorial a k
    exact Nat.mul_pos (by omega) (affineFallingFactorial_pos a k (by omega))

/-- Sampling without replacement never hits a fixed set more often than sampling with replacement:
    `affineFallingFactorial a k * n^k ≤ a^k * affineFallingFactorial n k` whenever `a ≤ n`. -/
theorem affineFallingFactorial_mul_pow_le (a n : Nat) (han : a ≤ n) :
    ∀ k : Nat, affineFallingFactorial a k * n ^ k ≤ a ^ k * affineFallingFactorial n k
  | 0 => Nat.le_refl _
  | k + 1 => by
    show (a - k) * affineFallingFactorial a k * n ^ (k + 1) ≤ a ^ (k + 1) * ((n - k) * affineFallingFactorial n k)
    have ih := affineFallingFactorial_mul_pow_le a n han k
    have hCross : (a - k) * n ≤ a * (n - k) := by
      if hk : k ≤ a then
        have e1 : (a - k) * n = a * n - k * n := Nat.sub_mul a k n
        have e2 : a * (n - k) = a * n - a * k := Nat.mul_sub a n k
        have h3 : a * k ≤ k * n := by
          rw [Nat.mul_comm a k]; exact Nat.mul_le_mul_left k han
        rw [e1, e2]
        exact Nat.sub_le_sub_left h3 (a * n)
      else
        have h0 : a - k = 0 := by omega
        rw [h0, Nat.zero_mul]
        exact Nat.zero_le _
    have hL : (a - k) * affineFallingFactorial a k * n ^ (k + 1) =
        ((a - k) * n) * (affineFallingFactorial a k * n ^ k) := by
      rw [Nat.pow_succ, Nat.mul_comm (n ^ k) n, Nat.mul_mul_mul_comm]
    have hR : a ^ (k + 1) * ((n - k) * affineFallingFactorial n k) =
        (a * (n - k)) * (a ^ k * affineFallingFactorial n k) := by
      rw [Nat.pow_succ, Nat.mul_comm (a ^ k) a, Nat.mul_mul_mul_comm]
    rw [hL, hR]
    exact Nat.mul_le_mul hCross ih

/-- Conservative `1/q`-scaled numerator `s_i * (ℓ + 2 ℓ₀ + 1)` for `[CWYZ26]` Theorem 4.8 + Theorem 5.1
    (`Eq. 5.7`, equal-degree affine folding **with linear claims** across `s_i` binary folds), valid
    whenever `checkWhirAffineWitness w q = true` (`nonpersCeil ≤ q` and `n(n-1)/2 ≤ q`). This is the
    quantity `loss * (list + 2 * list0 + 1)` of `affine_schedule.rs`. -/
def whirAffineStageSimpleNum (w : WhirAffineWitness) : Nat :=
  let ell := (w.n * (w.B - w.d - 1)) / (w.B * w.B - w.n * (w.d + 1))
  let ell0 := (w.n * (w.A - 1 - w.d)) / ((w.A - 1) * (w.A - 1) - w.n * w.d)
  w.sFolds * (ell + 2 * ell0 + 1)

/-- Exact `q^2`-scaled numerator from `[CWYZ26]` Theorem 4.8 (`Eq. 4.13`) + Theorem 5.1 (`Eq. 5.7`)
    across `w.sFolds` folds over a field of cardinality `q`. -/
def whirAffineStageExactNumQ2 (w : WhirAffineWitness) (q : Nat) : Nat :=
  let M := Nat.min w.D ((w.m * w.A - w.D - 1) / w.d)
  let ell := (w.n * (w.B - w.d - 1)) / (w.B * w.B - w.n * (w.d + 1))
  let ell0 := (w.n * (w.A - 1 - w.d)) / ((w.A - 1) * (w.A - 1) - w.n * w.d)
  let maxQChoose := Nat.max q (w.n * (w.n - 1) / 2)
  let nonpersCeil := w.D * w.D +
    natCeilDiv (4 * w.d * w.d * M * M * w.D * w.D * w.D * w.n * w.n)
               ((w.A - w.B) * (w.A - w.B))
  w.sFolds * (ell * maxQChoose + 2 * ell0 * q + nonpersCeil)

/-- Decidable verifier checking **every** side condition of `[CWYZ26]` Theorem 4.8 + Theorem 5.1
    exactly as stated in the paper (`m, D ≥ 1`, `M = min {D, ⌊(mA - D - 1)/d⌋} ≥ 1`) and as
    asserted by `affine_schedule.rs::finite_johnson_witnesses_cover_every_canonical_stage`, plus
    the exact `s_i`-loss distinct-fiber query soundness:
    1. `sFolds ≥ 1`, `n ≥ 2`, `d ≥ 1`, `d + 2 ≤ B < A`, `A + sFolds ≤ n`, `m ≥ 1`, `D ≥ 1`,
    2. `D + 1 + d ≤ m * A` and `M ≥ 1` (every term `m * A - D - d * j ≥ 1`, `D - j + 1 ≥ 1`
       for `j ≤ M`, so the truncated `Nat` sums equal the integer sums of Equation `(4.5)`),
    3. Exact Equation `(4.5)` interpolation dimension inequality `unknowns > n * equations`,
    4. Johnson denominator positivity `B^2 > n * (d + 1)` and `(A - 1)^2 > n * d`,
    5. Field-size domination `n * (n - 1) / 2 ≤ q` and `nonpersCeil ≤ q`,
    6. `queries ≤ n` and the EXACT hypergeometric bound
       `affineFallingFactorial (A + sFolds) queries * 2^queryTargetBits < affineFallingFactorial n queries`
       (implied by the upward-rounded dyadic check `query_error_below_2pow_minus256`; the
       with-replacement bound `((A + s)/n)^q` is strictly weaker and REJECTS the deployed table). -/
def checkWhirAffineWitness (w : WhirAffineWitness) (q : Nat) : Bool :=
  let mA := w.m * w.A
  let M := Nat.min w.D ((mA - w.D - 1) / w.d)
  let K := Nat.min (w.m - 1) M
  let unknowns := interpUnknownsAux (mA - w.D) w.d w.D M
  let eqsPerPoint := interpEquationsAux w.m w.D K
  let nonpersCeil := w.D * w.D +
    natCeilDiv (4 * w.d * w.d * M * M * w.D * w.D * w.D * w.n * w.n)
               ((w.A - w.B) * (w.A - w.B))
  decide (
    1 ≤ w.sFolds ∧
    2 ≤ w.n ∧
    1 ≤ w.d ∧
    w.d + 2 ≤ w.B ∧
    w.B < w.A ∧
    w.A + w.sFolds ≤ w.n ∧
    1 ≤ w.m ∧
    1 ≤ w.D ∧
    w.D + 1 + w.d ≤ mA ∧
    1 ≤ M ∧
    w.n * eqsPerPoint < unknowns ∧
    w.n * (w.d + 1) < w.B * w.B ∧
    w.n * w.d < (w.A - 1) * (w.A - 1) ∧
    w.n * (w.n - 1) / 2 ≤ q ∧
    nonpersCeil ≤ q ∧
    w.queries ≤ w.n ∧
    affineFallingFactorial (w.A + w.sFolds) w.queries * 2 ^ w.queryTargetBits <
      affineFallingFactorial w.n w.queries
  )

/-- **Exact-to-Simple Bound Reduction (`whirAffineStageExactNumQ2_le_simple_mul_q`)**:
    Whenever `checkWhirAffineWitness w q = true`, the exact `q^2`-scaled Theorem 4.8 + Theorem 5.1
    numerator is bounded above by `whirAffineStageSimpleNum w * q`, certifying that
    `whirAffineStageSimpleNum w / q` is a sound upper bound on `whirAffineStageExactNumQ2 w q / q^2`! -/
theorem whirAffineStageExactNumQ2_le_simple_mul_q (w : WhirAffineWitness) (q : Nat)
    (hok : checkWhirAffineWitness w q = true) :
    whirAffineStageExactNumQ2 w q ≤ whirAffineStageSimpleNum w * q := by
  unfold checkWhirAffineWitness at hok
  have hProps := of_decide_eq_true hok
  rcases hProps with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hChooseQ, hNonpersQ, _, _⟩
  unfold whirAffineStageExactNumQ2 whirAffineStageSimpleNum
  dsimp only
  have hMaxEq : Nat.max q (w.n * (w.n - 1) / 2) = q :=
    Nat.max_eq_left hChooseQ
  rw [hMaxEq, Nat.mul_assoc w.sFolds _ q]
  apply Nat.mul_le_mul_left
  rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
  exact Nat.add_le_add_left hNonpersQ _

/-! ### §5.1 Mirror of the Deployed Folding Geometry (`pcs.rs::stage_geometry`) -/

/-- Mirror of `pcs.rs::stage_geometry`: `(log₂ blowup, step_vars)` of every WHIR stage. -/
def hemStageGeometry (nv : Nat) : List (Nat × Nat) :=
  if nv ≤ 6 then
    let es := if nv ≤ 3 then 1 else 2
    [(4, nv - es)]
  else if nv ≤ 11 then
    let es := if nv ≤ 8 then 3 else 4
    let rem := nv - es
    let s0 := (rem + 1) / 2
    [(2, s0), (4, rem - s0)]
  else if nv ≤ 16 then
    let es := if nv ≤ 13 then 4 else if nv ≤ 15 then 5 else 6
    let rem := nv - es
    let s0 := Nat.min 4 (rem - 4)
    let s1 := (rem - s0) / 2
    [(2, s0), (4, s1), (6, rem - s0 - s1)]
  else if nv ≤ 20 then [(2, 5), (4, 3), (6, 4)]
  else if nv = 21 then [(2, 6), (4, 3), (6, 4)]
  else if nv = 22 then [(2, 6), (4, 4), (6, 4)]
  else [(2, 6), (4, 4), (6, 3), (8, 3)]

/-- Mirror of the `early_stop_vars` field produced by `pcs.rs::stage_geometry`. -/
def hemEarlyStopVars (nv : Nat) : Nat :=
  if nv ≤ 3 then 1 else if nv ≤ 6 then 2 else if nv ≤ 8 then 3 else if nv ≤ 13 then 4
  else if nv ≤ 15 then 5 else if nv ≤ 16 then 6 else if nv ≤ 20 then nv - 12
  else if nv = 23 then 7 else 8

/-- Mirror of `WhirSecurityRegime::minimum_queries` for the two unconditional Johnson regimes:
    `BciksJohnsonQrom128` uses `⌈512 / log₂ B⌉ + 2`, `BciksJohnsonClassical128` uses
    `⌈256 / log₂ B⌉ + 1`. -/
def hemJohnsonMinQueries (isQrom : Bool) (logBlowup : Nat) : Nat :=
  if isQrom then natCeilDiv 512 logBlowup + 2 else natCeilDiv 256 logBlowup + 1

/-- Resolved per-stage geometry: `n = blowup * 2^rem` coset fibers and folded degree bound
    `d = 2^rem + 2`, where `rem` counts the variables left AFTER this stage's `stepVars` folds
    (exactly the `n`, `d` computed inside `affine_schedule.rs`). -/
structure HemStageGeom where
  stageIdx : Nat
  logBlowup : Nat
  stepVars : Nat
  n : Nat
  d : Nat
  deriving Repr, DecidableEq

def hemStageGeomsAux : Nat → Nat → List (Nat × Nat) → List HemStageGeom
  | _, _, [] => []
  | idx, rem, (lb, sv) :: rest =>
    { stageIdx := idx, logBlowup := lb, stepVars := sv,
      n := 2 ^ lb * 2 ^ (rem - sv), d := 2 ^ (rem - sv) + 2 } ::
      hemStageGeomsAux (idx + 1) (rem - sv) rest

def hemStageGeoms (nv : Nat) : List HemStageGeom :=
  hemStageGeomsAux 0 nv (hemStageGeometry nv)

/-- Mirror of `WhirSchedule::validate` on the canonical geometry: at most `4` stages, blowups in
    `{4, 16, 64, 256}`, every stage folds `1..6` variables and strictly fewer than remain, and
    `early_stop_vars + ∑ step_vars = num_vars` with `1 ≤ early_stop_vars ≤ 8`. -/
def hemStageGeometryValid (nv : Nat) : Bool :=
  let g := hemStageGeometry nv
  decide (1 ≤ g.length ∧ g.length ≤ 4) &&
  g.all (fun p => (p.1 == 2 || p.1 == 4 || p.1 == 6 || p.1 == 8) &&
    decide (1 ≤ p.2 ∧ p.2 ≤ 6)) &&
  decide (hemEarlyStopVars nv + (g.map (·.2)).sum = nv) &&
  decide (1 ≤ hemEarlyStopVars nv ∧ hemEarlyStopVars nv ≤ 8)

/-- Every supported `num_vars ∈ 2..=24` has a schedule accepted by the `validate` mirror, and
    every stage's Johnson QROM query count fits the wire cap `NUM_PCS_QUERIES = 512`. -/
theorem hemStageGeometry_valid_and_under_query_cap :
    ∀ nv : Nat, 2 ≤ nv → nv ≤ 24 →
      hemStageGeometryValid nv = true ∧
      ∀ p ∈ hemStageGeometry nv, hemJohnsonMinQueries true p.1 ≤ 512 := by
  have hAll : ((List.range 23).all fun i =>
      hemStageGeometryValid (i + 2) &&
      (hemStageGeometry (i + 2)).all (fun p => decide (hemJohnsonMinQueries true p.1 ≤ 512))) = true := by
    decide +kernel
  intro nv h2 h24
  have h1 := List.all_eq_true.mp hAll (nv - 2) (List.mem_range.mpr (by omega))
  have hEq : nv - 2 + 2 = nv := by omega
  rw [hEq, Bool.and_eq_true] at h1
  refine ⟨h1.1, fun p hp => ?_⟩
  exact of_decide_eq_true (List.all_eq_true.mp h1.2 p hp)

/-! ### §5.2 The Deployed Witness Table (`affine_schedule.rs::WITNESSES`, Verbatim) -/

/-- VERBATIM copy of `crates/qsag-agg/src/pcs/affine_schedule.rs::WITNESSES`:
    `(num_vars, stage, A, m, D)` with `B = A - 1`, for the canonical `BciksJohnsonQrom128`
    schedule. Stages whose query count reaches the fiber count are exhaustively queried and carry
    no row. -/
def hemJohnsonQromWitnessTable : List (Nat × Nat × Nat × Nat × Nat) :=
  [ (9, 1, 127, 1, 20),
    (10, 0, 329, 1, 14),
    (10, 1, 126, 1, 20),
    (11, 0, 328, 1, 14),
    (11, 1, 126, 1, 20),
    (12, 0, 579, 4, 75),
    (12, 1, 310, 4, 59),
    (12, 2, 174, 8, 139),
    (13, 0, 1091, 8, 143),
    (13, 1, 570, 16, 351),
    (13, 2, 173, 8, 135),
    (14, 0, 2119, 32, 863),
    (14, 1, 1092, 32, 860),
    (14, 2, 308, 32, 706),
    (15, 0, 4178, 64, 2079),
    (15, 1, 1091, 32, 844),
    (15, 2, 308, 32, 706),
    (16, 0, 8296, 128, 5567),
    (16, 1, 2137, 64, 2392),
    (16, 2, 580, 64, 1921),
    (17, 0, 8295, 128, 5503),
    (17, 1, 2137, 64, 2392),
    (17, 2, 307, 32, 691),
    (18, 0, 16531, 128, 7295),
    (18, 1, 4229, 64, 3418),
    (18, 2, 579, 64, 1890),
    (19, 0, 33003, 128, 10879),
    (19, 1, 8413, 64, 5471),
    (19, 2, 1124, 32, 1305),
    (20, 0, 65948, 128, 18111),
    (20, 1, 16782, 32, 3286),
    (20, 2, 2215, 32, 2149),
    (21, 0, 65947, 128, 18047),
    (21, 1, 16782, 32, 3286),
    (21, 2, 2215, 32, 2149),
    (22, 0, 131836, 128, 32511),
    (22, 1, 16781, 32, 3270),
    (22, 2, 2215, 32, 2149),
    (23, 0, 263614, 64, 14494),
    (23, 1, 33518, 32, 5870),
    (23, 2, 8759, 16, 2733),
    (23, 3, 2254, 32, 2672),
    (24, 0, 527170, 64, 27164),
    (24, 1, 66992, 32, 11069),
    (24, 2, 17484, 16, 5228),
    (24, 3, 4482, 16, 2067) ]

def hemJohnsonQromTableRow (nv stage : Nat) : Option (Nat × Nat × Nat × Nat × Nat) :=
  hemJohnsonQromWitnessTable.find? (fun r => r.1 == nv && r.2.1 == stage)

/-- Stage is exhaustively queried (`num_queries ≥ n`): every fiber is opened, no proximity
    witness is needed (`if spec.num_queries as u128 >= n { continue; }`). -/
def hemJohnsonQromStageExhaustive (g : HemStageGeom) : Bool :=
  decide (g.n ≤ hemJohnsonMinQueries true g.logBlowup)

/-- The deployed stage witness: geometry from `hemStageGeoms`, `(A, m, D)` from the table row,
    `B = A - 1`, and the deployed QROM query count. -/
def hemJohnsonQromStageWitness (nv : Nat) (g : HemStageGeom) : Option WhirAffineWitness :=
  (hemJohnsonQromTableRow nv g.stageIdx).map (fun r =>
    { n := g.n, d := g.d, sFolds := g.stepVars, A := r.2.2.1, B := r.2.2.1 - 1,
      m := r.2.2.2.1, D := r.2.2.2.2,
      queries := hemJohnsonMinQueries true g.logBlowup, queryTargetBits := 256 })

/-- Per-stage coverage check mirroring one loop iteration of
    `finite_johnson_witnesses_cover_every_canonical_stage`: an exhaustive stage must carry no
    row; every other stage must carry a row passing `checkWhirAffineWitness` with
    `loss * (list + 2 * list0 + 1) + 1 < 2000`. -/
def hemJohnsonQromStageCovered (q nv : Nat) (g : HemStageGeom) : Bool :=
  if hemJohnsonQromStageExhaustive g = true then
    (hemJohnsonQromTableRow nv g.stageIdx).isNone
  else
    match hemJohnsonQromStageWitness nv g with
    | none => false
    | some w => checkWhirAffineWitness w q && decide (whirAffineStageSimpleNum w + 1 < 2000)

/-- Number of non-exhaustive canonical stages across `num_vars ∈ 2..=24` (the Rust `seen`). -/
def hemJohnsonQromSeenCount : Nat :=
  ((List.range 23).map (fun i =>
    ((hemStageGeoms (i + 2)).filter (fun g => !hemJohnsonQromStageExhaustive g)).length)).sum

/-- **Deployed-Table Coverage Certificate (`hem_johnson_qrom_witnesses_cover_every_canonical_stage`)**:
    Lean mirror of the Rust test `finite_johnson_witnesses_cover_every_canonical_stage`, decided
    by the kernel over `GoldilocksExt4` (`q = p^4`) on the VERBATIM deployed table:
    1. for every `num_vars ∈ 2..=24` and every stage of the canonical `BciksJohnsonQrom128`
       schedule, the stage is either exhaustively queried or carries a table row satisfying every
       `[CWYZ26]` Theorem 4.8 + Theorem 5.1 side condition, the exact distinct-fiber `< 2^-256`
       query bound, and folding numerator `+ 1 < 2000`;
    2. the number of non-exhaustive stages equals the table length (`seen == WITNESSES.len()`),
       so the table has no dead rows. -/
theorem hem_johnson_qrom_witnesses_cover_every_canonical_stage :
    (∀ nv : Nat, 2 ≤ nv → nv ≤ 24 → ∀ g ∈ hemStageGeoms nv,
      hemJohnsonQromStageCovered (goldilocksPrime ^ 4) nv g = true) ∧
    hemJohnsonQromSeenCount = hemJohnsonQromWitnessTable.length := by
  have hAll : ((List.range 23).all fun i =>
      (hemStageGeoms (i + 2)).all
        (hemJohnsonQromStageCovered (goldilocksPrime ^ 4) (i + 2))) = true := by
    decide +kernel
  refine ⟨?_, by decide +kernel⟩
  intro nv h2 h24 g hg
  have h1 := List.all_eq_true.mp hAll (nv - 2) (List.mem_range.mpr (by omega))
  have hEq : nv - 2 + 2 = nv := by omega
  rw [hEq] at h1
  exact List.all_eq_true.mp h1 g hg

/-- Stage witnesses for `Hem` WHIR at `num_vars = nv`.
    * `isQrom = true` (`BciksJohnsonQrom128`): EXACTLY the deployed rows of
      `hemJohnsonQromWitnessTable` on the deployed geometry, for every `nv`.
    * `isQrom = false` (`BciksJohnsonClassical128`, `q = (129, 65, 44, 33)`): Lean-side witnesses
      at `nv = 20` and `nv = 24` only. The Rust tree ships NO classical-regime table (the QROM rows
      do not meet the `2^-128` target at half the queries), so these rows have no Rust twin. -/
def whirAffineStageWitnesses (nv : Nat) (isQrom : Bool) : List WhirAffineWitness :=
  if isQrom then
    (hemStageGeoms nv).filterMap (fun g =>
      if hemJohnsonQromStageExhaustive g = true then none else hemJohnsonQromStageWitness nv g)
  else if nv = 20 then
    [ { n := 131072, d := 32770, sFolds := 5, A := 65884, B := 65798,
        m := 122, D := 12150, queries := 129, queryTargetBits := 128 },
      { n := 65536,  d := 4098,  sFolds := 3, A := 16734, B := 16648,
        m := 48,  D := 3072,  queries := 65, queryTargetBits := 128 },
      { n := 16384,  d := 258,   sFolds := 4, A := 2177,  B := 2148,
        m := 64,  D := 3072,  queries := 44, queryTargetBits := 128 } ]
  else if nv = 24 then
    [ { n := 1048576, d := 262146, sFolds := 6, A := 527106, B := 526403,
        m := 64,  D := 11007, queries := 129, queryTargetBits := 128 },
      { n := 262144,  d := 16386,  sFolds := 4, A := 66944,  B := 66594,
        m := 24,  D := 3200,  queries := 65, queryTargetBits := 128 },
      { n := 131072,  d := 2050,   sFolds := 3, A := 17446,  B := 17184,
        m := 12,  D := 768,   queries := 44, queryTargetBits := 128 },
      { n := 65536,   d := 258,    sFolds := 3, A := 4452,   B := 4369,
        m := 16,  D := 1536,  queries := 33, queryTargetBits := 128 } ]
  else []

/-- Columns beyond this Y degree have zero dimension at weighted budget `m*A`. -/
def gsDeployedYDegree (w : WhirAffineWitness) : Nat :=
  min w.D ((w.m * w.A - 1) / w.d)

/-- All 46 deployed rows satisfy the genuine bivariate Hasse-interpolation dimension
    inequality, including the multiplicity-one rows. This is separate from the trivariate
    affine-proximity explainer checked by `checkWhirAffineWitness`. -/
theorem hem_gs_interpolation_dimensions :
    ∀ nv : Nat, 2 ≤ nv → nv ≤ 24 → ∀ w ∈ whirAffineStageWitnesses nv true,
      w.n * (w.m * (w.m + 1) / 2) <
        gsMonomialCount (w.m * w.A) w.d (gsDeployedYDegree w) := by
  have hAll : ((List.range 23).all (fun i =>
      (whirAffineStageWitnesses (i + 2) true).all (fun w =>
        decide (w.n * (w.m * (w.m + 1) / 2) <
          gsMonomialCount (w.m * w.A) w.d (gsDeployedYDegree w))))) = true := by
    decide +kernel
  intro nv h2 h24 w hw
  have h := List.all_eq_true.mp hAll (nv - 2) (List.mem_range.mpr (by omega))
  have he : nv - 2 + 2 = nv := by omega
  rw [he] at h
  exact of_decide_eq_true (List.all_eq_true.mp h w hw)

/-- Executable interpolation witnesses at every deployed row, over any decidable field and
    any received word of the deployed length. No decoder or polynomial witness is an input. -/
theorem hem_gs_constructive_interpolation {F : Type} [LawfulField F] [DecidableEq F]
    (nv : Nat) (h2 : 2 ≤ nv) (h24 : nv ≤ 24)
    (w : WhirAffineWitness) (hw : w ∈ whirAffineStageWitnesses nv true)
    (points : List (F × F)) (hN : points.length = w.n) :
    let B := w.m * w.A
    let D := gsDeployedYDegree w
    let coeffs := solveHomogeneous (gsMonomialCount B w.d D)
      (gsInterpolationRows B w.d D w.m points)
    coeffs.length = gsMonomialCount B w.d D ∧
    coeffs.any (fun c => !(decide (c = CommRingOps.zero))) = true ∧
    ∀ p ∈ points, ∀ r s, r + s < w.m → gsHasseEval B w.d D coeffs (r, s) p = CommRingOps.zero := by
  apply guruswami_sudan_interpolation
  rw [hN]
  exact hem_gs_interpolation_dimensions nv h2 h24 w hw

/-- The `nv = 20` and `nv = 24` QROM witness lists ARE the deployed `(A, B = A - 1, m, D)` rows
    on the deployed `(n, d, s_i, q_i)` geometry (`q = (258, 130, 88, 66)`). -/
theorem whirAffineStageWitnesses_qrom_eq_deployed :
    whirAffineStageWitnesses 20 true =
      [ { n := 131072, d := 32770, sFolds := 5, A := 65948, B := 65947,
          m := 128, D := 18111, queries := 258, queryTargetBits := 256 },
        { n := 65536, d := 4098, sFolds := 3, A := 16782, B := 16781,
          m := 32, D := 3286, queries := 130, queryTargetBits := 256 },
        { n := 16384, d := 258, sFolds := 4, A := 2215, B := 2214,
          m := 32, D := 2149, queries := 88, queryTargetBits := 256 } ] ∧
    whirAffineStageWitnesses 24 true =
      [ { n := 1048576, d := 262146, sFolds := 6, A := 527170, B := 527169,
          m := 64, D := 27164, queries := 258, queryTargetBits := 256 },
        { n := 262144, d := 16386, sFolds := 4, A := 66992, B := 66991,
          m := 32, D := 11069, queries := 130, queryTargetBits := 256 },
        { n := 131072, d := 2050, sFolds := 3, A := 17484, B := 17483,
          m := 16, D := 5228, queries := 88, queryTargetBits := 256 },
        { n := 65536, d := 258, sFolds := 3, A := 4482, B := 4481,
          m := 16, D := 2067, queries := 66, queryTargetBits := 256 } ] := by
  constructor <;> decide +kernel

/-- **Kernel-Decided `Theorem 4.8 + Theorem 5.1` Soundness Certificate (`cwyz26_whir_nv20_and_nv24_all_stages_valid`)**:
    Certifies by exact kernel arithmetic (`0` floating point, `0` trust) that ALL 14 stage
    witnesses across `nv = 20` (`3` stages) and `nv = 24` (`4` stages) for both
    `BciksJohnsonClassical128` (`q = (129, 65, 44, 33)`, Lean-side rows) and `BciksJohnsonQrom128`
    (`q = (258, 130, 88, 66)`, the DEPLOYED rows) over `GoldilocksExt4` (`q = goldilocksPrime ^ 4`)
    satisfy `checkWhirAffineWitness` AND have commit-folding numerator **`< 1900`**
    (`> 245` bits of unconditional folding soundness per stage!). -/
theorem cwyz26_whir_nv20_and_nv24_all_stages_valid :
    let q := goldilocksPrime ^ 4
    (∀ w ∈ whirAffineStageWitnesses 20 false,
      checkWhirAffineWitness w q = true ∧ whirAffineStageSimpleNum w < 1900) ∧
    (∀ w ∈ whirAffineStageWitnesses 20 true,
      checkWhirAffineWitness w q = true ∧ whirAffineStageSimpleNum w < 1900) ∧
    (∀ w ∈ whirAffineStageWitnesses 24 false,
      checkWhirAffineWitness w q = true ∧ whirAffineStageSimpleNum w < 1900) ∧
    (∀ w ∈ whirAffineStageWitnesses 24 true,
      checkWhirAffineWitness w q = true ∧ whirAffineStageSimpleNum w < 1900) := by
  decide +kernel

/-- **`#tooth`: the checker is sensitive to the deployed table and to the sampling model.**
    1. Raising the deployed `nv = 24` stage-0 agreement threshold by ONE (`A = 527171`) breaks the
       exact `2^-256` distinct-fiber query bound;
    2. the superseded Lean-only row (`A = 527106, B = 526403, m = 64, D = 11007`) at the deployed
       `258` queries is NOT what Rust ships, and the deployed row fails the weaker
       with-replacement bound `((A + s)/n)^q < 2^-256` that the previous checker demanded. -/
theorem tooth_checkWhirAffineWitness_rejects_perturbed_rows :
    checkWhirAffineWitness
      { n := 1048576, d := 262146, sFolds := 6, A := 527171, B := 527170,
        m := 64, D := 27164, queries := 258, queryTargetBits := 256 }
      (goldilocksPrime ^ 4) = false ∧
    ¬ ((527170 + 6) ^ 258 * 2 ^ 256 < 1048576 ^ 258) ∧
    affineFallingFactorial (527170 + 6) 258 * 2 ^ 256 < affineFallingFactorial 1048576 258 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

end Qsag
