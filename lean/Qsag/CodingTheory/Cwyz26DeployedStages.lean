module
/-
# Qsag.CodingTheory.Cwyz26DeployedStages — the proved residual count on the deployed stages

Every non-exhaustive stage of the canonical `BciksJohnsonQrom128` schedule
(`num_vars ∈ 2..=24`) is evaluated against the hypotheses of `nonExcludedDecompBound_sliced`,
at the deployed geometry `(n, d)` and the deployed interpolation witness `(A, m, D)` of
`affine_schedule.rs::WITNESSES`, over `QuarticGoldilocks` with the whole field as challenge
set (`q = p⁴`). The persistence threshold `B` is free in the proved theorem; the table below
fixes one `B` per stage.

* `slicedParamsOk`, `slicedParamsOk_sound`: a decidable check of the numerical hypotheses and
  its consequence `AffineFoldDecompBound D S d A (Dy + slicedRest …)` for every domain of the
  stage size.
* `slicedStageTable`: `(num_vars, stage, B, bits)`; `bits` is a floor of
  `log₂ (q² / (Dy + rest))` for one binary affine fold at that stage.
* `sliced_stage_table_covers_every_canonical_stage`: every stage is exhaustively queried and
  carries no row, or carries a row that passes `slicedParamsOk` and whose bound is at most
  `q² / 2^bits` with `bits ≥ 184`.
* `sliced_stage_decomp_bound`: the resulting statement for each stage.
* `sliced_rest_exceeds_simple_budget`: on every stage `Dy + rest > 2000·q`. The bound
  `s·(ℓ + 2ℓ₀ + 1)/q < 2000/q` asserted next to the deployed table uses the nonpersistent
  constant of `[CWYZ26]` Lemma 4.7, which is not proved in this directory; the count proved
  here does not reach it on any stage.

This file does not use `hem_johnson_qrom_witnesses_cover_every_canonical_stage`. It reads the
same table and geometry mirrors and re-evaluates them. What it bounds is one binary fold
`f + (α + βX)·g` with agreement loss one. The equal-degree, linear-claim and `2^s`-ary lift
of `[CWYZ26]` Theorem 5.1, the query phase and the Fiat–Shamir analysis are outside it.
-/

public import Qsag.CodingTheory.Cwyz26JohnsonCertificate
import all Qsag.CodingTheory.Cwyz26JohnsonCertificate
import all Qsag.CodingTheory.Cwyz26AffineGap
import all Qsag.CodingTheory.GoldilocksCharacteristic
import all Qsag.CodingTheory.TrivariateGsExplainer
import all Qsag.CodingTheory.SylvesterResultant
import all Qsag.HemWhirRbrSoundness
import all Qsag.ConcreteSecurityBudget
import all Qsag.AffineProximityGaps
import all Qsag.Goldilocks

public section
namespace Qsag

set_option autoImplicit false

open CommRingOps Poly3

theorem sumTo_le_of_le (f : Nat → Nat) {a b : Nat} (h : a ≤ b) : sumTo f a ≤ sumTo f b := by
  have key : ∀ k, sumTo f a ≤ sumTo f (a + k) := by
    intro k
    induction k with
    | zero => exact Nat.le_refl _
    | succ k ih => exact Nat.le_trans ih (Nat.le_add_right _ _)
  have h2 := key (b - a)
  rwa [Nat.add_sub_cancel' h] at h2

/-- The proved residual count of `nonExcludedDecompBound_sliced`, as a function of the domain
    size `n` and the size `s` of the challenge set. -/
def slicedRest (n d A B Wx Dy s : Nat) : Nat :=
  ((n * (B - (d + 1))) / (B * B - n * (d + 1))) * Nat.max s (n * (n - 1) / 2) +
    s * ((Nat.min Dy ((Wx + Dy - 1) / d)) *
      (Dy * (n * ((Nat.min Dy ((Wx + Dy - 1) / d)) * (2 * d * Dy)) / (A - B) + 1)))

/-- The numerical hypotheses of `nonExcludedDecompBound_sliced` at `Wx = m·A - Dy`. The
    interpolation count (4.5) is checked on a truncation of its left-hand sum, which only
    drops zero terms. -/
def slicedParamsOk (n d A B m Dy : Nat) : Bool :=
  decide (1 ≤ d ∧ 1 ≤ Dy ∧ d + 1 ≤ B ∧ B < A ∧ n * (d + 1) < B * B ∧ Dy ≤ m * A ∧
    Dy < goldilocksPrime ∧
    n * sumTo (fun j => (Dy + 1 - j) * (m - 1 * j)) m <
      sumTo (fun j => (Dy + 1 - j) * (m * A - Dy - d * j))
        (Nat.min (Dy + 1) ((m * A - Dy) / d + 1)))

/-- **A passing parameter set gives the decomposition bound.** For every duplicate-free
    domain of size `n` and challenge set `S` in `QuarticGoldilocks`, at most
    `Dy + slicedRest n d A B (m·A - Dy) Dy |S|` challenges in `S × S` admit an accepted
    polynomial that does not decompose through a correlated pair. -/
theorem slicedParamsOk_sound (n d A B m Dy : Nat) (h : slicedParamsOk n d A B m Dy = true)
    (D S : List QuarticGoldilocks) (hD : D.Nodup) (hS : S.Nodup) (hn : D.length = n) :
    AffineFoldDecompBound D S d A (Dy + slicedRest n d A B (m * A - Dy) Dy S.length) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := of_decide_eq_true h
  subst hn
  have hcount : D.length * triCount 1 m Dy m < triCount d (m * A - Dy) Dy (Dy + 1) := by
    rw [triCount_eq, triCount_eq]
    exact Nat.lt_of_lt_of_le h8 (sumTo_le_of_le _ (Nat.min_le_left _ _))
  have hWA : m * A - Dy + Dy ≤ m * A := Nat.le_of_eq (Nat.sub_add_cancel h6)
  exact cwyz26_affineFoldDecompBound_of_nonExcluded D S d A m (m * A - Dy) Dy _
    (nonExcludedDecompBound_sliced D S d A B m (m * A - Dy) Dy hD hS hcount h1 h2 h3 h5 h4
      (fun k a b => QuarticGoldilocks.natCast_ne_zero k a (Nat.lt_of_le_of_lt b h7)))
    hD hS hcount hWA

/-- `(num_vars, stage, B, bits)`: one persistence threshold `B` per non-exhaustive canonical
    stage, and a floor of `log₂ (q² / (Dy + rest))` at `q = p⁴`. -/
def slicedStageTable : List (Nat × Nat × Nat × Nat) :=
  [
    (9, 1, 70, 234),
    (10, 0, 259, 235),
    (10, 1, 70, 234),
    (11, 0, 259, 235),
    (11, 1, 70, 234),
    (12, 0, 515, 224),
    (12, 1, 262, 224),
    (12, 2, 140, 219),
    (13, 0, 1027, 218),
    (13, 1, 518, 213),
    (13, 2, 140, 219),
    (14, 0, 2051, 207),
    (14, 1, 1030, 207),
    (14, 2, 268, 208),
    (15, 0, 4099, 201),
    (15, 1, 1030, 207),
    (15, 2, 268, 208),
    (16, 0, 8195, 194),
    (16, 1, 2054, 200),
    (16, 2, 524, 202),
    (17, 0, 8195, 194),
    (17, 1, 2054, 200),
    (17, 2, 268, 208),
    (18, 0, 16387, 192),
    (18, 1, 4102, 198),
    (18, 2, 524, 202),
    (19, 0, 32771, 190),
    (19, 1, 8198, 195),
    (19, 2, 1036, 204),
    (20, 0, 65539, 187),
    (20, 1, 16390, 198),
    (20, 2, 2060, 201),
    (21, 0, 65539, 187),
    (21, 1, 16390, 198),
    (21, 2, 2060, 201),
    (22, 0, 131075, 184),
    (22, 1, 16390, 198),
    (22, 2, 2060, 201),
    (23, 0, 262147, 187),
    (23, 1, 32774, 195),
    (23, 2, 8204, 201),
    (23, 3, 2072, 199),
    (24, 0, 524291, 185),
    (24, 1, 65542, 192),
    (24, 2, 16396, 198),
    (24, 3, 4120, 201) ]

def slicedStageRow (nv stage : Nat) : Option (Nat × Nat × Nat × Nat) :=
  slicedStageTable.find? (fun r => r.1 == nv && r.2.1 == stage)

/-- The bad-challenge count proved for one binary fold of a stage, at challenge-set size `q`:
    `r` is the deployed row `(num_vars, stage, A, m, D)`, `w` the row of `slicedStageTable`. -/
def slicedStageCount (q : Nat) (g : HemStageGeom) (r : Nat × Nat × Nat × Nat × Nat)
    (w : Nat × Nat × Nat × Nat) : Nat :=
  r.2.2.2.2 + slicedRest g.n g.d r.2.2.1 w.2.2.1 (r.2.2.2.1 * r.2.2.1 - r.2.2.2.2) r.2.2.2.2 q

/-- One stage: exhaustively queried with no row, or a row passing `slicedParamsOk` whose
    count is at most `q² / 2^bits` with `bits ≥ 184`. -/
def slicedStageCovered (q nv : Nat) (g : HemStageGeom) : Bool :=
  if hemJohnsonQromStageExhaustive g = true then
    (slicedStageRow nv g.stageIdx).isNone
  else
    match hemJohnsonQromTableRow nv g.stageIdx, slicedStageRow nv g.stageIdx with
    | some r, some w =>
      slicedParamsOk g.n g.d r.2.2.1 w.2.2.1 r.2.2.2.1 r.2.2.2.2 &&
        decide (slicedStageCount q g r w * 2 ^ w.2.2.2 ≤ q * q) && decide (184 ≤ w.2.2.2)
    | _, _ => false

/-- One stage: the proved count is above `2000·q`. -/
def slicedStageAboveSimpleBudget (q nv : Nat) (g : HemStageGeom) : Bool :=
  match hemJohnsonQromTableRow nv g.stageIdx, slicedStageRow nv g.stageIdx with
  | some r, some w => decide (2000 * q < slicedStageCount q g r w)
  | _, _ => hemJohnsonQromStageExhaustive g

def slicedStageSeenCount : Nat :=
  ((List.range 23).map (fun i =>
    ((hemStageGeoms (i + 2)).filter (fun g => !hemJohnsonQromStageExhaustive g)).length)).sum

/-- **Every canonical stage is covered by the proved count**, and the table has no dead rows. -/
theorem sliced_stage_table_covers_every_canonical_stage :
    (∀ nv : Nat, 2 ≤ nv → nv ≤ 24 → ∀ g ∈ hemStageGeoms nv,
      slicedStageCovered (goldilocksPrime ^ 4) nv g = true) ∧
    slicedStageSeenCount = slicedStageTable.length := by
  have hAll : ((List.range 23).all fun i =>
      (hemStageGeoms (i + 2)).all (slicedStageCovered (goldilocksPrime ^ 4) (i + 2))) = true := by
    decide +kernel
  refine ⟨?_, by decide +kernel⟩
  intro nv h2 h24 g hg
  have h1 := List.all_eq_true.mp hAll (nv - 2) (List.mem_range.mpr (by omega))
  have hEq : nv - 2 + 2 = nv := by omega
  rw [hEq] at h1
  exact List.all_eq_true.mp h1 g hg

/-- **The proved decomposition bound on a deployed stage.** A non-exhaustive canonical stage
    has a deployed row `r = (_, _, A, m, D)` and a row `w = (_, _, B, bits)` such that, on every
    duplicate-free domain of the stage size, at most `slicedStageCount |S| g r w` challenges in
    `S × S` break claim-preserving decomposition of one binary fold; at `|S| = p⁴` this is at
    most `p⁸ / 2^bits`, and `bits ≥ 184`. -/
theorem sliced_stage_decomp_bound (nv : Nat) (h2 : 2 ≤ nv) (h24 : nv ≤ 24) (g : HemStageGeom)
    (hg : g ∈ hemStageGeoms nv) (hne : hemJohnsonQromStageExhaustive g = false) :
    ∃ (r : Nat × Nat × Nat × Nat × Nat) (w : Nat × Nat × Nat × Nat),
      hemJohnsonQromTableRow nv g.stageIdx = some r ∧ slicedStageRow nv g.stageIdx = some w ∧
      (∀ D S : List QuarticGoldilocks, D.Nodup → S.Nodup → D.length = g.n →
        AffineFoldDecompBound D S g.d r.2.2.1 (slicedStageCount S.length g r w)) ∧
      slicedStageCount (goldilocksPrime ^ 4) g r w * 2 ^ w.2.2.2 ≤
        goldilocksPrime ^ 4 * goldilocksPrime ^ 4 ∧
      184 ≤ w.2.2.2 := by
  have hc := sliced_stage_table_covers_every_canonical_stage.1 nv h2 h24 g hg
  unfold slicedStageCovered at hc
  rw [hne] at hc
  simp only [Bool.false_eq_true, ↓reduceIte] at hc
  split at hc
  · next r w hr hw =>
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc
    exact ⟨r, w, hr, hw,
      fun D S hD hS hn => slicedParamsOk_sound g.n g.d r.2.2.1 w.2.2.1 r.2.2.2.1 r.2.2.2.2
        hc.1.1 D S hD hS hn,
      of_decide_eq_true hc.1.2, of_decide_eq_true hc.2⟩
  · exact absurd hc Bool.false_ne_true

/-- **The proved count does not reach the deployed simple budget.** On every canonical stage
    the count at `|S| = p⁴` exceeds `2000·p⁴`. -/
theorem sliced_rest_exceeds_simple_budget :
    ∀ nv : Nat, 2 ≤ nv → nv ≤ 24 → ∀ g ∈ hemStageGeoms nv,
      slicedStageAboveSimpleBudget (goldilocksPrime ^ 4) nv g = true := by
  have hAll : ((List.range 23).all fun i =>
      (hemStageGeoms (i + 2)).all
        (slicedStageAboveSimpleBudget (goldilocksPrime ^ 4) (i + 2))) = true := by
    decide +kernel
  intro nv h2 h24 g hg
  have h1 := List.all_eq_true.mp hAll (nv - 2) (List.mem_range.mpr (by omega))
  have hEq : nv - 2 + 2 = nv := by omega
  rw [hEq] at h1
  exact List.all_eq_true.mp h1 g hg

namespace DeployedStageTests
open JohnsonCertTests

/-- A passing parameter set on an actual domain: `|D| = 11`, `d = 1`, `A = 8`, `B = 5`. -/
theorem inhabited_slicedParamsOk :
    ∃ (n d A B m Dy : Nat) (D S : List QuarticGoldilocks),
      slicedParamsOk n d A B m Dy = true ∧ D.Nodup ∧ S.Nodup ∧ D.length = n :=
  ⟨11, 1, 8, 5, 2, 4, dom11, dom11, by decide +kernel, by decide, by decide, rfl⟩

/-- The check refuses a persistence threshold at the agreement threshold (`B = A`), and one
    below the Johnson radius (`n·(d + 1) ≥ B²`), on the deployed `(9, 1)` geometry. -/
theorem tooth_slicedParamsOk_rejects :
    slicedParamsOk 256 18 127 127 1 20 = false ∧ slicedParamsOk 256 18 127 69 1 20 = false ∧
      slicedParamsOk 256 18 127 70 1 20 = true := by
  decide +kernel

#verify_constructive sumTo_le_of_le slicedParamsOk_sound
#verify_constructive sliced_stage_table_covers_every_canonical_stage sliced_stage_decomp_bound
#verify_constructive sliced_rest_exceeds_simple_budget
#verify_constructive inhabited_slicedParamsOk tooth_slicedParamsOk_rejects
#verify_inhabited slicedParamsOk_sound inhabited_slicedParamsOk

end DeployedStageTests

end Qsag
end
