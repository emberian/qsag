module
/-
# Sliced binary and multi-fold stage budgets on the flat schedules of `nv ∈ 2..=28`

`sliced_stage_supported_budget` (`HemOpening`) and `sliced_multifold_stage_supported_budget`
(`Cwyz26EqualDegreeAndMultiFold`) are stated for `nv ≤ 24`. This module states both for
`nv ≤ 28`, the range of `pcs.rs::MAX_PCS_NUM_VARS`, over the geometry
`hemPcsHighCapStageGeoms`:

* on `2..=24` the geometry, the Johnson witness row and the persistence row are the ones of the
  two theorems above (`hemPcsHighCapStageGeoms_of_le_24`, `hemPcsHighCapTableRow_of_le_24`,
  `slicedPcsHighCapRow_of_le_24`), and the conclusions are theirs;
* on `25..=28` the geometry is the `25..=28` arm of `pcs.rs::stage_geometry`
  (`hemPcsHighCapStageGeoms_nv25` .. `hemPcsHighCapStageGeoms_nv28` list the resolved stages), the
  Johnson witness rows are `affine_schedule.rs::HIGH_CAPACITY_WITNESSES`
  (`hemPcsHighCapWitnessRows`), and the persistence thresholds are `slicedPcsHighCapTable`.

Floors. Binary bound: `183` bits on every stage (`184` up to `24` variables), so the DFM-scaled
`128`-bit conclusion holds for `Q + 1 ≤ 2^26` (`Q + 1 ≤ 2^27` up to `24` variables). Multi-fold
bound: `175` bits on every stage and `186` bits when a stage folds at most `4` variables, as in
`sliced_multifold_stage_supported_budget`; on `25..=28` the rows give `177` bits (`193` bits
when a stage folds at most `4` variables) and the DFM-scaled conclusion for `Q + 1 ≤ 2^23`.
The `183`-bit and `177`-bit floors are attained at `nv = 28`, stage `0`
(`Tests/HemHighCapSlicedBudgetTeeth`).

`nv ≥ 29` has no schedule: `hemPcsHighCapStageGeometry` is empty there, as
`pcs.rs::stage_geometry` rejects it.
-/
public import Qsag.Protocol.Aggregation.Cwyz26EqualDegreeAndMultiFold
public import Qsag.Protocol.Aggregation.HemOpening
public import Qsag.Coding.Cwyz26
import Qsag.Protocol.Aggregation.ConcreteSecurityBudget
import Qsag.Math.Counting
import Qsag.Math.Primality
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag
set_option autoImplicit false

/-! ### Bridge: defining equations awaiting the upstream export blocks

Each lemma below is appended under the same name without the `bridge_` prefix to the
`Exports for lane agg-whir-cert` block of its defining module. -/

private theorem bridge_goldilocksExt4Card_def : goldilocksExt4Card = goldilocksPrime ^ 4 := by rfl

private theorem bridge_slicedBinaryStageBound_num (g : HemStageGeom)
    (r : Nat × Nat × Nat × Nat × Nat) (w : Nat × Nat × Nat × Nat) :
    (slicedBinaryStageBound g r w).num = slicedStageCount goldilocksExt4Card g r w := slicedBinaryStageBound_num g r w

private theorem bridge_slicedBinaryStageBound_den (g : HemStageGeom)
    (r : Nat × Nat × Nat × Nat × Nat) (w : Nat × Nat × Nat × Nat) :
    (slicedBinaryStageBound g r w).den = goldilocksExt4Card * goldilocksExt4Card := slicedBinaryStageBound_den g r w

private theorem bridge_intraStepB_def (B_0 t : Nat) :
    intraStepB B_0 t = if t = 0 then B_0 else 2 ^ t * (B_0 - 2) + 3 := intraStepB_def B_0 t

private theorem bridge_slicedFourChallengeCount_def (n d A B m Dy q : Nat) :
    slicedFourChallengeCount n d A B m Dy q =
      (q * q) * (Dy + slicedRest n (d + 1) (A + 1) B (m * (A + 1) - Dy) Dy q) +
        (3 * (JohnsonBound.johnsonBound n A d * JohnsonBound.johnsonBound n A d) +
          JohnsonBound.johnsonBound n A (d + 1) * JohnsonBound.johnsonBound n A (d + 1)) *
          (q ^ 3) := slicedFourChallengeCount_def n d A B m Dy q

private theorem bridge_slicedMultiFoldStageBound_num (g : HemStageGeom)
    (r : Nat × Nat × Nat × Nat × Nat) (w : Nat × Nat × Nat × Nat) :
    (slicedMultiFoldStageBound g r w).num =
      ((List.range g.stepVars).map (fun t =>
        slicedFourChallengeCount (2 ^ t * g.n) (2 ^ t * (g.d - 2))
          (2 ^ t * (r.2.2.1 - 2) + 1) (intraStepB w.2.2.1 t) r.2.2.2.1 r.2.2.2.2
          goldilocksExt4Card)).sum := slicedMultiFoldStageBound_num g r w

private theorem bridge_slicedMultiFoldStageBound_den (g : HemStageGeom)
    (r : Nat × Nat × Nat × Nat × Nat) (w : Nat × Nat × Nat × Nat) :
    (slicedMultiFoldStageBound g r w).den = goldilocksExt4Card ^ 4 := slicedMultiFoldStageBound_den g r w

/-! ### §1. Geometry and rows -/

/-- Mirror of `pcs.rs::stage_geometry` on `2..=28`: `(log₂ blowup, step_vars)` of every WHIR
    stage. Up to `24` variables it is `hemStageGeometry`; `25..=28` are the four explicit match
    arms of `stage_geometry`. Above `MAX_PCS_NUM_VARS = 28` there is no schedule. -/
def hemPcsHighCapStageGeometry (nv : Nat) : List (Nat × Nat) :=
  if nv ≤ 24 then hemStageGeometry nv
  else if nv = 25 then [(2, 6), (4, 4), (6, 4), (8, 3)]
  else if nv = 26 then [(2, 6), (4, 5), (6, 4), (8, 3)]
  else if nv = 27 then [(2, 6), (4, 5), (6, 4), (8, 4)]
  else if nv = 28 then [(2, 6), (4, 6), (6, 4), (8, 4)]
  else []

/-- Mirror of the `early_stop_vars` field of `pcs.rs::stage_geometry` on `2..=28` (`8` on
    `25..=28`). -/
def hemPcsHighCapEarlyStopVars (nv : Nat) : Nat :=
  if nv ≤ 24 then hemEarlyStopVars nv else 8

/-- Resolved per-stage geometry on `2..=28`: `n = blowup · 2^rem` and `d = 2^rem + 2`, with `rem`
    the variables left after the stage (the `n`, `d` of `affine_schedule.rs::check_witness_row`). -/
def hemPcsHighCapStageGeoms (nv : Nat) : List HemStageGeom :=
  hemStageGeomsAux 0 nv (hemPcsHighCapStageGeometry nv)

/-- Mirror of `affine_schedule.rs::HIGH_CAPACITY_WITNESSES`: Johnson witness rows
    `(num_vars, stage, A, m, D)` of the `25..=28` schedules. -/
def hemPcsHighCapWitnessRows : List (Nat × Nat × Nat × Nat × Nat) :=
  [ (25, 0, 1054283, 128, 6353),
    (25, 1, 133941, 32, 1732),
    (25, 2, 17483, 16, 586),
    (25, 3, 4482, 16, 1049),
    (26, 0, 2108508, 128, 6359),
    (26, 1, 133940, 32, 1734),
    (26, 2, 17483, 16, 586),
    (26, 3, 4482, 16, 1049),
    (27, 0, 4216959, 128, 6361),
    (27, 1, 267837, 32, 1724),
    (27, 2, 34932, 16, 581),
    (27, 3, 4481, 16, 1056),
    (28, 0, 8433861, 128, 6362),
    (28, 1, 267836, 32, 1724),
    (28, 2, 34932, 16, 581),
    (28, 3, 4481, 16, 1056) ]

/-- Johnson witness row `(num_vars, stage, A, m, D)` used by the sliced budgets on `2..=28`: the
    `hemJohnsonQromWitnessTable` row (`affine_schedule.rs::WITNESSES`) up to `24` variables, the
    `hemPcsHighCapWitnessRows` row above. -/
def hemPcsHighCapTableRow (nv stage : Nat) : Option (Nat × Nat × Nat × Nat × Nat) :=
  if nv ≤ 24 then hemJohnsonQromTableRow nv stage
  else hemPcsHighCapWitnessRows.find? (fun r => r.1 == nv && r.2.1 == stage)

/-- `(num_vars, stage, B, bits)` for the `25..=28` schedules: the persistence threshold `B` paired
    with each `hemPcsHighCapWitnessRows` row, and the floor of `log₂ (q² / count)` of the binary
    decomposition count at `q = p⁴`. -/
def slicedPcsHighCapTable : List (Nat × Nat × Nat × Nat) :=
  [ (25, 0, 1048579, 186),
    (25, 1, 131078, 196),
    (25, 2, 16396, 204),
    (25, 3, 4120, 203),
    (26, 0, 2097155, 185),
    (26, 1, 131078, 196),
    (26, 2, 16396, 204),
    (26, 3, 4120, 203),
    (27, 0, 4194307, 184),
    (27, 1, 262150, 195),
    (27, 2, 32780, 203),
    (27, 3, 4120, 203),
    (28, 0, 8388611, 183),
    (28, 1, 262150, 195),
    (28, 2, 32780, 203),
    (28, 3, 4120, 203) ]

/-- Persistence row `(num_vars, stage, B, bits)` on `2..=28`: the `slicedStageTable` row up to
    `24` variables, the `slicedPcsHighCapTable` row above. -/
def slicedPcsHighCapRow (nv stage : Nat) : Option (Nat × Nat × Nat × Nat) :=
  if nv ≤ 24 then slicedStageRow nv stage
  else slicedPcsHighCapTable.find? (fun r => r.1 == nv && r.2.1 == stage)

theorem hemPcsHighCapStageGeometry_of_le_24 (nv : Nat) (h24 : nv ≤ 24) :
    hemPcsHighCapStageGeometry nv = hemStageGeometry nv := by
  unfold hemPcsHighCapStageGeometry
  simp only [h24, ↓reduceIte]

theorem hemPcsHighCapStageGeoms_of_le_24 (nv : Nat) (h24 : nv ≤ 24) :
    hemPcsHighCapStageGeoms nv = hemStageGeoms nv := by
  unfold hemPcsHighCapStageGeoms
  rw [hemPcsHighCapStageGeometry_of_le_24 nv h24, hemStageGeoms_def]

theorem hemPcsHighCapTableRow_of_le_24 (nv stage : Nat) (h24 : nv ≤ 24) :
    hemPcsHighCapTableRow nv stage = hemJohnsonQromTableRow nv stage := by
  unfold hemPcsHighCapTableRow
  simp only [h24, ↓reduceIte]

theorem slicedPcsHighCapRow_of_le_24 (nv stage : Nat) (h24 : nv ≤ 24) :
    slicedPcsHighCapRow nv stage = slicedStageRow nv stage := by
  unfold slicedPcsHighCapRow
  simp only [h24, ↓reduceIte]

/-- The `25..=28` arms of `pcs.rs::stage_geometry`, and no schedule above
    `MAX_PCS_NUM_VARS = 28`. -/
theorem hemPcsHighCapStageGeometry_nv25_to_28 :
    hemPcsHighCapStageGeometry 25 = [(2, 6), (4, 4), (6, 4), (8, 3)] ∧
    hemPcsHighCapStageGeometry 26 = [(2, 6), (4, 5), (6, 4), (8, 3)] ∧
    hemPcsHighCapStageGeometry 27 = [(2, 6), (4, 5), (6, 4), (8, 4)] ∧
    hemPcsHighCapStageGeometry 28 = [(2, 6), (4, 6), (6, 4), (8, 4)] ∧
    ∀ nv : Nat, 29 ≤ nv → hemPcsHighCapStageGeometry nv = [] := by
  refine ⟨by decide, by decide, by decide, by decide, fun nv h29 => ?_⟩
  unfold hemPcsHighCapStageGeometry
  have h24 : ¬ nv ≤ 24 := by omega
  have h25 : ¬ nv = 25 := by omega
  have h26 : ¬ nv = 26 := by omega
  have h27 : ¬ nv = 27 := by omega
  have h28 : ¬ nv = 28 := by omega
  simp only [h24, h25, h26, h27, h28, ↓reduceIte]

/-- Resolved stages of `pcs.rs::stage_geometry(25)`: blowups `(4, 16, 64, 256)`, step variables
    `(6, 4, 4, 3)`, `8` early-stop variables. -/
theorem hemPcsHighCapStageGeoms_nv25 :
    hemPcsHighCapStageGeoms 25 =
      [ { stageIdx := 0, logBlowup := 2, stepVars := 6, n := 2097152, d := 524290 },
        { stageIdx := 1, logBlowup := 4, stepVars := 4, n := 524288, d := 32770 },
        { stageIdx := 2, logBlowup := 6, stepVars := 4, n := 131072, d := 2050 },
        { stageIdx := 3, logBlowup := 8, stepVars := 3, n := 65536, d := 258 } ] := by
  unfold hemPcsHighCapStageGeoms
  rw [hemPcsHighCapStageGeometry_nv25_to_28.1]
  simp only [hemStageGeomsAux_cons, hemStageGeomsAux_nil]

/-- Resolved stages of `pcs.rs::stage_geometry(26)`: step variables `(6, 5, 4, 3)`. -/
theorem hemPcsHighCapStageGeoms_nv26 :
    hemPcsHighCapStageGeoms 26 =
      [ { stageIdx := 0, logBlowup := 2, stepVars := 6, n := 4194304, d := 1048578 },
        { stageIdx := 1, logBlowup := 4, stepVars := 5, n := 524288, d := 32770 },
        { stageIdx := 2, logBlowup := 6, stepVars := 4, n := 131072, d := 2050 },
        { stageIdx := 3, logBlowup := 8, stepVars := 3, n := 65536, d := 258 } ] := by
  unfold hemPcsHighCapStageGeoms
  rw [hemPcsHighCapStageGeometry_nv25_to_28.2.1]
  simp only [hemStageGeomsAux_cons, hemStageGeomsAux_nil]

/-- Resolved stages of `pcs.rs::stage_geometry(27)`: step variables `(6, 5, 4, 4)`. -/
theorem hemPcsHighCapStageGeoms_nv27 :
    hemPcsHighCapStageGeoms 27 =
      [ { stageIdx := 0, logBlowup := 2, stepVars := 6, n := 8388608, d := 2097154 },
        { stageIdx := 1, logBlowup := 4, stepVars := 5, n := 1048576, d := 65538 },
        { stageIdx := 2, logBlowup := 6, stepVars := 4, n := 262144, d := 4098 },
        { stageIdx := 3, logBlowup := 8, stepVars := 4, n := 65536, d := 258 } ] := by
  unfold hemPcsHighCapStageGeoms
  rw [hemPcsHighCapStageGeometry_nv25_to_28.2.2.1]
  simp only [hemStageGeomsAux_cons, hemStageGeomsAux_nil]

/-- Resolved stages of `pcs.rs::stage_geometry(28)`: step variables `(6, 6, 4, 4)`. -/
theorem hemPcsHighCapStageGeoms_nv28 :
    hemPcsHighCapStageGeoms 28 =
      [ { stageIdx := 0, logBlowup := 2, stepVars := 6, n := 16777216, d := 4194306 },
        { stageIdx := 1, logBlowup := 4, stepVars := 6, n := 1048576, d := 65538 },
        { stageIdx := 2, logBlowup := 6, stepVars := 4, n := 262144, d := 4098 },
        { stageIdx := 3, logBlowup := 8, stepVars := 4, n := 65536, d := 258 } ] := by
  unfold hemPcsHighCapStageGeoms
  rw [hemPcsHighCapStageGeometry_nv25_to_28.2.2.2.1]
  simp only [hemStageGeomsAux_cons, hemStageGeomsAux_nil]

/-- No stage above `MAX_PCS_NUM_VARS = 28`. -/
theorem hemPcsHighCapStageGeoms_of_ge_29 (nv : Nat) (h29 : 29 ≤ nv) :
    hemPcsHighCapStageGeoms nv = [] := by
  unfold hemPcsHighCapStageGeoms
  rw [hemPcsHighCapStageGeometry_nv25_to_28.2.2.2.2 nv h29, hemStageGeomsAux_nil]

/-- The geometric checks of `pcs.rs::WhirSchedule::validate_structural` on `25..=28`: four
    stages with blowups in `{4, 16, 64, 256}` folding `1..=6` variables each, `8` early-stop
    variables with `early_stop_vars + ∑ step_vars = num_vars`, every stage domain
    `blowup · 2^remaining` at most `2^31`, and every stage folding fewer variables than remain
    (`d = 2^rem + 2 ≥ 4`). -/
theorem hemPcsHighCap_geometry_valid_nv25_to_28 (nv : Nat) (h25 : 25 ≤ nv) (h28 : nv ≤ 28) :
    (hemPcsHighCapStageGeometry nv).length = 4 ∧
    (∀ p ∈ hemPcsHighCapStageGeometry nv,
      (p.1 = 2 ∨ p.1 = 4 ∨ p.1 = 6 ∨ p.1 = 8) ∧ 1 ≤ p.2 ∧ p.2 ≤ 6) ∧
    hemPcsHighCapEarlyStopVars nv = 8 ∧
    hemPcsHighCapEarlyStopVars nv + ((hemPcsHighCapStageGeometry nv).map (·.2)).sum = nv ∧
    ∀ g ∈ hemPcsHighCapStageGeoms nv, g.n * 2 ^ g.stepVars ≤ 2 ^ 31 ∧ 4 ≤ g.d := by
  have hcases : nv = 25 ∨ nv = 26 ∨ nv = 27 ∨ nv = 28 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · rw [hemPcsHighCapStageGeoms_nv25, hemPcsHighCapStageGeometry_nv25_to_28.1]
    exact ⟨by decide, by decide, by decide, by decide, by decide⟩
  · rw [hemPcsHighCapStageGeoms_nv26, hemPcsHighCapStageGeometry_nv25_to_28.2.1]
    exact ⟨by decide, by decide, by decide, by decide, by decide⟩
  · rw [hemPcsHighCapStageGeoms_nv27, hemPcsHighCapStageGeometry_nv25_to_28.2.2.1]
    exact ⟨by decide, by decide, by decide, by decide, by decide⟩
  · rw [hemPcsHighCapStageGeoms_nv28, hemPcsHighCapStageGeometry_nv25_to_28.2.2.2.1]
    exact ⟨by decide, by decide, by decide, by decide, by decide⟩

/-! ### §2. Kernel check of the `25..=28` rows

The upstream arithmetic (`slicedParamsOk`, `slicedRest`, `slicedFourChallengeCount`, `intraStepB`,
`hemStageGeomsAux`) is restated on local definitions the kernel can evaluate; each restatement is
proved equal to the upstream function from its exported defining equation. -/

private def geomsAuxT : Nat → Nat → List (Nat × Nat) → List HemStageGeom
  | _, _, [] => []
  | idx, rem, (lb, sv) :: rest =>
    { stageIdx := idx, logBlowup := lb, stepVars := sv,
      n := 2 ^ lb * 2 ^ (rem - sv), d := 2 ^ (rem - sv) + 2 } ::
      geomsAuxT (idx + 1) (rem - sv) rest

private theorem geomsAuxT_eq : ∀ (l : List (Nat × Nat)) (idx rem : Nat),
    geomsAuxT idx rem l = hemStageGeomsAux idx rem l
  | [], idx, rem => by rw [hemStageGeomsAux_nil]; rfl
  | (lb, sv) :: rest, idx, rem => by
    rw [hemStageGeomsAux_cons, ← geomsAuxT_eq rest (idx + 1) (rem - sv)]
    rfl

private def exhaustiveT (g : HemStageGeom) : Bool :=
  decide (g.n ≤ (512 + g.logBlowup - 1) / g.logBlowup + 2)

private theorem exhaustiveT_eq (g : HemStageGeom) :
    exhaustiveT g = hemJohnsonQromStageExhaustive g := by
  rw [hemJohnsonQromStageExhaustive_def, hemJohnsonMinQueries_def, natCeilDiv_def]
  rfl

private def restT (n d A B Wx Dy s : Nat) : Nat :=
  ((n * (B - (d + 1))) / (B * B - n * (d + 1))) * Nat.max s (n * (n - 1) / 2) +
    s * ((Nat.min Dy ((Wx + Dy - 1) / d)) *
      (Dy * (n * ((Nat.min Dy ((Wx + Dy - 1) / d)) * (2 * d * Dy)) / (A - B) + 1)))

private theorem restT_eq (n d A B Wx Dy s : Nat) :
    restT n d A B Wx Dy s = slicedRest n d A B Wx Dy s := by
  rw [slicedRest_def]; rfl

private def paramsOkT (n d A B m Dy : Nat) : Bool :=
  decide (1 ≤ d ∧ 1 ≤ Dy ∧ d + 1 ≤ B ∧ B < A ∧ n * (d + 1) < B * B ∧ Dy ≤ m * A ∧
    Dy < goldilocksPrime ∧
    n * sumTo (fun j => (Dy + 1 - j) * (m - 1 * j)) m <
      sumTo (fun j => (Dy + 1 - j) * (m * A - Dy - d * j))
        (Nat.min (Dy + 1) ((m * A - Dy) / d + 1)))

private theorem paramsOkT_eq (n d A B m Dy : Nat) :
    paramsOkT n d A B m Dy = slicedParamsOk n d A B m Dy := by
  rw [slicedParamsOk_def]; rfl

private def stepBT (B_0 t : Nat) : Nat :=
  if t = 0 then B_0 else 2 ^ t * (B_0 - 2) + 3

private theorem stepBT_eq (B_0 t : Nat) : stepBT B_0 t = intraStepB B_0 t := by
  rw [bridge_intraStepB_def]; rfl

private def fourT (n d A B m Dy q : Nat) : Nat :=
  (q * q) * (Dy + restT n (d + 1) (A + 1) B (m * (A + 1) - Dy) Dy q) +
    (3 * (((n * (A - d)) / (A * A - n * d)) * ((n * (A - d)) / (A * A - n * d))) +
      ((n * (A - (d + 1))) / (A * A - n * (d + 1))) *
        ((n * (A - (d + 1))) / (A * A - n * (d + 1)))) * (q ^ 3)

private theorem fourT_eq (n d A B m Dy q : Nat) :
    fourT n d A B m Dy q = slicedFourChallengeCount n d A B m Dy q := by
  rw [bridge_slicedFourChallengeCount_def, JohnsonBound.johnsonBound_eq,
    JohnsonBound.johnsonBound_eq, ← restT_eq]
  rfl

/-- Numerator of `slicedMultiFoldStageBound` at `q = p⁴`. -/
private def mfNumT (g : HemStageGeom) (r : Nat × Nat × Nat × Nat × Nat)
    (w : Nat × Nat × Nat × Nat) : Nat :=
  ((List.range g.stepVars).map (fun t =>
    fourT (2 ^ t * g.n) (2 ^ t * (g.d - 2)) (2 ^ t * (r.2.2.1 - 2) + 1) (stepBT w.2.2.1 t)
      r.2.2.2.1 r.2.2.2.2 (goldilocksPrime ^ 4))).sum

private theorem mfNumT_eq (g : HemStageGeom) (r : Nat × Nat × Nat × Nat × Nat)
    (w : Nat × Nat × Nat × Nat) :
    mfNumT g r w = (slicedMultiFoldStageBound g r w).num := by
  rw [bridge_slicedMultiFoldStageBound_num, bridge_goldilocksExt4Card_def]
  unfold mfNumT
  simp only [fourT_eq, stepBT_eq]

/-- Everything the two budgets need from one `25..=28` row, as one evaluable check: the stage is
    not exhaustively queried, the row passes `slicedParamsOk`, the binary count meets the row's
    own bit floor (at least `183`), every intra-stage fold passes `slicedParamsOk`, and the
    multi-fold count has `177` bits (`193` when the stage folds at most `4` variables). -/
private def rowOkT (g : HemStageGeom) (r : Nat × Nat × Nat × Nat × Nat)
    (w : Nat × Nat × Nat × Nat) : Bool :=
  !exhaustiveT g &&
  paramsOkT g.n g.d r.2.2.1 w.2.2.1 r.2.2.2.1 r.2.2.2.2 &&
  decide ((r.2.2.2.2 +
      restT g.n g.d r.2.2.1 w.2.2.1 (r.2.2.2.1 * r.2.2.1 - r.2.2.2.2) r.2.2.2.2
        (goldilocksPrime ^ 4)) * 2 ^ w.2.2.2 ≤
    goldilocksPrime ^ 4 * goldilocksPrime ^ 4) &&
  decide (183 ≤ w.2.2.2) &&
  decide (1 ≤ g.stepVars ∧ g.stepVars ≤ 6) &&
  decide (1 ≤ g.d - 2 ∧ (g.d - 2) + 3 ≤ r.2.2.1) &&
  (List.range g.stepVars).all (fun t =>
    paramsOkT (2 ^ t * g.n) (2 ^ t * (g.d - 2) + 1) (2 ^ t * (r.2.2.1 - 2) + 2)
      (stepBT w.2.2.1 t) r.2.2.2.1 r.2.2.2.2) &&
  decide (mfNumT g r w * 2 ^ 177 ≤ (goldilocksPrime ^ 4) ^ 4) &&
  decide (g.stepVars ≤ 4 → mfNumT g r w * 2 ^ 193 ≤ (goldilocksPrime ^ 4) ^ 4)

private def stageOkT (nv : Nat) (g : HemStageGeom) : Bool :=
  match hemPcsHighCapTableRow nv g.stageIdx, slicedPcsHighCapRow nv g.stageIdx with
  | some r, some w => rowOkT g r w
  | _, _ => false

set_option maxRecDepth 1000000 in
private theorem stageOkT_nv25_to_28 :
    ((List.range 4).all fun i =>
      decide ((geomsAuxT 0 (i + 25) (hemPcsHighCapStageGeometry (i + 25))).length = 4) &&
      (geomsAuxT 0 (i + 25) (hemPcsHighCapStageGeometry (i + 25))).all (stageOkT (i + 25))) =
      true := by
  decide +kernel

private theorem rowOkT_sound (g : HemStageGeom) (r : Nat × Nat × Nat × Nat × Nat)
    (w : Nat × Nat × Nat × Nat) (h : rowOkT g r w = true) :
    hemJohnsonQromStageExhaustive g = false ∧
    slicedParamsOk g.n g.d r.2.2.1 w.2.2.1 r.2.2.2.1 r.2.2.2.2 = true ∧
    atLeastBits w.2.2.2 (slicedBinaryStageBound g r w) ∧
    183 ≤ w.2.2.2 ∧
    (1 ≤ g.stepVars ∧ g.stepVars ≤ 6) ∧
    (1 ≤ g.d - 2 ∧ (g.d - 2) + 3 ≤ r.2.2.1) ∧
    (∀ t : Nat, t < g.stepVars →
      slicedParamsOk (2 ^ t * g.n) (2 ^ t * (g.d - 2) + 1)
        (2 ^ t * (r.2.2.1 - 2) + 2) (intraStepB w.2.2.1 t) r.2.2.2.1 r.2.2.2.2 = true) ∧
    atLeastBits 177 (slicedMultiFoldStageBound g r w) ∧
    (g.stepVars ≤ 4 → atLeastBits 193 (slicedMultiFoldStageBound g r w)) := by
  unfold rowOkT at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hEx, hOk⟩, hBin⟩, hBits⟩, hSv⟩, hDeg⟩, hSteps⟩, hMf⟩, hMf4⟩ := h
  rw [exhaustiveT_eq] at hEx
  rw [paramsOkT_eq] at hOk
  rw [restT_eq] at hBin
  rw [mfNumT_eq] at hMf hMf4
  have hDen : (slicedMultiFoldStageBound g r w).den = (goldilocksPrime ^ 4) ^ 4 := by
    rw [bridge_slicedMultiFoldStageBound_den, bridge_goldilocksExt4Card_def]
  refine ⟨hEx, hOk, ?_, hBits, hSv, hDeg, ?_, ?_, ?_⟩
  · show (slicedBinaryStageBound g r w).num * 2 ^ w.2.2.2 ≤ (slicedBinaryStageBound g r w).den
    rw [bridge_slicedBinaryStageBound_num, bridge_slicedBinaryStageBound_den,
      slicedStageCount_def, bridge_goldilocksExt4Card_def]
    exact hBin
  · intro t ht
    have ht' := List.all_eq_true.mp hSteps t (List.mem_range.mpr ht)
    rw [paramsOkT_eq, stepBT_eq] at ht'
    exact ht'
  · show (slicedMultiFoldStageBound g r w).num * 2 ^ 177 ≤ (slicedMultiFoldStageBound g r w).den
    rw [hDen]
    exact hMf
  · intro h4
    show (slicedMultiFoldStageBound g r w).num * 2 ^ 193 ≤ (slicedMultiFoldStageBound g r w).den
    rw [hDen]
    exact hMf4 h4

/-- The facts of `rowOkT_sound` for every stage of every `25..=28` schedule. -/
private theorem highCap_rows_nv25_to_28 (nv : Nat) (h25 : 25 ≤ nv) (h28 : nv ≤ 28) :
    (hemPcsHighCapStageGeoms nv).length = 4 ∧
    ∀ g ∈ hemPcsHighCapStageGeoms nv,
      ∃ (r : Nat × Nat × Nat × Nat × Nat) (w : Nat × Nat × Nat × Nat),
        hemPcsHighCapTableRow nv g.stageIdx = some r ∧
        slicedPcsHighCapRow nv g.stageIdx = some w ∧
        rowOkT g r w = true := by
  have h1 := List.all_eq_true.mp stageOkT_nv25_to_28 (nv - 25) (List.mem_range.mpr (by omega))
  have hEq : nv - 25 + 25 = nv := by omega
  rw [hEq, Bool.and_eq_true, geomsAuxT_eq] at h1
  refine ⟨of_decide_eq_true h1.1, fun g hg => ?_⟩
  have h2 := List.all_eq_true.mp h1.2 g hg
  unfold stageOkT at h2
  split at h2
  · next r w hr hw => exact ⟨r, w, hr, hw, h2⟩
  · exact absurd h2 Bool.false_ne_true

/-! ### §3. Budgets -/

/-- Every `25..=28` schedule has four stages and none of them is exhaustively queried, so the
    non-exhaustiveness premise of the budgets below holds on every stage above `24` variables. -/
theorem highCap_stages_nonexhaustive (nv : Nat) (h25 : 25 ≤ nv) (h28 : nv ≤ 28) :
    (hemPcsHighCapStageGeoms nv).length = 4 ∧
    ∀ g ∈ hemPcsHighCapStageGeoms nv, hemJohnsonQromStageExhaustive g = false := by
  obtain ⟨hLen, hRows⟩ := highCap_rows_nv25_to_28 nv h25 h28
  refine ⟨hLen, fun g hg => ?_⟩
  obtain ⟨r, w, _, _, hOk⟩ := hRows g hg
  exact (rowOkT_sound g r w hOk).1

/-- Pure arithmetic: a bound with `128 + 2 (k + 1)` bits tolerates `Q + 1 ≤ 2^k` under the DFM
    round scale `(2 Q + 1)²`. It does not assert that DFM applies to any protocol execution. -/
theorem dfmRoundScale_clears_128bits_of_bits (b : RatBound) (k : Nat)
    (hb : atLeastBits (128 + (k + 1) * 2) b) (Q : Nat) (hQ : Q + 1 ≤ 2 ^ k) :
    atLeastBits 128 (dfmRoundScale Q b) := by
  have hbase : 2 * Q + 1 ≤ 2 ^ (k + 1) := by
    have h1 : 2 * Q + 1 ≤ 2 * (Q + 1) := by omega
    have h2 : 2 * (Q + 1) ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 hQ
    have h3 : 2 * 2 ^ k = 2 ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [← h3]
    exact Nat.le_trans h1 h2
  have hScale : (2 * Q + 1) ^ 2 ≤ 2 ^ ((k + 1) * 2) := by
    rw [Nat.pow_mul]
    exact Nat.pow_le_pow_left hbase 2
  show (2 * Q + 1) ^ 2 * b.num * 2 ^ 128 ≤ b.den
  have h := Nat.mul_le_mul_right (b.num * 2 ^ 128) hScale
  have he : 2 ^ ((k + 1) * 2) * (b.num * 2 ^ 128) = b.num * 2 ^ (128 + (k + 1) * 2) := by
    rw [Nat.pow_add, Nat.mul_left_comm]
    exact congrArg (b.num * ·) (Nat.mul_comm _ _)
  rw [Nat.mul_assoc]
  have hb' : 2 ^ ((k + 1) * 2) * (b.num * 2 ^ 128) ≤ b.den := by
    rw [he]
    exact hb
  exact Nat.le_trans h hb'

/-- Bit floors are monotone: a bound with `b` bits has `a` bits for every `a ≤ b`. -/
private theorem atLeastBits_weaken {a b : Nat} (hab : a ≤ b) (x : RatBound)
    (hx : atLeastBits b x) : atLeastBits a x :=
  Nat.le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hab)) hx

/-- **Binary sliced budget on `nv ∈ 2..=28`** (the range of `pcs.rs::MAX_PCS_NUM_VARS`). Every
    non-exhaustive stage of `pcs.rs::stage_geometry` has a Johnson witness row and a persistence
    row with a proved binary decomposition count and a `183`-bit rational budget (`184` bits up to
    `24` variables; on `25..=28` also the row's own `bits` entry). The DFM-scaled budget clears
    `128` bits for `Q + 1 ≤ 2^26` (`Q + 1 ≤ 2^27` up to `24` variables). As in
    `sliced_stage_supported_budget`, the DFM conclusions are arithmetic and assert no QROM
    experiment reduction. -/
theorem highCap_sliced_stage_supported_budget (nv : Nat) (h2 : 2 ≤ nv) (h28 : nv ≤ 28)
    (g : HemStageGeom) (hg : g ∈ hemPcsHighCapStageGeoms nv)
    (hne : hemJohnsonQromStageExhaustive g = false) :
    ∃ (r : Nat × Nat × Nat × Nat × Nat) (w : Nat × Nat × Nat × Nat),
      hemPcsHighCapTableRow nv g.stageIdx = some r ∧
      slicedPcsHighCapRow nv g.stageIdx = some w ∧
      (∀ D S : List QuarticGoldilocks, D.Nodup → S.Nodup → D.length = g.n →
        AffineFoldDecompBound D S g.d r.2.2.1 (slicedStageCount S.length g r w)) ∧
      atLeastBits 183 (slicedBinaryStageBound g r w) ∧
      (nv ≤ 24 → atLeastBits 184 (slicedBinaryStageBound g r w)) ∧
      (25 ≤ nv → atLeastBits w.2.2.2 (slicedBinaryStageBound g r w)) ∧
      (∀ Q : Nat, Q + 1 ≤ 2 ^ 26 →
        atLeastBits 128 (dfmRoundScale Q (slicedBinaryStageBound g r w))) ∧
      (nv ≤ 24 → ∀ Q : Nat, Q + 1 ≤ 2 ^ 27 →
        atLeastBits 128 (dfmRoundScale Q (slicedBinaryStageBound g r w))) := by
  cases Nat.lt_or_ge 24 nv with
  | inr h24 =>
    rw [hemPcsHighCapStageGeoms_of_le_24 nv h24] at hg
    obtain ⟨r, w, hr, hw, hd, hb184, hDfm⟩ := sliced_stage_supported_budget nv h2 h24 g hg hne
    have hb183 : atLeastBits 183 (slicedBinaryStageBound g r w) :=
      atLeastBits_weaken (by decide) _ hb184
    exact ⟨r, w, (hemPcsHighCapTableRow_of_le_24 nv _ h24).trans hr,
      (slicedPcsHighCapRow_of_le_24 nv _ h24).trans hw, hd, hb183, fun _ => hb184,
      fun h25 => absurd h24 (Nat.not_le_of_gt h25),
      fun Q hQ => dfmRoundScale_clears_128bits_of_bits _ 26
        (atLeastBits_weaken (by decide) _ hb183) Q hQ,
      fun _ => hDfm⟩
  | inl h25 =>
    obtain ⟨r, w, hr, hw, hOk⟩ := (highCap_rows_nv25_to_28 nv h25 h28).2 g hg
    obtain ⟨_, hParams, hRowBits, hBits, _⟩ := rowOkT_sound g r w hOk
    have hb183 : atLeastBits 183 (slicedBinaryStageBound g r w) :=
      atLeastBits_weaken hBits _ hRowBits
    refine ⟨r, w, hr, hw, fun D S hD hS hn => ?_, hb183,
      fun h24 => absurd h24 (Nat.not_le_of_gt h25), fun _ => hRowBits,
      fun Q hQ => dfmRoundScale_clears_128bits_of_bits _ 26
        (atLeastBits_weaken (by decide) _ hb183) Q hQ,
      fun h24 => absurd h24 (Nat.not_le_of_gt h25)⟩
    rw [slicedStageCount_def]
    exact slicedParamsOk_sound g.n g.d r.2.2.1 w.2.2.1 r.2.2.2.1 r.2.2.2.2 hParams D S hD hS hn

/-- The intra-stage fold check of `slicedStageMultiFoldCovered` on the `25..=28` rows, at the
    floors those rows meet: `177` bits, and `193` bits when the stage folds at most `4`
    variables. -/
def slicedPcsHighCapStageMultiFoldCovered (nv : Nat) (g : HemStageGeom) : Bool :=
  match hemPcsHighCapTableRow nv g.stageIdx, slicedPcsHighCapRow nv g.stageIdx with
  | some r, some w =>
    decide (1 ≤ g.stepVars ∧ g.stepVars ≤ 6) &&
    decide (1 ≤ g.d - 2 ∧ (g.d - 2) + 3 ≤ r.2.2.1) &&
    (List.range g.stepVars).all (fun t =>
      slicedParamsOk (2 ^ t * g.n) (2 ^ t * (g.d - 2) + 1)
        (2 ^ t * (r.2.2.1 - 2) + 2) (intraStepB w.2.2.1 t) r.2.2.2.1 r.2.2.2.2) &&
    decide (atLeastBits 177 (slicedMultiFoldStageBound g r w)) &&
    decide (g.stepVars ≤ 4 → atLeastBits 193 (slicedMultiFoldStageBound g r w))
  | _, _ => false

/-- Every stage of every `25..=28` schedule passes the intra-stage fold check. -/
theorem slicedPcsHighCap_multifold_covers_nv25_to_28 (nv : Nat) (h25 : 25 ≤ nv) (h28 : nv ≤ 28)
    (g : HemStageGeom) (hg : g ∈ hemPcsHighCapStageGeoms nv) :
    slicedPcsHighCapStageMultiFoldCovered nv g = true := by
  obtain ⟨r, w, hr, hw, hOk⟩ := (highCap_rows_nv25_to_28 nv h25 h28).2 g hg
  obtain ⟨_, _, _, _, hSv, hDeg, hSteps, hMf, hMf4⟩ := rowOkT_sound g r w hOk
  unfold slicedPcsHighCapStageMultiFoldCovered
  rw [hr, hw]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  exact ⟨⟨⟨⟨hSv, hDeg⟩, hSteps⟩, hMf⟩, hMf4⟩

/-- **Multi-fold sliced budget on `nv ∈ 2..=28`** (the range of `pcs.rs::MAX_PCS_NUM_VARS`).
    Every non-exhaustive stage of `pcs.rs::stage_geometry` satisfies `slicedParamsOk` at every
    intermediate binary fold step `t < g.stepVars`; the summed `k`-fold error has `≥ 175` bits,
    and `≥ 186` bits when `g.stepVars ≤ 4`, the floors of
    `sliced_multifold_stage_supported_budget`; on `25..=28` it has `≥ 177` bits, and `≥ 193` bits
    when `g.stepVars ≤ 4`. The DFM-scaled budget clears `128` bits for `Q + 1 ≤ 2^22`, and for
    `Q + 1 ≤ 2^23` on `25..=28`. -/
theorem highCap_sliced_multifold_stage_supported_budget
    (nv : Nat) (h2 : 2 ≤ nv) (h28 : nv ≤ 28)
    (g : HemStageGeom) (hg : g ∈ hemPcsHighCapStageGeoms nv)
    (hne : hemJohnsonQromStageExhaustive g = false) :
    ∃ (r : Nat × Nat × Nat × Nat × Nat) (w : Nat × Nat × Nat × Nat),
      hemPcsHighCapTableRow nv g.stageIdx = some r ∧
      slicedPcsHighCapRow nv g.stageIdx = some w ∧
      (1 ≤ g.stepVars ∧ g.stepVars ≤ 6) ∧
      (1 ≤ g.d - 2 ∧ (g.d - 2) + 3 ≤ r.2.2.1) ∧
      (∀ t : Nat, t < g.stepVars →
        slicedParamsOk (2 ^ t * g.n) (2 ^ t * (g.d - 2) + 1)
          (2 ^ t * (r.2.2.1 - 2) + 2) (intraStepB w.2.2.1 t) r.2.2.2.1 r.2.2.2.2 = true) ∧
      atLeastBits 175 (slicedMultiFoldStageBound g r w) ∧
      (25 ≤ nv → atLeastBits 177 (slicedMultiFoldStageBound g r w)) ∧
      (g.stepVars ≤ 4 → atLeastBits 186 (slicedMultiFoldStageBound g r w)) ∧
      (25 ≤ nv → g.stepVars ≤ 4 → atLeastBits 193 (slicedMultiFoldStageBound g r w)) ∧
      (∀ Q : Nat, Q + 1 ≤ 2 ^ 22 →
        atLeastBits 128 (dfmRoundScale Q (slicedMultiFoldStageBound g r w))) ∧
      (25 ≤ nv → ∀ Q : Nat, Q + 1 ≤ 2 ^ 23 →
        atLeastBits 128 (dfmRoundScale Q (slicedMultiFoldStageBound g r w))) := by
  cases Nat.lt_or_ge 24 nv with
  | inr h24 =>
    rw [hemPcsHighCapStageGeoms_of_le_24 nv h24] at hg
    obtain ⟨r, w, hr, hw, hSv, hDeg, hSteps, hb175, hb186, hDfm⟩ :=
      sliced_multifold_stage_supported_budget nv h2 h24 g hg hne
    exact ⟨r, w, (hemPcsHighCapTableRow_of_le_24 nv _ h24).trans hr,
      (slicedPcsHighCapRow_of_le_24 nv _ h24).trans hw, hSv, hDeg, hSteps, hb175,
      fun h25 => absurd h24 (Nat.not_le_of_gt h25), hb186,
      fun h25 => absurd h24 (Nat.not_le_of_gt h25), hDfm,
      fun h25 => absurd h24 (Nat.not_le_of_gt h25)⟩
  | inl h25 =>
    obtain ⟨r, w, hr, hw, hOk⟩ := (highCap_rows_nv25_to_28 nv h25 h28).2 g hg
    obtain ⟨_, _, _, _, hSv, hDeg, hSteps, hb177, hb193⟩ := rowOkT_sound g r w hOk
    have hb175 : atLeastBits 175 (slicedMultiFoldStageBound g r w) :=
      atLeastBits_weaken (by decide) _ hb177
    exact ⟨r, w, hr, hw, hSv, hDeg, hSteps, hb175, fun _ => hb177,
      fun h4 => atLeastBits_weaken (by decide) _ (hb193 h4), fun _ => hb193,
      fun Q hQ => dfm175_budget_at_2pow22 _ hb175 Q hQ,
      fun _ Q hQ => dfmRoundScale_clears_128bits_of_bits _ 23
        (atLeastBits_weaken (by decide) _ hb177) Q hQ⟩

#verify_constructive
  Qsag.hemPcsHighCapStageGeometry_of_le_24
  Qsag.hemPcsHighCapStageGeoms_of_le_24
  Qsag.hemPcsHighCapTableRow_of_le_24
  Qsag.slicedPcsHighCapRow_of_le_24
  Qsag.hemPcsHighCapStageGeometry_nv25_to_28
  Qsag.hemPcsHighCapStageGeoms_nv25
  Qsag.hemPcsHighCapStageGeoms_nv26
  Qsag.hemPcsHighCapStageGeoms_nv27
  Qsag.hemPcsHighCapStageGeoms_nv28
  Qsag.hemPcsHighCapStageGeoms_of_ge_29
  Qsag.hemPcsHighCap_geometry_valid_nv25_to_28
  Qsag.highCap_stages_nonexhaustive
  Qsag.dfmRoundScale_clears_128bits_of_bits
  Qsag.highCap_sliced_stage_supported_budget
  Qsag.slicedPcsHighCap_multifold_covers_nv25_to_28
  Qsag.highCap_sliced_multifold_stage_supported_budget

end Qsag
end
