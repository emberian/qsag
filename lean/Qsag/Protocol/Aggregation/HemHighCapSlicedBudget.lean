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
public import Qsag.Protocol.Aggregation.Cwyz26JohnsonCertificate
public import Qsag.Protocol.Aggregation.HemRbrSoundness
public import Qsag.Protocol.Aggregation.HemOpening
public import Qsag.Coding.Cwyz26
public import Qsag.Coding.GuruswamiSudan
import Qsag.Protocol.Aggregation.ConcreteSecurityBudget
import Qsag.Math.Counting
import Qsag.Math.Primality
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag
set_option autoImplicit false
attribute [-instance] Fin.instLinearOrderPackage

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

/-- `hemStageGeometry` directly encodes `pcs.rs::stage_geometry` across every `nv : Nat`. -/
theorem hemPcsHighCapStageGeometry_eq_hemStageGeometry (nv : Nat) :
    hemPcsHighCapStageGeometry nv = hemStageGeometry nv := by
  cases Nat.lt_or_ge 24 nv with
  | inr h24 => exact hemPcsHighCapStageGeometry_of_le_24 nv h24
  | inl h25 =>
    have hcases : nv = 25 ∨ nv = 26 ∨ nv = 27 ∨ nv = 28 ∨ 29 ≤ nv := by omega
    rcases hcases with rfl | rfl | rfl | rfl | h29
    · rw [hemStageGeometry_def]; decide
    · rw [hemStageGeometry_def]; decide
    · rw [hemStageGeometry_def]; decide
    · rw [hemStageGeometry_def]; decide
    · unfold hemPcsHighCapStageGeometry
      rw [hemStageGeometry_def]
      have hNot6 : ¬ nv ≤ 6 := by omega
      have hNot11 : ¬ nv ≤ 11 := by omega
      have hNot16 : ¬ nv ≤ 16 := by omega
      have hNot20 : ¬ nv ≤ 20 := by omega
      have hNot21 : ¬ nv = 21 := by omega
      have hNot22 : ¬ nv = 22 := by omega
      have hNot24 : ¬ nv ≤ 24 := by omega
      have hNot25 : ¬ nv = 25 := by omega
      have hNot26 : ¬ nv = 26 := by omega
      have hNot27 : ¬ nv = 27 := by omega
      have hNot28 : ¬ nv = 28 := by omega
      simp only [hNot6, hNot11, hNot16, hNot20, hNot21, hNot22, hNot24, hNot25, hNot26,
        hNot27, hNot28, ↓reduceIte]

theorem hemPcsHighCapStageGeoms_eq_hemStageGeoms (nv : Nat) :
    hemPcsHighCapStageGeoms nv = hemStageGeoms nv := by
  unfold hemPcsHighCapStageGeoms
  rw [hemPcsHighCapStageGeometry_eq_hemStageGeometry nv, hemStageGeoms_def]

theorem hemPcsHighCapEarlyStopVars_eq_hemEarlyStopVars (nv : Nat) :
    hemPcsHighCapEarlyStopVars nv = hemEarlyStopVars nv := by
  unfold hemPcsHighCapEarlyStopVars hemEarlyStopVars
  cases Nat.lt_or_ge 24 nv with
  | inr h24 => simp only [h24, ↓reduceIte]
  | inl h25 =>
    have hNot24 : ¬ nv ≤ 24 := by omega
    have hNot23 : ¬ nv = 23 := by omega
    have hNot20 : ¬ nv ≤ 20 := by omega
    have hNot16 : ¬ nv ≤ 16 := by omega
    have hNot15 : ¬ nv ≤ 15 := by omega
    have hNot13 : ¬ nv ≤ 13 := by omega
    have hNot8 : ¬ nv ≤ 8 := by omega
    have hNot6 : ¬ nv ≤ 6 := by omega
    have hNot3 : ¬ nv ≤ 3 := by omega
    simp only [hNot24, hNot23, hNot20, hNot16, hNot15, hNot13, hNot8, hNot6, hNot3, ↓reduceIte]

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

/-! ### §4. Constructive Cylinder-Sliced Johnson & Guruswami–Sudan Certificates (`nv ∈ 2..=28`) -/

/-- Closed-form bad-triple count for the 3-challenge `(θ, α, β)` equal-degree claim-fold at
    `(n, d, A, B, m, Dy)` with `q_θ = |S_θ|` and `q = |S|`. -/
def highCapSlicedThreeChallengeCount (n d A B m Dy q_θ q : Nat) : Nat :=
  let badMca := Dy + slicedRest n (d + 1) (A + 1) B (m * (A + 1) - Dy) Dy q
  let jbLo := JohnsonBound.johnsonBound n A d
  let jbHi := JohnsonBound.johnsonBound n A (d + 1)
  q_θ * badMca + (jbLo * jbLo) * (q_θ * q) + (jbHi * jbHi) * (q * q)

/-- Full 3-challenge `(θ, α, β)` rational error bound at stage geometry `g` over
    `QuarticGoldilocks³` (`q³ = (p⁴)³`, setting `d = g.d - 1` and `A = r.2.2.1 - 1`). -/
def highCapSlicedThreeChallengeStageBound (g : HemStageGeom)
    (r : Nat × Nat × Nat × Nat × Nat) (w : Nat × Nat × Nat × Nat) : RatBound :=
  let q := goldilocksExt4Card
  ⟨highCapSlicedThreeChallengeCount g.n (g.d - 1) (r.2.2.1 - 1) w.2.2.1 r.2.2.2.1 r.2.2.2.2 q q,
   q * (q * q),
   Nat.mul_pos goldilocksExt4Card_pos (Nat.mul_pos goldilocksExt4Card_pos goldilocksExt4Card_pos)⟩

theorem highCapSlicedThreeChallengeCount_def (n d A B m Dy q_θ q : Nat) :
    highCapSlicedThreeChallengeCount n d A B m Dy q_θ q =
      q_θ * (Dy + slicedRest n (d + 1) (A + 1) B (m * (A + 1) - Dy) Dy q) +
        (JohnsonBound.johnsonBound n A d * JohnsonBound.johnsonBound n A d) * (q_θ * q) +
        (JohnsonBound.johnsonBound n A (d + 1) * JohnsonBound.johnsonBound n A (d + 1)) * (q * q) := by
  rfl

theorem highCapSlicedThreeChallengeStageBound_num (g : HemStageGeom)
    (r : Nat × Nat × Nat × Nat × Nat) (w : Nat × Nat × Nat × Nat) :
    (highCapSlicedThreeChallengeStageBound g r w).num =
      highCapSlicedThreeChallengeCount g.n (g.d - 1) (r.2.2.1 - 1) w.2.2.1 r.2.2.2.1 r.2.2.2.2
        goldilocksExt4Card goldilocksExt4Card := by
  rfl

theorem highCapSlicedThreeChallengeStageBound_den (g : HemStageGeom)
    (r : Nat × Nat × Nat × Nat × Nat) (w : Nat × Nat × Nat × Nat) :
    (highCapSlicedThreeChallengeStageBound g r w).den =
      goldilocksExt4Card * (goldilocksExt4Card * goldilocksExt4Card) := by
  rfl

private def threeT (n d A B m Dy q : Nat) : Nat :=
  let badMca := Dy + restT n (d + 1) (A + 1) B (m * (A + 1) - Dy) Dy q
  let jbLo := (n * (A - d)) / (A * A - n * d)
  let jbHi := (n * (A - (d + 1))) / (A * A - n * (d + 1))
  q * badMca + (jbLo * jbLo) * (q * q) + (jbHi * jbHi) * (q * q)

private theorem threeT_eq (n d A B m Dy q : Nat) :
    threeT n d A B m Dy q = highCapSlicedThreeChallengeCount n d A B m Dy q q := by
  unfold threeT
  rw [highCapSlicedThreeChallengeCount_def, JohnsonBound.johnsonBound_eq,
    JohnsonBound.johnsonBound_eq, ← restT_eq]

/-- Evaluable check of bivariate Hasse Guruswami–Sudan interpolation dimensions and 3-challenge
    equal-degree claim-fold bounds across every stage of `nv ∈ 25..=28`. -/
private def gsAndThreeRowOkT (g : HemStageGeom)
    (r : Nat × Nat × Nat × Nat × Nat) (w : Nat × Nat × Nat × Nat) : Bool :=
  let d₀ := g.d - 1
  let A₀ := r.2.2.1 - 1
  let m := r.2.2.2.1
  let Dy := r.2.2.2.2
  let listG₀ := Nat.min Dy ((m * A₀ - 1) / d₀)
  let listG := Nat.min Dy ((m * r.2.2.1 - 1) / g.d)
  let q := goldilocksPrime ^ 4
  decide (2 ≤ g.d) &&
  decide (d₀ + 2 ≤ A₀) &&
  decide (r.2.2.1 ≤ g.n) &&
  paramsOkT g.n g.d r.2.2.1 w.2.2.1 m Dy &&
  decide (g.n * (m * (m + 1) / 2) < gsMonomialCount (m * A₀) d₀ listG₀) &&
  decide (g.n * (m * (m + 1) / 2) < gsMonomialCount (m * r.2.2.1) g.d listG) &&
  decide (threeT g.n d₀ A₀ w.2.2.1 m Dy q * 2 ^ 183 ≤ q * (q * q))

private def gsAndThreeStageOkT (nv : Nat) (g : HemStageGeom) : Bool :=
  if exhaustiveT g = true then true
  else
    match hemPcsHighCapTableRow nv g.stageIdx, slicedPcsHighCapRow nv g.stageIdx with
    | some r, some w => gsAndThreeRowOkT g r w
    | _, _ => false

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
private theorem gsAndThreeStageOkT_nv25_to_28 :
    ((List.range 4).all fun i =>
      (geomsAuxT 0 (i + 25) (hemPcsHighCapStageGeometry (i + 25))).all
        (gsAndThreeStageOkT (i + 25))) = true := by
  decide +kernel

private theorem highCap_gs_and_three_rows_nv2_to_28 (nv : Nat) (h2 : 2 ≤ nv) (h28 : nv ≤ 28)
    (g : HemStageGeom) (hg : g ∈ hemStageGeoms nv)
    (hne : hemJohnsonQromStageExhaustive g = false) :
    ∃ (r : Nat × Nat × Nat × Nat × Nat) (w : Nat × Nat × Nat × Nat),
      hemPcsHighCapTableRow nv g.stageIdx = some r ∧
      slicedPcsHighCapRow nv g.stageIdx = some w ∧
      2 ≤ g.d ∧
      (g.d - 1) + 2 ≤ r.2.2.1 - 1 ∧
      r.2.2.1 ≤ g.n ∧
      slicedParamsOk g.n g.d r.2.2.1 w.2.2.1 r.2.2.2.1 r.2.2.2.2 = true ∧
      g.n * (r.2.2.2.1 * (r.2.2.2.1 + 1) / 2) <
        gsMonomialCount (r.2.2.2.1 * (r.2.2.1 - 1)) (g.d - 1)
          (Nat.min r.2.2.2.2 ((r.2.2.2.1 * (r.2.2.1 - 1) - 1) / (g.d - 1))) ∧
      g.n * (r.2.2.2.1 * (r.2.2.2.1 + 1) / 2) <
        gsMonomialCount (r.2.2.2.1 * r.2.2.1) g.d
          (Nat.min r.2.2.2.2 ((r.2.2.2.1 * r.2.2.1 - 1) / g.d)) ∧
      atLeastBits 183 (highCapSlicedThreeChallengeStageBound g r w) ∧
      (nv ≤ 24 → atLeastBits 184 (highCapSlicedThreeChallengeStageBound g r w)) := by
  cases Nat.lt_or_ge 24 nv with
  | inr h24 =>
    obtain ⟨r, w, hr, hw, hd2, hdA, hOk, hCert184⟩ :=
      sliced_three_challenge_table_certificate JohnsonBound.johnsonBound
        JohnsonBound.johnsonBound_eq goldilocksExt4Card bridge_goldilocksExt4Card_def
        nv h2 h24 g hg hne
    obtain ⟨r', hr', hAg, hGs0, hGs1⟩ :=
      hem_gs_stage_row_dimensions_nv2_to_24 nv h2 h24 g hg hne
    cases Option.some.inj (hr.symm.trans hr')
    have hb184 : atLeastBits 184 (highCapSlicedThreeChallengeStageBound g r w) := by
      show (highCapSlicedThreeChallengeStageBound g r w).num * 2 ^ 184 ≤
          (highCapSlicedThreeChallengeStageBound g r w).den
      rw [highCapSlicedThreeChallengeStageBound_num, highCapSlicedThreeChallengeStageBound_den,
        highCapSlicedThreeChallengeCount_def]
      exact hCert184
    exact ⟨r, w, (hemPcsHighCapTableRow_of_le_24 nv _ h24).trans hr,
      (slicedPcsHighCapRow_of_le_24 nv _ h24).trans hw, hd2, by omega, hAg, hOk, hGs0, hGs1,
      atLeastBits_weaken (by decide) _ hb184, fun _ => hb184⟩
  | inl h25 =>
    have h1 := List.all_eq_true.mp gsAndThreeStageOkT_nv25_to_28 (nv - 25)
      (List.mem_range.mpr (by omega))
    have hEq : nv - 25 + 25 = nv := by omega
    rw [hEq, geomsAuxT_eq, ← hemPcsHighCapStageGeoms, hemPcsHighCapStageGeoms_eq_hemStageGeoms] at h1
    have h2' := List.all_eq_true.mp h1 g hg
    unfold gsAndThreeStageOkT at h2'
    have hExF : exhaustiveT g = false := (exhaustiveT_eq g).trans hne
    simp only [hExF, Bool.false_eq_true, ↓reduceIte] at h2'
    cases hr : hemPcsHighCapTableRow nv g.stageIdx with
    | none => rw [hr] at h2'; exact absurd h2' Bool.false_ne_true
    | some r =>
      cases hw : slicedPcsHighCapRow nv g.stageIdx with
      | none => rw [hr, hw] at h2'; exact absurd h2' Bool.false_ne_true
      | some w =>
        rw [hr, hw] at h2'
        dsimp only at h2'
        unfold gsAndThreeRowOkT at h2'
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h2'
        obtain ⟨⟨⟨⟨⟨⟨hd2, hdA⟩, hAg⟩, hOk⟩, hGs0⟩, hGs1⟩, hTh183⟩ := h2'
        rw [paramsOkT_eq] at hOk
        rw [threeT_eq] at hTh183
        have hNum : (highCapSlicedThreeChallengeStageBound g r w).num =
            highCapSlicedThreeChallengeCount g.n (g.d - 1) (r.2.2.1 - 1) w.2.2.1 r.2.2.2.1 r.2.2.2.2
              (goldilocksPrime ^ 4) (goldilocksPrime ^ 4) := by
          rw [highCapSlicedThreeChallengeStageBound_num, bridge_goldilocksExt4Card_def]
        have hDen : (highCapSlicedThreeChallengeStageBound g r w).den =
            (goldilocksPrime ^ 4) * ((goldilocksPrime ^ 4) * (goldilocksPrime ^ 4)) := by
          rw [highCapSlicedThreeChallengeStageBound_den, bridge_goldilocksExt4Card_def]
        refine ⟨r, w, rfl, rfl, hd2, hdA, hAg, hOk, hGs0, hGs1, ?_,
          fun h24 => absurd h24 (Nat.not_le_of_gt h25)⟩
        show (highCapSlicedThreeChallengeStageBound g r w).num * 2 ^ 183 ≤
            (highCapSlicedThreeChallengeStageBound g r w).den
        rw [hNum, hDen]
        exact hTh183

/-- **Guruswami–Sudan bivariate Hasse interpolation dimension certificate across `nv ∈ 2..=28`**:
    every non-exhaustive stage of `pcs.rs::stage_geometry` (`2..=28`) satisfies the exact bivariate
    Hasse interpolation dimension inequality both at `(g.d - 1, r.A - 1)` and at `(g.d, r.A)`. -/
theorem highCap_gs_interpolation_dimensions_nv2_to_28
    (nv : Nat) (h2 : 2 ≤ nv) (h28 : nv ≤ 28)
    (g : HemStageGeom) (hg : g ∈ hemStageGeoms nv)
    (hne : hemJohnsonQromStageExhaustive g = false) :
    ∃ r : Nat × Nat × Nat × Nat × Nat,
      hemPcsHighCapTableRow nv g.stageIdx = some r ∧
      g.n * (r.2.2.2.1 * (r.2.2.2.1 + 1) / 2) <
        gsMonomialCount (r.2.2.2.1 * (r.2.2.1 - 1)) (g.d - 1)
          (Nat.min r.2.2.2.2 ((r.2.2.2.1 * (r.2.2.1 - 1) - 1) / (g.d - 1))) ∧
      g.n * (r.2.2.2.1 * (r.2.2.2.1 + 1) / 2) <
        gsMonomialCount (r.2.2.2.1 * r.2.2.1) g.d
          (Nat.min r.2.2.2.2 ((r.2.2.2.1 * r.2.2.1 - 1) / g.d)) := by
  obtain ⟨r, _, hr, _, _, _, _, _, hGs0, hGs1, _, _⟩ :=
    highCap_gs_and_three_rows_nv2_to_28 nv h2 h28 g hg hne
  exact ⟨r, hr, hGs0, hGs1⟩

/-- **Executable Guruswami–Sudan Hasse interpolation witness across `nv ∈ 2..=28`** over any
    decidable field `F`. -/
theorem highCap_gs_constructive_interpolation_nv2_to_28 {F : Type} [LawfulField F] [DecidableEq F]
    (nv : Nat) (h2 : 2 ≤ nv) (h28 : nv ≤ 28)
    (g : HemStageGeom) (hg : g ∈ hemStageGeoms nv)
    (hne : hemJohnsonQromStageExhaustive g = false)
    (points : List (F × F)) (hN : points.length = g.n) :
    ∃ r : Nat × Nat × Nat × Nat × Nat,
      hemPcsHighCapTableRow nv g.stageIdx = some r ∧
      let B := r.2.2.2.1 * r.2.2.1
      let D := Nat.min r.2.2.2.2 ((r.2.2.2.1 * r.2.2.1 - 1) / g.d)
      let coeffs := solveHomogeneous (gsMonomialCount B g.d D)
        (gsInterpolationRows B g.d D r.2.2.2.1 points)
      coeffs.length = gsMonomialCount B g.d D ∧
      coeffs.any (fun c => !(decide (c = CommRingOps.zero))) = true ∧
      ∀ p ∈ points, ∀ i j, i + j < r.2.2.2.1 →
        gsHasseEval B g.d D coeffs (i, j) p = CommRingOps.zero := by
  obtain ⟨r, hr, _, hGs1⟩ := highCap_gs_interpolation_dimensions_nv2_to_28 nv h2 h28 g hg hne
  refine ⟨r, hr, ?_⟩
  apply guruswami_sudan_interpolation
  rw [hN]
  exact hGs1

/-- **Unconditional Guruswami–Sudan list bound across all non-exhaustive stages of `nv ∈ 2..=28`**
    over any decidable field `F`. -/
theorem highCap_gs_deployed_list_bound_nv2_to_28 {F : Type} [LawfulField F] [DecidableEq F]
    (nv : Nat) (h2 : 2 ≤ nv) (h28 : nv ≤ 28)
    (g : HemStageGeom) (hg : g ∈ hemStageGeoms nv)
    (hne : hemJohnsonQromStageExhaustive g = false)
    (domain : List F) (hDomNd : domain.Nodup) (hDomLen : domain.length = g.n)
    (word : F → F) :
    ∃ r : Nat × Nat × Nat × Nat × Nat,
      hemPcsHighCapTableRow nv g.stageIdx = some r ∧
      (∀ polys : List (GsUniPoly F), polys.Nodup →
        (∀ P ∈ polys, P.coeffs.length ≤ g.d + 1 ∧
          r.2.2.1 ≤ (domain.filter (fun x => decide (RoundPoly.evalCoeffs P.coeffs x = word x))).length) →
        polys.length ≤ Nat.min r.2.2.2.2 ((r.2.2.2.1 * r.2.2.1 - 1) / g.d) ∧
        polys.length ≤ r.2.2.2.2) := by
  obtain ⟨r, hr, _, hGs1⟩ := highCap_gs_interpolation_dimensions_nv2_to_28 nv h2 h28 g hg hne
  refine ⟨r, hr, fun polys hNd hClose => ?_⟩
  have hDim : domain.length * (r.2.2.2.1 * (r.2.2.2.1 + 1) / 2) <
      gsMonomialCount (r.2.2.2.1 * r.2.2.1) g.d
        (Nat.min r.2.2.2.2 ((r.2.2.2.1 * r.2.2.1 - 1) / g.d)) := by
    rw [hDomLen]
    exact hGs1
  have hB := guruswami_sudan_filter_list_bound domain word g.d r.2.2.1
    (Nat.min r.2.2.2.2 ((r.2.2.2.1 * r.2.2.1 - 1) / g.d)) r.2.2.2.1 hDomNd hDim polys hNd hClose
  exact ⟨hB, Nat.le_trans hB (Nat.min_le_left _ _)⟩

/-- **Constructive cylinder-sliced `[CWYZ26]` Johnson cascade certificate across `nv ∈ 2..=28`
    (`highCap_cwyz26_johnson_cascade_cert_nv2_to_28`)**:
    Every non-exhaustive canonical stage of `pcs.rs::stage_geometry` (`2 ≤ nv ≤ 28`, including all
    16 high-capacity stages of `nv = 25, 26, 27, 28`) carries a Lean-verified `HemCascadeRbrCert`
    constructed unconditionally via `hemCwyz26JohnsonCert_sliced` (`0` residual assumptions, `0`
    Rust-only witness caveats), paired with a `≥ 183`-bit binary budget (`≥ 184` up to `24`
    variables). -/
theorem highCap_cwyz26_johnson_cascade_cert_nv2_to_28
    (nv : Nat) (h2 : 2 ≤ nv) (h28 : nv ≤ 28)
    (g : HemStageGeom) (hg : g ∈ hemStageGeoms nv)
    (hne : hemJohnsonQromStageExhaustive g = false) :
    ∃ (r : Nat × Nat × Nat × Nat × Nat) (w : Nat × Nat × Nat × Nat),
      hemPcsHighCapTableRow nv g.stageIdx = some r ∧
      slicedPcsHighCapRow nv g.stageIdx = some w ∧
      (∀ (domPts S : List QuarticGoldilocks),
        domPts.Nodup → S.Nodup → domPts.length = g.n →
        HemCascadeRbrCert S domPts (g.d - 1) (r.2.2.1 - 1)
          (slicedStageCount S.length g r w)
          (Nat.min r.2.2.2.2 ((r.2.2.2.1 * (r.2.2.1 - 1) - 1) / (g.d - 1)))) ∧
      atLeastBits 183 (slicedBinaryStageBound g r w) ∧
      (nv ≤ 24 → atLeastBits 184 (slicedBinaryStageBound g r w)) ∧
      (25 ≤ nv → atLeastBits w.2.2.2 (slicedBinaryStageBound g r w)) := by
  have hgHigh : g ∈ hemPcsHighCapStageGeoms nv := by
    rwa [hemPcsHighCapStageGeoms_eq_hemStageGeoms]
  obtain ⟨r, w, hr, hw, hd, hb183, hb184, hbRow, _, _⟩ :=
    highCap_sliced_stage_supported_budget nv h2 h28 g hgHigh hne
  obtain ⟨r', w', hr', hw', hd2, hdA, hAg, _, hGs0, _, _, _⟩ :=
    highCap_gs_and_three_rows_nv2_to_28 nv h2 h28 g hg hne
  cases Option.some.inj (hr.symm.trans hr')
  cases Option.some.inj (hw.symm.trans hw')
  refine ⟨r, w, hr, hw, fun domPts S hDom hS hDomLen => ?_, hb183, hb184, hbRow⟩
  clear hb183 hb184 hbRow hr hw hg hgHigh hne h2 h28
  have hd1 : (g.d - 1) + 1 = g.d := Nat.sub_add_cancel (Nat.le_trans (by decide : 1 ≤ 2) hd2)
  have hApos : 1 ≤ r.2.2.1 :=
    Nat.le_trans (Nat.le_trans (by decide : 1 ≤ 2) (Nat.le_add_left 2 (g.d - 1)))
      (Nat.le_trans hdA (Nat.sub_le _ _))
  have hA1 : (r.2.2.1 - 1) + 1 = r.2.2.1 := Nat.sub_add_cancel hApos
  have hAgDom : (r.2.2.1 - 1) + 1 ≤ domPts.length := by
    rw [hA1, hDomLen]
    exact hAg
  have hDecomp : AffineFoldDecompBound domPts S ((g.d - 1) + 1) ((r.2.2.1 - 1) + 1)
      (slicedStageCount S.length g r w) := by
    rw [hd1, hA1]
    exact hd domPts S hDom hS hDomLen
  have hGsDim : domPts.length * (r.2.2.2.1 * (r.2.2.2.1 + 1) / 2) <
      gsMonomialCount (r.2.2.2.1 * (r.2.2.1 - 1)) (g.d - 1)
        (Nat.min r.2.2.2.2 ((r.2.2.2.1 * (r.2.2.1 - 1) - 1) / (g.d - 1))) := by
    rwa [hDomLen]
  have hdLeA : (g.d - 1) + 1 ≤ r.2.2.1 - 1 :=
    Nat.le_trans (Nat.succ_le_succ (Nat.le_succ _)) hdA
  exact
    { dom_nodup := hDom
      pool_nodup := hS
      deg_le_agree := hdA
      agree_succ_le_dom := hAgDom
      decomp_bound := hDecomp
      gs_list_bound := fun word =>
        guruswami_sudan_filter_list_bound domPts word (g.d - 1) (r.2.2.1 - 1)
          (Nat.min r.2.2.2.2 ((r.2.2.2.1 * (r.2.2.1 - 1) - 1) / (g.d - 1))) r.2.2.2.1
          hDom hGsDim (gsDecodeList (g.d - 1) (r.2.2.1 - 1) domPts word)
          (gsDecodeList_nodup (g.d - 1) (r.2.2.1 - 1) domPts word)
          (fun P hP => (mem_gsDecodeList_iff word hDom hdLeA P).mp hP) }

/-- **Closed-form 3-challenge `(θ, α, β)` equal-degree claim-fold bound at `(n, d, A, B, m, Dy)`**
    over `QuarticGoldilocks`. -/
theorem highCap_equal_degree_three_challenge_bound
    (D S_θ S kernel : List QuarticGoldilocks) (d A B m Dy : Nat)
    (f g : QuarticGoldilocks → QuarticGoldilocks) (e_f e_g c_f c_g : QuarticGoldilocks)
    (hD : D.Nodup) (hSθ : S_θ.Nodup) (hS : S.Nodup) (hdA : d + 2 ≤ A)
    (hParams : slicedParamsOk D.length (d + 1) (A + 1) B m Dy = true)
    (hInvalidFG :
      (∀ Fw : List QuarticGoldilocks, Fw.length ≤ d + 1 →
        A ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs Fw z = f z))).length →
        ringDot Fw kernel ≠ e_f) ∨
      (∀ Gw : List QuarticGoldilocks, Gw.length ≤ d + 1 →
        A ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs Gw z = g z))).length →
        ringDot Gw kernel ≠ e_g))
    (L : List (Fin (threePool S_θ S).length)) (hNd : L.Nodup)
    (hFlip : ∀ ch ∈ L, ¬¬ ∃ P : List QuarticGoldilocks,
      P.length ≤ d + 2 ∧
      A + 1 ≤ (D.filter (fun z =>
        let t := (threePool S_θ S).get ch
        let h_θ := CommRingOps.add (f z) (CommRingOps.mul t.1 (g z))
        decide (RoundPoly.evalCoeffs P z =
          CommRingOps.add (g z)
            (CommRingOps.mul (CommRingOps.add t.2.1 (CommRingOps.mul t.2.2 z)) h_θ)))).length ∧
      ringDot P kernel =
        let t := (threePool S_θ S).get ch
        hemFoldClaimUpdate e_f e_g c_f c_g t.1 t.2.1 t.2.2) :
    L.length ≤ highCapSlicedThreeChallengeCount D.length d A B m Dy S_θ.length S.length := by
  have hBase := equal_degree_three_challenge_fold_bound D S_θ S kernel d A
    (Dy + slicedRest D.length (d + 1) (A + 1) B (m * (A + 1) - Dy) Dy S.length)
    f g e_f e_g c_f c_g hD hSθ hS hdA
    (slicedParamsOk_sound D.length (d + 1) (A + 1) B m Dy hParams D S hD hS rfl)
    hInvalidFG L hNd hFlip
  obtain ⟨_, _, _, hBltA1, hDenB, _, _, _⟩ := of_decide_eq_true hParams
  clear hInvalidFG hFlip hParams
  have hBLeA : B ≤ A := Nat.le_of_lt_succ hBltA1
  have hBBLeAA : B * B ≤ A * A := Nat.mul_le_mul hBLeA hBLeA
  have hDenHi : D.length * (d + 1) < A * A :=
    Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.mul_le_mul_left D.length (by omega)) hDenB) hBBLeAA
  have hDenLo : D.length * d < A * A :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left D.length (by omega)) hDenHi
  have hF_lo := gsDecodeList_length_le_johnson D f d A hD (by omega) hDenLo
  have hG_lo := gsDecodeList_length_le_johnson D g d A hD (by omega) hDenLo
  have hF_hi := gsDecodeList_length_le_johnson D f (d + 1) A hD hdA hDenHi
  have hG_hi := gsDecodeList_length_le_johnson D g (d + 1) A hD hdA hDenHi
  rw [highCapSlicedThreeChallengeCount_def]
  have hMulLo : (gsDecodeList d A D f).length * (gsDecodeList d A D g).length * (S_θ.length * S.length) ≤
      (JohnsonBound.johnsonBound D.length A d * JohnsonBound.johnsonBound D.length A d) *
        (S_θ.length * S.length) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul hF_lo hG_lo)
  have hMulHi : (gsDecodeList (d + 1) A D f).length * (gsDecodeList (d + 1) A D g).length *
      (S.length * S.length) ≤
      (JohnsonBound.johnsonBound D.length A (d + 1) * JohnsonBound.johnsonBound D.length A (d + 1)) *
        (S.length * S.length) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul hF_hi hG_hi)
  omega

/-- **Three-challenge `(θ, α, β)` equal-degree claim-fold budget across `nv ∈ 2..=28`**:
    every non-exhaustive canonical stage of `pcs.rs::stage_geometry` (`2 ≤ nv ≤ 28`) satisfies the
    constructive 3-challenge equal-degree fold bound at `≥ 183` bits (`≥ 184` up to `24`
    variables), clearing `128` bits under `dfmRoundScale Q` for `Q + 1 ≤ 2^26` (`Q + 1 ≤ 2^27` up
    to `24` variables). -/
theorem highCap_sliced_three_challenge_stage_supported_budget
    (nv : Nat) (h2 : 2 ≤ nv) (h28 : nv ≤ 28)
    (g : HemStageGeom) (hg : g ∈ hemStageGeoms nv)
    (hne : hemJohnsonQromStageExhaustive g = false) :
    ∃ (r : Nat × Nat × Nat × Nat × Nat) (w : Nat × Nat × Nat × Nat),
      hemPcsHighCapTableRow nv g.stageIdx = some r ∧
      slicedPcsHighCapRow nv g.stageIdx = some w ∧
      2 ≤ g.d ∧
      (g.d - 1) + 2 ≤ r.2.2.1 - 1 ∧
      slicedParamsOk g.n g.d r.2.2.1 w.2.2.1 r.2.2.2.1 r.2.2.2.2 = true ∧
      atLeastBits 183 (highCapSlicedThreeChallengeStageBound g r w) ∧
      (nv ≤ 24 → atLeastBits 184 (highCapSlicedThreeChallengeStageBound g r w)) ∧
      (∀ Q : Nat, Q + 1 ≤ 2 ^ 26 →
        atLeastBits 128 (dfmRoundScale Q (highCapSlicedThreeChallengeStageBound g r w))) ∧
      (nv ≤ 24 → ∀ Q : Nat, Q + 1 ≤ 2 ^ 27 →
        atLeastBits 128 (dfmRoundScale Q (highCapSlicedThreeChallengeStageBound g r w))) := by
  obtain ⟨r, w, hr, hw, hd2, hdA, _, hOk, _, _, hb183, hb184⟩ :=
    highCap_gs_and_three_rows_nv2_to_28 nv h2 h28 g hg hne
  exact ⟨r, w, hr, hw, hd2, hdA, hOk, hb183, hb184,
    fun Q hQ => dfmRoundScale_clears_128bits_of_bits _ 26
      (atLeastBits_weaken (by decide) _ hb183) Q hQ,
    fun h24 Q hQ => dfmRoundScale_clears_128bits_of_bits _ 27
      (atLeastBits_weaken (by decide) _ (hb184 h24)) Q hQ⟩

#verify_constructive Qsag.hemPcsHighCapStageGeometry_of_le_24
#verify_constructive Qsag.hemPcsHighCapStageGeoms_of_le_24
#verify_constructive Qsag.hemPcsHighCapTableRow_of_le_24
#verify_constructive Qsag.slicedPcsHighCapRow_of_le_24
#verify_constructive Qsag.hemPcsHighCapStageGeometry_eq_hemStageGeometry
#verify_constructive Qsag.hemPcsHighCapStageGeoms_eq_hemStageGeoms
#verify_constructive Qsag.hemPcsHighCapEarlyStopVars_eq_hemEarlyStopVars
#verify_constructive Qsag.hemPcsHighCapStageGeometry_nv25_to_28
#verify_constructive Qsag.hemPcsHighCapStageGeoms_nv25
#verify_constructive Qsag.hemPcsHighCapStageGeoms_nv26
#verify_constructive Qsag.hemPcsHighCapStageGeoms_nv27
#verify_constructive Qsag.hemPcsHighCapStageGeoms_nv28
#verify_constructive Qsag.hemPcsHighCapStageGeoms_of_ge_29
#verify_constructive Qsag.hemPcsHighCap_geometry_valid_nv25_to_28
#verify_constructive Qsag.highCap_stages_nonexhaustive
#verify_constructive Qsag.dfmRoundScale_clears_128bits_of_bits
#verify_constructive Qsag.highCap_sliced_stage_supported_budget
#verify_constructive Qsag.slicedPcsHighCap_multifold_covers_nv25_to_28
#verify_constructive Qsag.highCap_sliced_multifold_stage_supported_budget
#verify_constructive Qsag.highCap_gs_interpolation_dimensions_nv2_to_28
#verify_constructive Qsag.highCap_gs_constructive_interpolation_nv2_to_28
#verify_constructive Qsag.highCap_gs_deployed_list_bound_nv2_to_28
#verify_constructive Qsag.highCap_cwyz26_johnson_cascade_cert_nv2_to_28
#verify_constructive Qsag.highCap_equal_degree_three_challenge_bound
#verify_constructive Qsag.highCap_sliced_three_challenge_stage_supported_budget

end Qsag
end

/-! ### Exports for lane agg -/
public section
namespace Qsag

#export_eqns hemPcsHighCapTableRow slicedPcsHighCapRow hemPcsHighCapWitnessRows
  slicedPcsHighCapTable

/- Bit floors of the three stage bounds, restated on the evaluable twins of §2 and §4. -/

private theorem binaryBits_iff_T (g : HemStageGeom) (r : Nat × Nat × Nat × Nat × Nat)
    (w : Nat × Nat × Nat × Nat) (k b : Nat) :
    k * (slicedBinaryStageBound g r w).num * 2 ^ b ≤ (slicedBinaryStageBound g r w).den ↔
      k * (r.2.2.2.2 +
          restT g.n g.d r.2.2.1 w.2.2.1 (r.2.2.2.1 * r.2.2.1 - r.2.2.2.2) r.2.2.2.2
            (goldilocksPrime ^ 4)) * 2 ^ b ≤
        goldilocksPrime ^ 4 * goldilocksPrime ^ 4 := by
  rw [bridge_slicedBinaryStageBound_num, bridge_slicedBinaryStageBound_den,
    slicedStageCount_def, bridge_goldilocksExt4Card_def, restT_eq]

private theorem multiFoldBits_iff_T (g : HemStageGeom) (r : Nat × Nat × Nat × Nat × Nat)
    (w : Nat × Nat × Nat × Nat) (k b : Nat) :
    k * (slicedMultiFoldStageBound g r w).num * 2 ^ b ≤ (slicedMultiFoldStageBound g r w).den ↔
      k * mfNumT g r w * 2 ^ b ≤ (goldilocksPrime ^ 4) ^ 4 := by
  rw [mfNumT_eq, bridge_slicedMultiFoldStageBound_den, bridge_goldilocksExt4Card_def]

private theorem threeChallengeBits_iff_T (g : HemStageGeom)
    (r : Nat × Nat × Nat × Nat × Nat) (w : Nat × Nat × Nat × Nat) (k b : Nat) :
    k * (highCapSlicedThreeChallengeStageBound g r w).num * 2 ^ b ≤
        (highCapSlicedThreeChallengeStageBound g r w).den ↔
      k * threeT g.n (g.d - 1) (r.2.2.1 - 1) w.2.2.1 r.2.2.2.1 r.2.2.2.2 (goldilocksPrime ^ 4) *
          2 ^ b ≤
        goldilocksPrime ^ 4 * (goldilocksPrime ^ 4 * goldilocksPrime ^ 4) := by
  rw [highCapSlicedThreeChallengeStageBound_num, highCapSlicedThreeChallengeStageBound_den,
    bridge_goldilocksExt4Card_def, threeT_eq]

private theorem atLeastBits_iff_one_mul (b : Nat) (x : RatBound) :
    atLeastBits b x ↔ 1 * x.num * 2 ^ b ≤ x.den := by
  rw [Nat.one_mul]
  exact Iff.rfl

private theorem dfm_atLeastBits_iff (Q : Nat) (x : RatBound) :
    atLeastBits 128 (dfmRoundScale Q x) ↔ (2 * Q + 1) ^ 2 * x.num * 2 ^ 128 ≤ x.den :=
  Iff.rfl

/-- `nv = 28`, stage `0`: the binary bound does not have `184` bits, and its DFM scale at
    `Q + 1 = 2^27` does not have `128` bits. -/
theorem highCap_nv28_stage0_binary_tight :
    ¬ atLeastBits 184 (slicedBinaryStageBound { stageIdx := 0, logBlowup := 2, stepVars := 6, n := 16777216, d := 4194306 }
        (28, 0, 8433861, 128, 6362) (28, 0, 8388611, 183)) ∧
    ¬ atLeastBits 128 (dfmRoundScale (2 ^ 27 - 1) (slicedBinaryStageBound
        { stageIdx := 0, logBlowup := 2, stepVars := 6, n := 16777216, d := 4194306 }
        (28, 0, 8433861, 128, 6362) (28, 0, 8388611, 183))) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact absurd ((binaryBits_iff_T _ _ _ _ _).mp ((atLeastBits_iff_one_mul _ _).mp h))
      (by decide +kernel)
  · exact absurd ((binaryBits_iff_T _ _ _ _ _).mp ((dfm_atLeastBits_iff _ _).mp h))
      (by decide +kernel)

set_option maxRecDepth 1000000 in
/-- `nv = 28`, stage `0`: the multi-fold bound does not have `178` bits, and its DFM scale at
    `Q + 1 = 2^24` does not have `128` bits. -/
theorem highCap_nv28_stage0_multifold_tight :
    ¬ atLeastBits 178 (slicedMultiFoldStageBound { stageIdx := 0, logBlowup := 2, stepVars := 6, n := 16777216, d := 4194306 }
        (28, 0, 8433861, 128, 6362) (28, 0, 8388611, 183)) ∧
    ¬ atLeastBits 128 (dfmRoundScale (2 ^ 24 - 1) (slicedMultiFoldStageBound
        { stageIdx := 0, logBlowup := 2, stepVars := 6, n := 16777216, d := 4194306 }
        (28, 0, 8433861, 128, 6362) (28, 0, 8388611, 183))) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact absurd ((multiFoldBits_iff_T _ _ _ _ _).mp ((atLeastBits_iff_one_mul _ _).mp h))
      (by decide +kernel)
  · exact absurd ((multiFoldBits_iff_T _ _ _ _ _).mp ((dfm_atLeastBits_iff _ _).mp h))
      (by decide +kernel)

set_option maxRecDepth 1000000 in
/-- `nv = 25`, stage `1`: the multi-fold bound does not have `194` bits. -/
theorem highCap_nv25_stage1_multifold_tight :
    ¬ atLeastBits 194 (slicedMultiFoldStageBound { stageIdx := 1, logBlowup := 4, stepVars := 4, n := 524288, d := 32770 }
        (25, 1, 133941, 32, 1732) (25, 1, 131078, 196)) := fun h =>
  absurd ((multiFoldBits_iff_T _ _ _ _ _).mp ((atLeastBits_iff_one_mul _ _).mp h))
    (by decide +kernel)

/-- `nv = 28`, stage `0`: the 3-challenge bound does not have `184` bits, and its DFM scale at
    `Q + 1 = 2^27` does not have `128` bits. -/
theorem highCap_nv28_stage0_three_challenge_tight :
    ¬ atLeastBits 184 (highCapSlicedThreeChallengeStageBound
        { stageIdx := 0, logBlowup := 2, stepVars := 6, n := 16777216, d := 4194306 }
        (28, 0, 8433861, 128, 6362) (28, 0, 8388611, 183)) ∧
    ¬ atLeastBits 128 (dfmRoundScale (2 ^ 27 - 1) (highCapSlicedThreeChallengeStageBound
        { stageIdx := 0, logBlowup := 2, stepVars := 6, n := 16777216, d := 4194306 }
        (28, 0, 8433861, 128, 6362) (28, 0, 8388611, 183))) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact absurd ((threeChallengeBits_iff_T _ _ _ _ _).mp ((atLeastBits_iff_one_mul _ _).mp h))
      (by decide +kernel)
  · exact absurd ((threeChallengeBits_iff_T _ _ _ _ _).mp ((dfm_atLeastBits_iff _ _).mp h))
      (by decide +kernel)

#verify_constructive Qsag.highCap_nv28_stage0_binary_tight
#verify_constructive Qsag.highCap_nv28_stage0_multifold_tight
#verify_constructive Qsag.highCap_nv25_stage1_multifold_tight
#verify_constructive Qsag.highCap_nv28_stage0_three_challenge_tight

end Qsag
end
