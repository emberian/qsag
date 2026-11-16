module
/-
Fixtures and teeth for `Qsag.Protocol.Aggregation.HemHighCapSlicedBudget`.

* Positive witnesses of both budgets at `nv = 28`, stage `0`, and `nv = 27`, stage `1`.
* Tightness: at `nv = 28`, stage `0`, the binary bound has `183` bits and not `184`, and the
  multi-fold bound `177` bits and not `178`; the DFM scale fails `128` bits one query bit above
  each stated budget. At `nv = 25`, stage `1`, the multi-fold bound has `193` bits and not `194`.
* `nv = 29` has no stage and no rows.
* The `25..=28` rows pass the Johnson witness check of `checkWhirAffineWitness` at the query
  counts and targets of `affine_schedule.rs::finite_johnson_witnesses_cover_every_canonical_stage`.
* Constructive `[CWYZ26]` cylinder-sliced Johnson cascade certificates (`HemCascadeRbrCert`),
  bivariate Hasse Guruswami–Sudan interpolation dimensions, and 3-challenge `(θ, α, β)`
  equal-degree fold budgets across `nv ∈ 2..=28` (`183` bits and not `184` at `nv = 28, stage 0`;
  multiplicity-`1` Sudan fails the interpolation dimension bound at `nv = 28, stage 0`).
* Full parity of `hemStageGeometry`, `hemPcsHighCapStageGeometry`, and `hemHighCapStageGeometry`
  across every `nv : Nat` (matching `pcs.rs::stage_geometry` on `2..=28` and empty for `nv ≥ 29`).
-/
public import Qsag.Protocol.Aggregation.HemHighCapSlicedBudget
public import Qsag.Protocol.Aggregation.Cwyz26EqualDegreeAndMultiFold
public import Qsag.Protocol.Aggregation.HemOpening
public import Qsag.Protocol.Aggregation.ConcreteSecurityBudget
public import Qsag.Coding.Cwyz26
public import Qsag.Coding.AffineProximity
public import Qsag.Math.Counting
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag
namespace HemHighCapSlicedBudgetTests

set_option autoImplicit false
attribute [-instance] Fin.instLinearOrderPackage

/-! ### Positive witnesses -/

/-- Premises of both budgets are met at `nv = 28`, stage `0`. -/
theorem inhabited_highCap_sliced_budget_nv28 :
    ∃ (nv : Nat) (g : HemStageGeom),
      2 ≤ nv ∧ nv ≤ 28 ∧ g ∈ hemPcsHighCapStageGeoms nv ∧
        hemJohnsonQromStageExhaustive g = false :=
  ⟨28, (hemPcsHighCapStageGeoms 28).get ⟨0, by decide +kernel⟩,
    by decide, by decide, list_get_mem _ _, by decide +kernel⟩

/-- Premises of both budgets are met at `nv = 27`, stage `1`. -/
theorem inhabited_highCap_sliced_budget_nv27 :
    ∃ (nv : Nat) (g : HemStageGeom),
      2 ≤ nv ∧ nv ≤ 28 ∧ g ∈ hemPcsHighCapStageGeoms nv ∧
        hemJohnsonQromStageExhaustive g = false :=
  ⟨27, (hemPcsHighCapStageGeoms 27).get ⟨1, by decide +kernel⟩,
    by decide, by decide, list_get_mem _ _, by decide +kernel⟩

/-- The two fixtures are above `24` variables and have the stage shape of
    `pcs.rs::stage_geometry` at `28` and `27`. -/
theorem inhabited_highCap_sliced_budget_fixture_shape :
    (hemPcsHighCapStageGeoms 28).map (fun g => (g.stageIdx, g.logBlowup, g.stepVars)) =
      [(0, 2, 6), (1, 4, 6), (2, 6, 4), (3, 8, 4)] ∧
    (hemPcsHighCapStageGeoms 27).map (fun g => (g.stageIdx, g.logBlowup, g.stepVars)) =
      [(0, 2, 6), (1, 4, 5), (2, 6, 4), (3, 8, 4)] := by
  decide +kernel

/-! ### Tightness of the floors -/

/-- Binary bound of a stage, `RatBound.one` when a row is missing. -/
def binaryProfile (nv : Nat) (g : HemStageGeom) : RatBound :=
  match hemPcsHighCapTableRow nv g.stageIdx, slicedPcsHighCapRow nv g.stageIdx with
  | some r, some w => slicedBinaryStageBound g r w
  | _, _ => RatBound.one

/-- Multi-fold bound of a stage, `RatBound.one` when a row is missing. -/
def multiFoldProfile (nv : Nat) (g : HemStageGeom) : RatBound :=
  match hemPcsHighCapTableRow nv g.stageIdx, slicedPcsHighCapRow nv g.stageIdx with
  | some r, some w => slicedMultiFoldStageBound g r w
  | _, _ => RatBound.one

/-- At `nv = 28`, stage `0`, the binary bound has `183` bits and not `184`, and the DFM scale
    fails `128` bits at `Q + 1 = 2^27`: neither the `184`-bit floor nor the `Q + 1 ≤ 2^27`
    budget of `sliced_stage_supported_budget` extends above `24` variables, and `183` bits /
    `Q + 1 ≤ 2^26` cannot be raised. -/
theorem tooth_highCap_nv28_binary_at_183_bits :
    ∃ g : HemStageGeom,
      g ∈ hemPcsHighCapStageGeoms 28 ∧
      atLeastBits 183 (binaryProfile 28 g) ∧
      ¬ atLeastBits 184 (binaryProfile 28 g) ∧
      ¬ atLeastBits 128 (dfmRoundScale (2 ^ 27 - 1) (binaryProfile 28 g)) :=
  ⟨(hemPcsHighCapStageGeoms 28).get ⟨0, by decide +kernel⟩, list_get_mem _ _,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 1000000 in
/-- At `nv = 28`, stage `0` (`stepVars = 6`), the summed multi-fold bound has `177` bits and
    not `178`, and the DFM scale fails `128` bits at `Q + 1 = 2^24`. -/
theorem tooth_highCap_nv28_multifold_at_177_bits :
    ∃ g : HemStageGeom,
      g ∈ hemPcsHighCapStageGeoms 28 ∧
      g.stepVars = 6 ∧
      atLeastBits 177 (multiFoldProfile 28 g) ∧
      ¬ atLeastBits 178 (multiFoldProfile 28 g) ∧
      ¬ atLeastBits 128 (dfmRoundScale (2 ^ 24 - 1) (multiFoldProfile 28 g)) :=
  ⟨(hemPcsHighCapStageGeoms 28).get ⟨0, by decide +kernel⟩, list_get_mem _ _,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 1000000 in
/-- At `nv = 25`, stage `1` (`stepVars = 4`, the stage where `pcs.rs::stage_geometry` differs
    from `hemHighCapStageGeometry`), the summed multi-fold bound has `193` bits and not `194`. -/
theorem tooth_highCap_nv25_stage1_multifold_at_193_bits :
    ∃ g : HemStageGeom,
      g ∈ hemPcsHighCapStageGeoms 25 ∧
      g.stepVars = 4 ∧
      atLeastBits 193 (multiFoldProfile 25 g) ∧
      ¬ atLeastBits 194 (multiFoldProfile 25 g) :=
  ⟨(hemPcsHighCapStageGeoms 25).get ⟨1, by decide +kernel⟩, list_get_mem _ _,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ### The cap at `28` variables -/

/-- `nv = 29` is outside `pcs.rs::MAX_PCS_NUM_VARS`: no stage satisfies the membership premise of
    the budgets. -/
theorem tooth_highCap_nv29_has_no_stage :
    ¬ (∃ g : HemStageGeom, g ∈ hemPcsHighCapStageGeoms 29) := by
  rw [hemPcsHighCapStageGeoms_of_ge_29 29 (by decide)]
  exact fun ⟨_, hg⟩ => nomatch hg

/-- Neither table has a row at `nv = 29`, for any stage index. -/
theorem highCap_nv29_has_no_row (stage : Nat) :
    hemPcsHighCapTableRow 29 stage = none ∧ slicedPcsHighCapRow 29 stage = none := by
  have hJ : hemPcsHighCapWitnessRows.all (fun r => !(r.1 == 29)) = true := by decide
  have hS : slicedPcsHighCapTable.all (fun r => !(r.1 == 29)) = true := by decide
  have h24 : ¬ (29 ≤ 24) := by decide
  unfold hemPcsHighCapTableRow slicedPcsHighCapRow
  simp only [h24, ↓reduceIte]
  refine ⟨List.find?_eq_none.mpr fun x hx => ?_, List.find?_eq_none.mpr fun x hx => ?_⟩
  · have h := List.all_eq_true.mp hJ x hx
    cases hb : (x.1 == 29) with
    | false => exact Bool.false_ne_true
    | true => rw [hb] at h; exact absurd h (by decide)
  · have h := List.all_eq_true.mp hS x hx
    cases hb : (x.1 == 29) with
    | false => exact Bool.false_ne_true
    | true => rw [hb] at h; exact absurd h (by decide)

/-! ### Johnson witness check of the `25..=28` rows -/

/-- The stage witness of `affine_schedule.rs::check_witness_row`: geometry from the stage,
    `(A, m, D)` from the row, `B = A - 1`. -/
def johnsonWitness (queries targetBits : Nat) (g : HemStageGeom)
    (r : Nat × Nat × Nat × Nat × Nat) : WhirAffineWitness :=
  { n := g.n, d := g.d, sFolds := g.stepVars, A := r.2.2.1, B := r.2.2.1 - 1,
    m := r.2.2.2.1, D := r.2.2.2.2, queries := queries, queryTargetBits := targetBits }

/-- One `25..=28` stage under the three query tables of `pcs.rs::minimum_queries`:
    `BciksJohnsonQrom128` (`⌈512 / log₂ B⌉ + 2` queries, target `256`),
    `Cdhz25JohnsonQrom128` (`(202, 102, 70, 52)`, target `200`) and `Cdhz25ZeroPowQrom128`
    (`(216, 109, 74, 56)`, target `214`). -/
def johnsonStageChecked (nv : Nat) (g : HemStageGeom) : Bool :=
  match hemPcsHighCapTableRow nv g.stageIdx with
  | some r =>
    checkWhirAffineWitness
      (johnsonWitness (hemJohnsonMinQueries true g.logBlowup) 256 g r) (goldilocksPrime ^ 4) &&
    checkWhirAffineWitness
      (johnsonWitness (HemOptimizedQromSchedule.cdhzPow16At2pow38.minQueries g.logBlowup) 200 g r)
      (goldilocksPrime ^ 4) &&
    checkWhirAffineWitness
      (johnsonWitness (HemOptimizedQromSchedule.unitaryZeroPow.minQueries g.logBlowup) 214 g r)
      (goldilocksPrime ^ 4) &&
    decide (whirAffineStageSimpleNum
      (johnsonWitness (hemJohnsonMinQueries true g.logBlowup) 256 g r) + 1 < 2000)
  | none => false

set_option maxRecDepth 1000000 in
/-- Every `hemPcsHighCapWitnessRows` row passes `checkWhirAffineWitness` over `GoldilocksExt4`
    on its `pcs.rs::stage_geometry` stage at the query count and target of each QROM regime, with
    folding numerator `+ 1 < 2000` (the assertions of
    `affine_schedule.rs::finite_johnson_witnesses_cover_every_canonical_stage` on `25..=28`,
    without its fixed-path modulo-bias check). -/
theorem highCap_witness_rows_pass_johnson_check (nv : Nat) (h25 : 25 ≤ nv) (h28 : nv ≤ 28)
    (g : HemStageGeom) (hg : g ∈ hemPcsHighCapStageGeoms nv) :
    johnsonStageChecked nv g = true := by
  have hAll : ((List.range 4).all fun i =>
      (hemPcsHighCapStageGeoms (i + 25)).all (johnsonStageChecked (i + 25))) = true := by
    decide +kernel
  have h1 := List.all_eq_true.mp hAll (nv - 25) (List.mem_range.mpr (by omega))
  have hEq : nv - 25 + 25 = nv := by omega
  rw [hEq] at h1
  exact List.all_eq_true.mp h1 g hg

/-- Lowering the agreement threshold of the `nv = 28`, stage `0` row by `40000` breaks the
    Johnson check: the rows are not slack parameters. -/
theorem tooth_highCap_johnson_check_rejects_low_agreement :
    ∃ g : HemStageGeom,
      g ∈ hemPcsHighCapStageGeoms 28 ∧
      johnsonStageChecked 28 g = true ∧
      ¬ (checkWhirAffineWitness
        (johnsonWitness (hemJohnsonMinQueries true g.logBlowup) 256 g
          (28, 0, 8433861 - 40000, 128, 6362)) (goldilocksPrime ^ 4) = true) :=
  ⟨(hemPcsHighCapStageGeoms 28).get ⟨0, by decide +kernel⟩, list_get_mem _ _,
    by decide +kernel, by decide +kernel⟩

/-! ### Constructive `[CWYZ26]` Johnson certificates, GS list bounds, and 3-challenge fold teeth -/

/-- Premises of `highCap_cwyz26_johnson_cascade_cert_nv2_to_28`,
    `highCap_gs_interpolation_dimensions_nv2_to_28`, and
    `highCap_sliced_three_challenge_stage_supported_budget` are met at `nv = 28`, stage `0`. -/
theorem inhabited_highCap_cwyz26_johnson_cert_nv28 :
    ∃ (nv : Nat) (g : HemStageGeom),
      2 ≤ nv ∧ nv ≤ 28 ∧ g ∈ hemStageGeoms nv ∧
        hemJohnsonQromStageExhaustive g = false :=
  ⟨28, (hemStageGeoms 28).get ⟨0, by decide +kernel⟩,
    by decide, by decide, list_get_mem _ _, by decide +kernel⟩

/-- Premises of `highCap_cwyz26_johnson_cascade_cert_nv2_to_28` are met at `nv = 25`, stage `1`
    (`stepVars = 4`, matching `pcs.rs::stage_geometry(25)`). -/
theorem inhabited_highCap_cwyz26_johnson_cert_nv25 :
    ∃ (nv : Nat) (g : HemStageGeom),
      2 ≤ nv ∧ nv ≤ 28 ∧ g ∈ hemStageGeoms nv ∧
        hemJohnsonQromStageExhaustive g = false :=
  ⟨25, (hemStageGeoms 25).get ⟨1, by decide +kernel⟩,
    by decide, by decide, list_get_mem _ _, by decide +kernel⟩

/-- 3-challenge equal-degree fold bound of a stage, `RatBound.one` when a row is missing. -/
def threeChallengeProfile (nv : Nat) (g : HemStageGeom) : RatBound :=
  match hemPcsHighCapTableRow nv g.stageIdx, slicedPcsHighCapRow nv g.stageIdx with
  | some r, some w => highCapSlicedThreeChallengeStageBound g r w
  | _, _ => RatBound.one

/-- At `nv = 28`, stage `0`, the 3-challenge `(θ, α, β)` equal-degree fold bound has `183` bits
    and not `184`, and fails `128` bits under `dfmRoundScale` at `Q + 1 = 2^27`. -/
theorem tooth_highCap_nv28_three_challenge_at_183_bits :
    ∃ g : HemStageGeom,
      g ∈ hemStageGeoms 28 ∧
      atLeastBits 183 (threeChallengeProfile 28 g) ∧
      ¬ atLeastBits 184 (threeChallengeProfile 28 g) ∧
      ¬ atLeastBits 128 (dfmRoundScale (2 ^ 27 - 1) (threeChallengeProfile 28 g)) :=
  ⟨(hemStageGeoms 28).get ⟨0, by decide +kernel⟩, list_get_mem _ _,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 1000000 in
/-- At `nv = 28`, stage `0`, multiplicity `m = 1` (Sudan) fails the bivariate Hasse interpolation
    dimension inequality `g.n * (m*(m+1)/2) < gsMonomialCount (m*A₀) d₀ listG₀`, whereas the
    deployed multiplicity `m = 128` strictly clears it. -/
theorem tooth_highCap_nv28_gs_dim_rejects_sudan_m1 :
    let g := (hemStageGeoms 28).get ⟨0, by decide +kernel⟩
    let d₀ := g.d - 1
    let A₀ := 8433861 - 1
    let listG_m1 := Nat.min 6362 ((1 * A₀ - 1) / d₀)
    let listG_m128 := Nat.min 6362 ((128 * A₀ - 1) / d₀)
    ¬ (g.n * (1 * (1 + 1) / 2) < gsMonomialCount (1 * A₀) d₀ listG_m1) ∧
    g.n * (128 * (128 + 1) / 2) < gsMonomialCount (128 * A₀) d₀ listG_m128 := by
  decide +kernel

/-- `hemStageGeoms 29` is empty (`MAX_PCS_NUM_VARS = 28`). -/
theorem tooth_highCap_hemStageGeoms_nv29_empty :
    ¬ (∃ g : HemStageGeom, g ∈ hemStageGeoms 29) := by
  rw [← hemPcsHighCapStageGeoms_eq_hemStageGeoms, hemPcsHighCapStageGeoms_of_ge_29 29 (by decide)]
  exact fun ⟨_, hg⟩ => nomatch hg

/-! ### Exact lockstep parity with `hemStageGeometry` and `hemHighCapStageGeometry` -/

/-- `hemPcsHighCapStageGeometry` and `hemStageGeometry` agree across every `nv : Nat`
    (`2..=28` match `pcs.rs::stage_geometry`, and `nv ≥ 29` is `[]`). -/
theorem hemPcsHighCapStageGeometry_eq_hemStageGeometry_all (nv : Nat) :
    hemPcsHighCapStageGeometry nv = hemStageGeometry nv ∧
    hemPcsHighCapStageGeoms nv = hemStageGeoms nv :=
  ⟨hemPcsHighCapStageGeometry_eq_hemStageGeometry nv,
   hemPcsHighCapStageGeoms_eq_hemStageGeoms nv⟩

#verify_constructive
  inhabited_highCap_sliced_budget_nv28
  inhabited_highCap_sliced_budget_nv27
  inhabited_highCap_sliced_budget_fixture_shape
  inhabited_highCap_cwyz26_johnson_cert_nv28
  inhabited_highCap_cwyz26_johnson_cert_nv25
  tooth_highCap_nv28_binary_at_183_bits
  tooth_highCap_nv28_multifold_at_177_bits
  tooth_highCap_nv25_stage1_multifold_at_193_bits
  tooth_highCap_nv28_three_challenge_at_183_bits
  tooth_highCap_nv28_gs_dim_rejects_sudan_m1
  tooth_highCap_nv29_has_no_stage
  tooth_highCap_hemStageGeoms_nv29_empty
  highCap_nv29_has_no_row
  highCap_witness_rows_pass_johnson_check
  tooth_highCap_johnson_check_rejects_low_agreement
  hemPcsHighCapStageGeometry_eq_hemStageGeometry_all

#verify_inhabited Qsag.highCap_sliced_stage_supported_budget inhabited_highCap_sliced_budget_nv28
#verify_inhabited Qsag.highCap_sliced_stage_supported_budget inhabited_highCap_sliced_budget_nv27
#tooth_pair Qsag.highCap_sliced_stage_supported_budget vs tooth_highCap_nv28_binary_at_183_bits
#tooth_pair Qsag.highCap_sliced_stage_supported_budget vs tooth_highCap_nv29_has_no_stage

#verify_inhabited Qsag.highCap_sliced_multifold_stage_supported_budget inhabited_highCap_sliced_budget_nv28
#verify_inhabited Qsag.highCap_sliced_multifold_stage_supported_budget inhabited_highCap_sliced_budget_nv27
#tooth_pair Qsag.highCap_sliced_multifold_stage_supported_budget vs tooth_highCap_nv28_multifold_at_177_bits
#tooth_pair Qsag.highCap_sliced_multifold_stage_supported_budget vs tooth_highCap_nv25_stage1_multifold_at_193_bits

#verify_inhabited Qsag.highCap_cwyz26_johnson_cascade_cert_nv2_to_28 inhabited_highCap_cwyz26_johnson_cert_nv28
#verify_inhabited Qsag.highCap_cwyz26_johnson_cascade_cert_nv2_to_28 inhabited_highCap_cwyz26_johnson_cert_nv25
#tooth_pair Qsag.highCap_cwyz26_johnson_cascade_cert_nv2_to_28 vs tooth_highCap_nv28_gs_dim_rejects_sudan_m1
#tooth_pair Qsag.highCap_cwyz26_johnson_cascade_cert_nv2_to_28 vs tooth_highCap_hemStageGeoms_nv29_empty

#verify_inhabited Qsag.highCap_gs_interpolation_dimensions_nv2_to_28 inhabited_highCap_cwyz26_johnson_cert_nv28
#tooth_pair Qsag.highCap_gs_interpolation_dimensions_nv2_to_28 vs tooth_highCap_nv28_gs_dim_rejects_sudan_m1

#verify_inhabited Qsag.highCap_sliced_three_challenge_stage_supported_budget inhabited_highCap_cwyz26_johnson_cert_nv28
#tooth_pair Qsag.highCap_sliced_three_challenge_stage_supported_budget vs tooth_highCap_nv28_three_challenge_at_183_bits

#tooth_pair highCap_witness_rows_pass_johnson_check vs tooth_highCap_johnson_check_rejects_low_agreement

end HemHighCapSlicedBudgetTests
end Qsag
end
