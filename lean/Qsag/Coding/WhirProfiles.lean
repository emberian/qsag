module
/- Arithmetic data and executable side-condition checks for WHIR profiles.

The finite checker is a computational API: consumers calculate profile coverage from these
Nat-valued definitions. Algebraic soundness of a passing witness remains in `Cwyz26`.
-/
public import Qsag.Math.Counting
public section
namespace Qsag
set_option autoImplicit false
set_option exponentiation.threshold 2048

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
@[expose] def interpUnknownsAux (mA_sub_D d D : Nat) : Nat → Nat
  | 0 => mA_sub_D * (D + 1)
  | j + 1 => interpUnknownsAux mA_sub_D d D j + (mA_sub_D - d * (j + 1)) * (D - (j + 1) + 1)

/-- Primitive-recursive accumulator for the per-point equation count
    `∑_{s=0}^K (m - s) (D - s + 1)` in `[CWYZ26]` Equation `(4.2)` / `(4.5)`. -/
@[expose] def interpEquationsAux (m D : Nat) : Nat → Nat
  | 0 => m * (D + 1)
  | s + 1 => interpEquationsAux m D s + (m - (s + 1)) * (D - (s + 1) + 1)

/-- Exact ceiling `⌈a / b⌉` for `b > 0`. -/
@[expose] def natCeilDiv (a b : Nat) : Nat :=
  (a + b - 1) / b

/-- Conservative `1/q`-scaled numerator `s_i * (ℓ + 2 ℓ₀ + 1)` for `[CWYZ26]` Theorem 4.8 + Theorem 5.1
    (`Eq. 5.7`, equal-degree affine folding **with linear claims** across `s_i` binary folds), valid
    whenever `checkWhirAffineWitness w q = true` (`nonpersCeil ≤ q` and `n(n-1)/2 ≤ q`). This is the
    quantity `loss * (list + 2 * list0 + 1)` of `affine_schedule.rs`. -/
@[expose] def whirAffineStageSimpleNum (w : WhirAffineWitness) : Nat :=
  let ell := (w.n * (w.B - w.d - 1)) / (w.B * w.B - w.n * (w.d + 1))
  let ell0 := (w.n * (w.A - 1 - w.d)) / ((w.A - 1) * (w.A - 1) - w.n * w.d)
  w.sFolds * (ell + 2 * ell0 + 1)

/-- Exact `q^2`-scaled numerator from `[CWYZ26]` Theorem 4.8 (`Eq. 4.13`) + Theorem 5.1 (`Eq. 5.7`)
    across `w.sFolds` folds over a field of cardinality `q`. -/
@[expose] def whirAffineStageExactNumQ2 (w : WhirAffineWitness) (q : Nat) : Nat :=
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
@[expose] def checkWhirAffineWitness (w : WhirAffineWitness) (q : Nat) : Bool :=
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

/-- Mirror of `pcs.rs::stage_geometry`: `(log₂ blowup, step_vars)` of every WHIR stage. -/
@[expose] def hemStageGeometry (nv : Nat) : List (Nat × Nat) :=
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
  else if nv ≤ 24 then [(2, 6), (4, 4), (6, 3), (8, 3)]
  else if nv = 25 then [(2, 6), (4, 4), (6, 4), (8, 3)]
  else if nv = 26 then [(2, 6), (4, 5), (6, 4), (8, 3)]
  else if nv = 27 then [(2, 6), (4, 5), (6, 4), (8, 4)]
  else if nv = 28 then [(2, 6), (4, 6), (6, 4), (8, 4)]
  else []

/-- Mirror of the `early_stop_vars` field produced by `pcs.rs::stage_geometry`. -/
@[expose] def hemEarlyStopVars (nv : Nat) : Nat :=
  if nv ≤ 3 then 1 else if nv ≤ 6 then 2 else if nv ≤ 8 then 3 else if nv ≤ 13 then 4
  else if nv ≤ 15 then 5 else if nv ≤ 16 then 6 else if nv ≤ 20 then nv - 12
  else if nv = 23 then 7 else 8

/-- Mirror of `WhirSecurityRegime::minimum_queries` for the two unconditional Johnson regimes:
    `BciksJohnsonQrom128` uses `⌈512 / log₂ B⌉ + 2`, `BciksJohnsonClassical128` uses
    `⌈256 / log₂ B⌉ + 1`. -/
@[expose] def hemJohnsonMinQueries (isQrom : Bool) (logBlowup : Nat) : Nat :=
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

@[expose] def hemStageGeomsAux : Nat → Nat → List (Nat × Nat) → List HemStageGeom
  | _, _, [] => []
  | idx, rem, (lb, sv) :: rest =>
    { stageIdx := idx, logBlowup := lb, stepVars := sv,
      n := 2 ^ lb * 2 ^ (rem - sv), d := 2 ^ (rem - sv) + 2 } ::
      hemStageGeomsAux (idx + 1) (rem - sv) rest

@[expose] def hemStageGeoms (nv : Nat) : List HemStageGeom :=
  hemStageGeomsAux 0 nv (hemStageGeometry nv)

/-- Mirror of `WhirSchedule::validate` on the canonical geometry: at most `4` stages, blowups in
    `{4, 16, 64, 256}`, every stage folds `1..6` variables and strictly fewer than remain, and
    `early_stop_vars + ∑ step_vars = num_vars` with `1 ≤ early_stop_vars ≤ 8`. -/
@[expose] def hemStageGeometryValid (nv : Nat) : Bool :=
  let g := hemStageGeometry nv
  decide (1 ≤ g.length ∧ g.length ≤ 4) &&
  g.all (fun p => (p.1 == 2 || p.1 == 4 || p.1 == 6 || p.1 == 8) &&
    decide (1 ≤ p.2 ∧ p.2 ≤ 6)) &&
  decide (hemEarlyStopVars nv + (g.map (·.2)).sum = nv) &&
  decide (1 ≤ hemEarlyStopVars nv ∧ hemEarlyStopVars nv ≤ 8)

/-- Explicit `25..=28` stage geometries of `pcs.rs::stage_geometry`, and rejection above
    `MAX_PCS_NUM_VARS = 28`. -/
theorem hemStageGeometry_nv25_to_28 :
    hemStageGeometry 25 = [(2, 6), (4, 4), (6, 4), (8, 3)] ∧
    hemStageGeometry 26 = [(2, 6), (4, 5), (6, 4), (8, 3)] ∧
    hemStageGeometry 27 = [(2, 6), (4, 5), (6, 4), (8, 4)] ∧
    hemStageGeometry 28 = [(2, 6), (4, 6), (6, 4), (8, 4)] ∧
    ∀ nv : Nat, 29 ≤ nv → hemStageGeometry nv = [] := by
  refine ⟨by decide, by decide, by decide, by decide, fun nv h29 => ?_⟩
  unfold hemStageGeometry
  have h6 : ¬ nv ≤ 6 := by omega
  have h11 : ¬ nv ≤ 11 := by omega
  have h16 : ¬ nv ≤ 16 := by omega
  have h20 : ¬ nv ≤ 20 := by omega
  have h21 : ¬ nv = 21 := by omega
  have h22 : ¬ nv = 22 := by omega
  have h24 : ¬ nv ≤ 24 := by omega
  have h25 : ¬ nv = 25 := by omega
  have h26 : ¬ nv = 26 := by omega
  have h27 : ¬ nv = 27 := by omega
  have h28 : ¬ nv = 28 := by omega
  simp only [h6, h11, h16, h20, h21, h22, h24, h25, h26, h27, h28, ↓reduceIte]

/-- Folding-sum conservation `early_stop_vars + ∑ step_vars = nv` across every supported
    `nv ∈ 2..=28` (`MAX_PCS_NUM_VARS = 28`). -/
theorem hemStageGeometry_folding_sum_nv2_to_28 (nv : Nat) (h2 : 2 ≤ nv) (h28 : nv ≤ 28) :
    hemEarlyStopVars nv + ((hemStageGeometry nv).map (·.2)).sum = nv := by
  have hAll : ((List.range 27).all fun i =>
      decide (hemEarlyStopVars (i + 2) + ((hemStageGeometry (i + 2)).map (·.2)).sum = i + 2)) =
      true := by
    decide +kernel
  have h1 := List.all_eq_true.mp hAll (nv - 2) (List.mem_range.mpr (by omega))
  have hEq : nv - 2 + 2 = nv := by omega
  rw [hEq] at h1
  exact of_decide_eq_true h1

/-- Stage-validity certificate across every supported `nv ∈ 2..=28`: `hemStageGeometryValid`
    holds, every stage domain `blowup · 2^remaining` is at most `2^31`, and every stage folds
    strictly fewer variables than remain (`d = 2^rem + 2 ≥ 4`). -/
theorem hemStageGeometryValid_nv2_to_28 (nv : Nat) (h2 : 2 ≤ nv) (h28 : nv ≤ 28) :
    hemStageGeometryValid nv = true ∧
    ∀ g ∈ hemStageGeoms nv, g.n * 2 ^ g.stepVars ≤ 2 ^ 31 ∧ 4 ≤ g.d := by
  have hAll : ((List.range 27).all fun i =>
      hemStageGeometryValid (i + 2) &&
      (hemStageGeoms (i + 2)).all (fun g => decide (g.n * 2 ^ g.stepVars ≤ 2 ^ 31 ∧ 4 ≤ g.d))) =
      true := by
    decide +kernel
  have h1 := List.all_eq_true.mp hAll (nv - 2) (List.mem_range.mpr (by omega))
  have hEq : nv - 2 + 2 = nv := by omega
  rw [hEq, Bool.and_eq_true] at h1
  exact ⟨h1.1, fun g hg => of_decide_eq_true (List.all_eq_true.mp h1.2 g hg)⟩

/-- Above `MAX_PCS_NUM_VARS = 28`, `hemStageGeometryValid` rejects (`hemStageGeometry nv = []`). -/
theorem hemStageGeometryValid_false_of_ge_29 (nv : Nat) (h29 : 29 ≤ nv) :
    hemStageGeometryValid nv = false := by
  unfold hemStageGeometryValid
  rw [hemStageGeometry_nv25_to_28.2.2.2.2 nv h29]
  rfl

end Qsag
end
