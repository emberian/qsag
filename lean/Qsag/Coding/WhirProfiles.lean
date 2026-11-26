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


/-- Mirror of the `early_stop_vars` field produced by `pcs.rs::stage_geometry`. -/
@[expose] def hemEarlyStopVars (nv : Nat) : Nat :=
  if nv ≤ 3 then 1 else if nv ≤ 6 then 2 else if nv ≤ 8 then 3 else if nv ≤ 13 then 4
  else if nv ≤ 15 then 5 else if nv ≤ 16 then 6 else if nv ≤ 20 then nv - 12
  else if nv = 23 then 7 else 8


end Qsag
end
