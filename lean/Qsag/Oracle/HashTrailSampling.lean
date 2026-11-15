module
/-
# Sampling boundary for S-box trail products

Actual S-box root bounds do multiply in the explicit experiment below: each
active gate receives a fresh independent field input. This is not the input
experiment of a fixed permutation, whose gates share a single initial state.
The second result exhibits that obstruction without a cryptographic assumption.
-/
public import Qsag.Oracle.ParallelSeededSpnSecurity
import all Qsag.Oracle.ParallelSeededSpnSecurity

public section
namespace Qsag
set_option autoImplicit false

/-- Cartesian prefixing: each fresh choice is paired with every remaining assignment. -/
def prefixAssignments {α : Type} (choices : List α) (tails : List (List α)) : List (List α) :=
  choices.flatMap fun x => tails.map (x :: ·)

theorem prefixAssignments_length {α : Type} (choices : List α) (tails : List (List α)) :
    (prefixAssignments choices tails).length = choices.length * tails.length := by
  induction choices with
  | nil => simp [prefixAssignments]
  | cons x xs ih =>
    simp only [prefixAssignments, List.flatMap_cons, List.length_append, List.length_map]
    change tails.length + (prefixAssignments xs tails).length = _
    rw [ih, List.length_cons, Nat.succ_mul, Nat.add_comm]

/-- Uniform Cartesian sample space: a fresh choice at every gate. -/
def freshInputAssignments {α : Type} (inputs : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => prefixAssignments inputs (freshInputAssignments inputs n)

theorem freshInputAssignments_length {α : Type} (inputs : List α) (n : Nat) :
    (freshInputAssignments inputs n).length = inputs.length ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [freshInputAssignments, prefixAssignments_length, ih, Nat.pow_succ, Nat.mul_comm]

/-- All successful assignments in an experiment with one fresh input per active gate.
    Each gate specifies its nonzero input difference and desired output difference. -/
def freshSboxAssignments (inputs : List Tower128) :
    List (Tower128 × Tower128) → List (List Tower128)
  | [] => [[]]
  | (delta, outDiff) :: gates =>
    prefixAssignments
      (inputs.filter fun x => decide
        (towerAdd 7 (towerSbox7 7 (towerAdd 7 x delta)) (towerSbox7 7 x) = outDiff))
      (freshSboxAssignments inputs gates)

/-- Component root bounds give an actual cardinality bound for the fresh-input experiment.
    Its uniform Cartesian sample space has `inputs.length ^ gates.length` elements, so the
    success fraction is at most `6^gates.length / inputs.length^gates.length` when nonempty.
    No corresponding independence assertion is made for the deployed fixed SPN. -/
theorem freshSboxAssignments_length_le (inputs : List Tower128) (hNd : inputs.Nodup)
    (gates : List (Tower128 × Tower128))
    (hNonzero : ∀ gate ∈ gates, gate.1 ≠ towerZero 7) :
    (freshSboxAssignments inputs gates).length ≤ 6 ^ gates.length := by
  induction gates with
  | nil => simp [freshSboxAssignments]
  | cons gate gates ih =>
    rcases gate with ⟨delta, outDiff⟩
    rw [freshSboxAssignments, prefixAssignments_length]
    have hRoot := towerSbox7_differential_uniformity_le_six 7 delta outDiff
      (hNonzero (delta, outDiff) (by simp)) inputs hNd
    have hTail := ih (fun gate hg => hNonzero gate (List.mem_cons_of_mem _ hg))
    simpa [Nat.pow_succ, Nat.mul_comm] using Nat.mul_le_mul hRoot hTail

/-- Reusing one input at two identical tests does not square its acceptance fraction.
    This small exact experiment has each marginal `1/2`, but joint probability `1/2 > 1/4`. -/
theorem repeated_test_does_not_multiply :
    ([false, true].filter id).length = 1 ∧
    ([false, true].filter fun b => b && b).length = 1 ∧
    1 * 2 < 1 * 4 := by decide

/-- A realized trace on a finite uniform input space has at least one accepting input. -/
theorem realized_trace_has_positive_count {α β : Type} [DecidableEq β]
    (coins : List α) (trace : α → β) (x : α) (hx : x ∈ coins) :
    0 < (coins.filter fun y => decide (trace y = trace x)).length := by
  have hm : x ∈ coins.filter (fun y => decide (trace y = trace x)) := by
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨hx, trivial⟩
  cases he : coins.filter (fun y => decide (trace y = trace x)) with
  | nil => rw [he] at hm; cases hm
  | cons a rest => simp

/-- No bound strictly below one atom can bound every realized deterministic trace.
    The inequality `num * coins.length < den` says `num/den < 1/coins.length`.
    The rejected inequality is the cross-multiplied claim that this trace has probability
    at most `num/den`. This applies to any actual fixed-round SPN/Poseidon trace function. -/
theorem realized_trace_refutes_subatom_bound {α β : Type} [DecidableEq β]
    (coins : List α) (trace : α → β) (x : α) (hx : x ∈ coins)
    (num den : Nat) (hSmall : num * coins.length < den) :
    ¬ (coins.filter fun y => decide (trace y = trace x)).length * den ≤ num * coins.length := by
  have hPositive := realized_trace_has_positive_count coins trace x hx
  have hFloor : den ≤ (coins.filter fun y => decide (trace y = trace x)).length * den := by
    simpa using Nat.mul_le_mul_right den hPositive
  omega

/-- Differential trajectory of the actual 48-round tower SPN with fixed constants. -/
def fixedSpnDifferenceTrace (mdsA mdsB : Tower128) (rcs : Nat → Tower128 × Tower128)
    (delta input : Tower128 × Tower128) : List (Tower128 × Tower128) :=
  (List.range 49).map fun r =>
    let a := spnIterRounds128 mdsA mdsB rcs r input
    let b := spnIterRounds128 mdsA mdsB rcs r
      (towerAdd 7 input.1 delta.1, towerAdd 7 input.2 delta.2)
    (towerAdd 7 a.1 b.1, towerAdd 7 a.2 b.2)

/-- Concrete obstruction to interpreting the arithmetic product as a fixed-SPN trail bound.
    On a uniform sample list of size `2^256`, every realized differential trajectory has mass
    at least `2^-256`, strictly greater than `(6/2^128)^48`. This does not challenge the valid
    active-box theorem or the separate fresh-input experiment above. -/
theorem fixedSpnDifferenceTrace_not_bounded_by_component_product
    (mdsA mdsB : Tower128) (rcs : Nat → Tower128 × Tower128)
    (delta input : Tower128 × Tower128) (coins : List (Tower128 × Tower128))
    (hSize : coins.length = 2 ^ 256) (hInput : input ∈ coins) :
    ¬ (coins.filter fun x => decide
      (fixedSpnDifferenceTrace mdsA mdsB rcs delta x =
        fixedSpnDifferenceTrace mdsA mdsB rcs delta input)).length * (2 ^ 128) ^ 48 ≤
      6 ^ 48 * coins.length := by
  apply realized_trace_refutes_subatom_bound coins
    (fixedSpnDifferenceTrace mdsA mdsB rcs delta) input hInput
  rw [hSize]
  decide

end Qsag
end

#verify_constructive
  Qsag.freshSboxAssignments_length_le
  Qsag.realized_trace_refutes_subatom_bound
  Qsag.fixedSpnDifferenceTrace_not_bounded_by_component_product
