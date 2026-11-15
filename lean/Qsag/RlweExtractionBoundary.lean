module
/-
# The norm boundary of the production fork-extraction relation

The extraction dichotomy is valid algebra. Its SIS branch must not be interpreted as
an established hard problem solely because its infinity norm is below q/2.
At bound 6144 it has a deterministic solution for every A; at bound 6142 the same
solver fails only if a coefficient is in four exceptional residue classes.
These are statements about the reduction target, not forged OR-Sigma transcripts.
-/
public import Qsag.RlweCyclotomicExtraction
import all Qsag.RlweCyclotomicExtraction
public import Qsag.Tactic.AssuranceKit
public section
namespace Qsag
set_option autoImplicit false

/-- Explicit nonzero candidate `(1, centered(-A))`. -/
def rlweUnitSisError (A : CycPolyZq 10 12289) : CycPolyInt 10 :=
  cycZqCentered (cycZqNeg A)

theorem rlweUnitSis_relation (A : CycPolyZq 10 12289) :
    cycIntToZq 12289 (@cycIntOne 1024) ≠ cycZqZero ∧
    cycIntInfNorm (@cycIntOne 1024) ≤ 1 ∧
    cycZqAdd (cycZqMul A (cycIntToZq 12289 (@cycIntOne 1024)))
      (cycIntToZq 12289 (rlweUnitSisError A)) = cycZqZero := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h0 := congrFun h ⟨0, by decide⟩
    have hv := congrArg ModZq.val h0
    change 1 = 0 at hv
    omega
  · rw [cycIntInfNorm_le_iff]
    intro k
    unfold cycIntOne
    split <;> decide
  · rw [cycIntToZq_one, cycZqMul_one_right (by decide), rlweUnitSisError,
      cycIntToZq_centered]
    funext k
    unfold cycZqAdd cycZqNeg cycZqZero
    rw [← ModZq.ofInt_natVal (A k), ← ModZq.ofInt_neg, ← ModZq.ofInt_add]
    rw [show ((A k).val : Int) + -((A k).val : Int) = 0 by omega, ModZq.ofInt_zero]

theorem rlweUnitSis_norm_le_half_modulus (A : CycPolyZq 10 12289) :
    cycIntInfNorm (rlweUnitSisError A) ≤ 6144 := by
  rw [cycIntInfNorm_le_iff]
  intro k
  unfold rlweUnitSisError cycZqCentered ModZq.centered
  have h := (cycZqNeg A k).isLt
  split <;> omega

/-- Only four out of 12289 residues can obstruct this public candidate at bound 6142.
For independent uniform coefficients the exact success rate is `(12285/12289)^1024`.
The probability interpretation requires that distribution; this theorem is pointwise. -/
theorem rlweUnitSis_norm_le_6142
    (A : CycPolyZq 10 12289)
    (hAvoid : ∀ k, (cycZqNeg A k).val ≤ 6142 ∨ 6147 ≤ (cycZqNeg A k).val) :
    cycIntInfNorm (rlweUnitSisError A) ≤ 6142 := by
  rw [cycIntInfNorm_le_iff]
  intro k
  have h := (cycZqNeg A k).isLt
  have ha := hAvoid k
  unfold rlweUnitSisError cycZqCentered ModZq.centered
  split <;> omega

/-- The union-bound failure numerator is below one third of the denominator.
Together with four excluded residues per coefficient, this gives success > 2/3
under independent uniform A, without a large-power computation. -/
theorem rlweUnitSis_uniform_union_budget : 3 * (1024 * 4) < 12289 := by decide

#verify_constructive rlweUnitSis_relation rlweUnitSis_norm_le_half_modulus
  rlweUnitSis_norm_le_6142 rlweUnitSis_uniform_union_budget
end Qsag
end
