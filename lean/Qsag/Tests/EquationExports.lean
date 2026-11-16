module
public import Qsag.Tests.EquationExportOwner
public import Qsag.Tactic.AssuranceKit

/-! These calculations use only the selected public equations, across a normal import. -/
public section
namespace Qsag.EquationExportFixture
set_option autoImplicit false

theorem arithmetic_public (n : Nat) : arithmetic n = n + 2 := by
  fail_if_success rfl
  simp only [arithmetic.public_eqs]
theorem listSum_public_nil : listSum [] = 0 := by simp only [listSum.public_eqs]
theorem listSum_public_cons (n : Nat) (xs : List Nat) :
    listSum (n :: xs) = n + listSum xs := by simp only [listSum.public_eqs]

theorem innerMatch_public_nil : innerMatch [] = 0 := by
  simp only [innerMatch.public_eqs, List.head?_nil]
theorem innerMatch_public_cons (n : Nat) (xs : List Nat) :
    innerMatch (n :: xs) = n + 1 := by
  simp only [innerMatch.public_eqs, List.head?_cons]

theorem importedMatch_boundary (xs : List Nat) : importedMatch xs = importedMatch xs := rfl

#verify_constructive importedMatch_boundary arithmetic_public listSum_public_nil listSum_public_cons
  innerMatch_public_nil innerMatch_public_cons
private def hidden (n : Nat) : Nat := n + 1
def usesHidden (n : Nat) : Nat := hidden n

/-- error: The definition must be public: Qsag.EquationExportFixture.hidden -/
#guard_msgs in
#export_eqns hidden

/-- error: Export equations in the definition's owning module: Nat.add -/
#guard_msgs in
#export_eqns Nat.add

/-- error: Equation type exposes a private helper Qsag.EquationExportFixture.hidden; write a projection lemma instead -/
#guard_msgs in
#export_eqns usesHidden

end Qsag.EquationExportFixture
end
