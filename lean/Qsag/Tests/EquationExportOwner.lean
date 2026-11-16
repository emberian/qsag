module
public import Qsag.Tactic.AssuranceKit

/-! Ordinary and recursive equations used by the normal-import consumer regression. -/
public section
namespace Qsag.EquationExportFixture
set_option autoImplicit false

def arithmetic (n : Nat) : Nat := n + 2

def listSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + listSum xs

def innerMatch (xs : List Nat) : Nat :=
  match xs.head? with
  | none => 0
  | some n => n + 1

@[expose] def importedMatch (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | [n] => n
  | a :: b :: _ => a + b

#export_eqns arithmetic listSum innerMatch
end Qsag.EquationExportFixture
end
