module
/-
# Qsag.Machine.Tactic.KernelRfl — `kernel_rfl`

`by kernel_rfl` closes a goal `a = b` by assigning the proof term `Eq.refl a` without running the
elaborator's definitional-equality check. Whether `a` and `b` are definitionally equal is decided
by the kernel when the enclosing declaration is added, so a goal that is not a definitional
equality is rejected there. The tactic adds no axioms.

It is for closed-form evaluations whose statement has free variables (so `decide` does not apply)
and whose reduction is too slow in the elaborator.
-/

public meta import Lean

public section

namespace Qsag.Machine.Tactic
open Lean Meta Elab Tactic

/-- Close `a = b` with `Eq.refl a`; the definitional equality is checked by the kernel only. -/
elab "kernel_rfl" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (α, a, _) := t.eq? | throwError "kernel_rfl: equality expected"
  g.assign (mkApp2 (mkConst ``Eq.refl [← getLevel α]) α a)

end Qsag.Machine.Tactic
end
