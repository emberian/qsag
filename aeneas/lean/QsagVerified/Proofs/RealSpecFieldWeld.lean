module

public import QsagVerified.Proofs.Goldilocks
public import QsagVerified.Proofs.MirRefinementKit
public import Qsag.SimulationSpine
public import Qsag.Goldilocks

/-!
# Field-kernel weld between the Aeneas extraction and `Qsag.Goldilocks`

Imports `QsagVerified.Funs` (through the proof modules) and the `Qsag` specification modules
`Qsag.Goldilocks` and `Qsag.SimulationSpine` into one kernel environment. `qsag_aeneas` requires
the `qsag` Lake package (`aeneas/lean/lakefile.toml`); nothing in `qsag` imports the extraction.

Contents: `extractedPartyMachine`, which views an extracted step function as a
`Qsag.PartyMachine` with no intermediate model, and refinement theorems from the extracted
`goldilocks_add`, `goldilocks_sub` and `goldilocks_mul` to `Qsag.Goldilocks.add`, `.sub`, `.mul`.
This module depends on none of the large protocol modules, so it builds whenever
`Qsag.Goldilocks` does. The guard welds are in `AuthenticatedBeltAndRealSpecWeld.lean`.
-/

public section

namespace qsag_verified.proofs

open Aeneas Aeneas.Std Result
open qsag_verified

/-! ## 1. Extracted step functions as `Qsag.PartyMachine`s -/

/-- An Aeneas-extracted transition `fn step(self, i) -> (Self, Result<O, E>)` viewed as a
    `Qsag.PartyMachine`. Accepted outputs are re-typed by `encOut`; a rejection keeps the state the
    extracted function returned. A panic or divergence would be a rejection that keeps the old
    state; the simulation theorems below show the welded functions never take that branch. -/
@[expose]
def extractedPartyMachine {M I O O' E : Type}
    (f : M → I → Result (M × core.result.Result O E)) (encOut : O → O') :
    Qsag.PartyMachine M I O' where
  step m i :=
    match f m i with
    | .ok (m', .Ok o) => some (m', encOut o)
    | _ => none
  errStep m i :=
    match f m i with
    | .ok (m', _) => m'
    | _ => m

/-- Pull a `Qsag.PartyMachine` back along an encoding of inputs. -/
@[expose]
def comapInputs {S In In' Out : Type} (A : Qsag.PartyMachine S In Out) (encIn : In' → In) :
    Qsag.PartyMachine S In' Out where
  step s i := A.step s (encIn i)
  errStep s i := A.errStep s (encIn i)

/-! ## 2. Goldilocks field kernels against `Qsag.Goldilocks` -/

/-- The canonical field element denoted by an extracted `u64` Goldilocks word. -/
def goldilocksAbs (x : goldilocks.Goldilocks) : Qsag.Goldilocks :=
  Qsag.Goldilocks.ofNat x.val

private theorem goldilocksP_eq : GoldilocksP = Qsag.goldilocksPrime := rfl

/-- Extracted `goldilocks_add` computes `Qsag.Goldilocks.add` and returns a canonical word. -/
theorem goldilocks_add_refines_qsag (a b : goldilocks.Goldilocks) :
    ∃ y : goldilocks.Goldilocks,
      goldilocks.goldilocks_add a b = .ok y ∧
      goldilocksAbs y = Qsag.Goldilocks.add (goldilocksAbs a) (goldilocksAbs b) ∧
      y.val < Qsag.goldilocksPrime := by
  obtain ⟨y, hy, hv, hlt⟩ := goldilocks_add_spec a b
  rw [goldilocksP_eq] at hv hlt
  refine ⟨y, hy, Qsag.Goldilocks.ext ?_, hlt⟩
  rw [Qsag.Goldilocks.add_val]
  show y.val % Qsag.goldilocksPrime =
    (a.val % Qsag.goldilocksPrime + b.val % Qsag.goldilocksPrime) % Qsag.goldilocksPrime
  rw [hv, Nat.mod_mod]

/-- Extracted `goldilocks_sub` computes `Qsag.Goldilocks.sub` and returns a canonical word. -/
theorem goldilocks_sub_refines_qsag (a b : goldilocks.Goldilocks) :
    ∃ y : goldilocks.Goldilocks,
      goldilocks.goldilocks_sub a b = .ok y ∧
      goldilocksAbs y = Qsag.Goldilocks.sub (goldilocksAbs a) (goldilocksAbs b) ∧
      y.val < Qsag.goldilocksPrime := by
  obtain ⟨y, hy, hv, hlt⟩ := goldilocks_sub_spec a b
  rw [goldilocksP_eq] at hv hlt
  refine ⟨y, hy, Qsag.Goldilocks.ext ?_, hlt⟩
  rw [Qsag.Goldilocks.sub_val]
  show y.val % Qsag.goldilocksPrime =
    (a.val % Qsag.goldilocksPrime + Qsag.goldilocksPrime - b.val % Qsag.goldilocksPrime) %
      Qsag.goldilocksPrime
  rw [hv, Nat.mod_mod, Nat.add_comm Qsag.goldilocksPrime]

/-- Extracted `goldilocks_mul` computes `Qsag.Goldilocks.mul` and returns a canonical word. -/
theorem goldilocks_mul_refines_qsag (a b : goldilocks.Goldilocks) :
    ∃ y : goldilocks.Goldilocks,
      goldilocks.goldilocks_mul a b = .ok y ∧
      goldilocksAbs y = Qsag.Goldilocks.mul (goldilocksAbs a) (goldilocksAbs b) ∧
      y.val < Qsag.goldilocksPrime := by
  obtain ⟨y, hy, hv, hlt⟩ := goldilocks_mul_spec a b
  rw [goldilocksP_eq] at hv hlt
  refine ⟨y, hy, Qsag.Goldilocks.ext ?_, hlt⟩
  rw [Qsag.Goldilocks.mul_val]
  show y.val % Qsag.goldilocksPrime =
    (a.val % Qsag.goldilocksPrime * (b.val % Qsag.goldilocksPrime)) % Qsag.goldilocksPrime
  rw [hv, Nat.mod_mod]

/-- `#tooth`: the weld distinguishes operations. The extracted product of `2` and `3` denotes
    `6`, not their sum `5`. -/
theorem tooth_goldilocks_mul_weld_is_not_add :
    ∃ y, goldilocks.goldilocks_mul 2#u64 3#u64 = .ok y ∧
      (goldilocksAbs y).val = 6 ∧
      (Qsag.Goldilocks.add (goldilocksAbs 2#u64) (goldilocksAbs 3#u64)).val = 5 := by
  obtain ⟨y, hy, hAbs, _⟩ := goldilocks_mul_refines_qsag 2#u64 3#u64
  refine ⟨y, hy, ?_, ?_⟩
  · rw [hAbs, Qsag.Goldilocks.mul_val]
    decide
  · rw [Qsag.Goldilocks.add_val]
    decide

end qsag_verified.proofs
