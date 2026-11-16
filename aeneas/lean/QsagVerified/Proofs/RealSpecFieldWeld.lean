module
import all QsagVerified.Funs

public import QsagVerified.Proofs.Goldilocks
public import QsagVerified.Proofs.MirRefinementKit
public import Qsag.Exec.SimulationSpine
public import Qsag.Math.Goldilocks

/-!
# Field-kernel weld between the Aeneas extraction and `Qsag.Goldilocks`

Imports `QsagVerified.Funs` (through the proof modules) and the `Qsag` specification modules
`Qsag.Goldilocks` and `Qsag.SimulationSpine` into one kernel environment. `qsag_aeneas` requires
the `qsag` Lake package (`aeneas/lean/lakefile.toml`); nothing in `qsag` imports the extraction.

Contents: `extractedPartyMachine`, which views an extracted step function as a
`Qsag.PartyMachine` with no intermediate model; `ExtractedStepRefines`, the exact-step statement
every guard weld proves, with its lockstep `ForwardSim`; and refinement theorems from the extracted
`goldilocks_add`, `goldilocks_sub` and `goldilocks_mul` to `Qsag.Goldilocks.add`, `.sub`, `.mul`.
These statements concern the extracted verified-crate functions. Production's distinct
wrapping/overflowing arithmetic is not extracted here; a Cargo dependency alone does not
transfer these theorems to that implementation. KoalaBear has no declaration in the current
`QsagVerified.Funs` extraction. Inversion below additionally uses the canonical prime-field law.
This module depends on none of the large protocol modules, so it builds whenever
`Qsag.Goldilocks` does. The guard welds are in `AuthenticatedBeltAndRealSpecWeld.lean` and
`RealSpecGuardBoundary.lean`.
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

/-- A trace of the pulled-back machine is a trace of the original on the encoded inputs. -/
theorem comapInputs_validTrace {S In In' Out : Type} {A : Qsag.PartyMachine S In Out}
    {encIn : In' → In} {s s' : S} {tr : List (In' × Out)}
    (h : (comapInputs A encIn).ValidTrace s tr s') :
    A.ValidTrace s (tr.map fun p => (encIn p.1, p.2)) s' := by
  induction h with
  | nil s => exact .nil s
  | accept hStep _ ih => exact .accept hStep ih
  | reject inp hNone _ ih => exact .reject (encIn inp) hNone ih

/-- The step-exactness statement every guard weld proves: on each state and input the extracted
    function returns normally, an accepted result is the spec step on the abstracted state and
    input, and a rejected result is the spec's rejection with the abstracted post-state. -/
@[expose]
def ExtractedStepRefines {M I O E S I' O' : Type}
    (f : M → I → Result (M × core.result.Result O E)) (encOut : O → O')
    (A : Qsag.PartyMachine S I' O') (absSt : M → S) (absIn : I → I') : Prop :=
  ∀ c i, match f c i with
    | .ok (c', .Ok o) => A.step (absSt c) (absIn i) = some (absSt c', encOut o)
    | .ok (c', .Err _) =>
      A.step (absSt c) (absIn i) = none ∧ A.errStep (absSt c) (absIn i) = absSt c'
    | _ => False

/-- Exact step refinement gives a lockstep forward simulation whose relation is the graph of the
    state abstraction. -/
@[expose]
def ExtractedStepRefines.forwardSim {M I O E S I' O' : Type}
    {f : M → I → Result (M × core.result.Result O E)} {encOut : O → O'}
    {A : Qsag.PartyMachine S I' O'} {absSt : M → S} {absIn : I → I'}
    (h : ExtractedStepRefines f encOut A absSt absIn) :
    Qsag.ForwardSim (extractedPartyMachine f encOut) (comapInputs A absIn) where
  Rel c a := a = absSt c
  sim_ok {c c' a inp out} hRel hStepC := by
    subst hRel
    have hc := h c inp
    dsimp only [extractedPartyMachine, comapInputs] at hStepC ⊢
    cases hf : f c inp with
    | ok p =>
      rcases p with ⟨m1, o | e⟩ <;> rw [hf] at hc hStepC <;> dsimp only at hc hStepC
      · simp only [Option.some.injEq, Prod.mk.injEq] at hStepC
        obtain ⟨rfl, rfl⟩ := hStepC
        rw [hc]
        exact ⟨rfl, rfl⟩
      · cases hStepC
    | fail _ => rw [hf] at hStepC; cases hStepC
    | div => rw [hf] at hStepC; cases hStepC
  sim_err {c a inp} hRel hNoneC := by
    subst hRel
    have hc := h c inp
    dsimp only [extractedPartyMachine, comapInputs] at hNoneC ⊢
    cases hf : f c inp with
    | ok p =>
      rcases p with ⟨m1, o | e⟩ <;> rw [hf] at hc hNoneC <;> dsimp only at hc hNoneC ⊢
      · cases hNoneC
      · exact hc
    | fail _ => rw [hf] at hc; exact False.elim hc
    | div => rw [hf] at hc; exact False.elim hc

/-- Under exact step refinement, a spec rejection is an extracted rejection. -/
theorem ExtractedStepRefines.step_none {M I O E S I' O' : Type}
    {f : M → I → Result (M × core.result.Result O E)} {encOut : O → O'}
    {A : Qsag.PartyMachine S I' O'} {absSt : M → S} {absIn : I → I'}
    (h : ExtractedStepRefines f encOut A absSt absIn) {c : M} {i : I}
    (hA : A.step (absSt c) (absIn i) = none) :
    (extractedPartyMachine f encOut).step c i = none := by
  have hc := h c i
  dsimp only [extractedPartyMachine]
  cases hf : f c i with
  | ok p =>
    rcases p with ⟨m1, o | e⟩
    · rw [hf] at hc; dsimp only at hc; rw [hA] at hc; cases hc
    · rfl
  | fail _ => rfl
  | div => rfl

/-! ## 2. Goldilocks field kernels against `Qsag.Goldilocks` -/

/-- The canonical field element denoted by an extracted `u64` Goldilocks word. -/
@[expose] def goldilocksAbs (x : goldilocks.Goldilocks) : Qsag.Goldilocks :=
  Qsag.Goldilocks.ofNat x.val

/-- Public value equation for consumers composing field refinements. -/
theorem goldilocksAbs_val (x : goldilocks.Goldilocks) :
    (goldilocksAbs x).val = x.val % Qsag.goldilocksPrime := rfl

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


/-- The extracted Fermat chain denotes the canonical inverse, including zero. -/
theorem goldilocks_inv_or_zero_refines_qsag (a : goldilocks.Goldilocks) :
    ∃ y, goldilocks.goldilocks_inv_or_zero a = .ok y ∧
      goldilocksAbs y = Qsag.Goldilocks.inv (goldilocksAbs a) ∧
      y.val < Qsag.goldilocksPrime := by
  obtain ⟨y, hy, hv, hlt, hz⟩ := goldilocks_inv_or_zero_spec a
  rw [goldilocksP_eq] at hv hlt hz
  refine ⟨y, hy, Qsag.Goldilocks.ext ?_, hlt⟩
  show y.val % Qsag.goldilocksPrime = (Qsag.Goldilocks.inv (goldilocksAbs a)).val
  rw [Nat.mod_eq_of_lt hlt]
  unfold Qsag.Goldilocks.inv
  by_cases ha : a.val % Qsag.goldilocksPrime = 0
  · have hav : (goldilocksAbs a).val = 0 := ha
    rw [ite_eq_left_of_eq_true _ _ (eq_true hav), hz ha]
    rfl
  · have hav : ¬ (goldilocksAbs a).val = 0 := ha
    rw [ite_eq_right_of_eq_false _ _ (eq_false hav), Qsag.Goldilocks.ofNat_val,
      Qsag.modPowFuel_eq_pow_mod 64 _ _ _ (by decide), Nat.mod_mod]
    exact hv

/-- Every nonzero residue has an extracted inverse whose *extracted* product is exactly
one. This discharges the mathematical inverse law, rather than only identifying an exponent. -/
theorem goldilocks_inverse_mul_eq_one (a : goldilocks.Goldilocks)
    (ha : a.val % GoldilocksP ≠ 0) :
    ∃ y, goldilocks.goldilocks_inv_or_zero a = .ok y ∧
      goldilocks.goldilocks_mul a y = .ok 1#u64 ∧ y ≠ 0#u64 := by
  obtain ⟨y, hy, habs, _⟩ := goldilocks_inv_or_zero_refines_qsag a
  have hane : goldilocksAbs a ≠ Qsag.Goldilocks.zero := by
    intro h
    exact ha (congrArg Qsag.Goldilocks.val h)
  have hcancel : Qsag.Goldilocks.mul (goldilocksAbs a) (goldilocksAbs y) =
      Qsag.Goldilocks.one := by
    rw [habs]
    exact Qsag.Goldilocks.mul_inv_cancel hane
  obtain ⟨z, hz, hzabs, hzlt⟩ := goldilocks_mul_refines_qsag a y
  have hzval := congrArg Qsag.Goldilocks.val (hzabs.trans hcancel)
  change z.val % Qsag.goldilocksPrime = 1 at hzval
  rw [Nat.mod_eq_of_lt hzlt] at hzval
  have hz1 : z = 1#u64 := UScalar.eq_of_val_eq hzval
  refine ⟨y, hy, hz1 ▸ hz, ?_⟩
  intro hy0
  have hc := congrArg Qsag.Goldilocks.val hcancel
  rw [Qsag.Goldilocks.mul_val, hy0] at hc
  change ((goldilocksAbs a).val * (0 % Qsag.goldilocksPrime)) %
    Qsag.goldilocksPrime = 1 at hc
  simp at hc

/-- Exact option behavior: `none` occurs precisely for the zero residue, with no
unresolved alternative allowing a nonzero input's inverse to vanish. -/
theorem goldilocks_inv_none_iff_zero (a : goldilocks.Goldilocks) :
    goldilocks.goldilocks_inv a = .ok none ↔ a.val % GoldilocksP = 0 := by
  obtain ⟨y, hy, hnone, _⟩ := goldilocks_inv_spec a
  rw [hnone]
  constructor
  · intro h
    rcases h with hz | hy0
    · exact hz
    · by_cases hn : a.val % GoldilocksP = 0
      · exact hn
      · obtain ⟨z, hz, _, hzne⟩ := goldilocks_inverse_mul_eq_one a hn
        have heq : y = z := Result.ok.inj (hy.symm.trans hz)
        exact False.elim (hzne (heq ▸ hy0))
  · exact Or.inl

/-- Nonzero inputs return `some` and satisfy the canonical inverse law in MIR. -/
theorem goldilocks_inv_some_mul_eq_one (a : goldilocks.Goldilocks)
    (ha : a.val % GoldilocksP ≠ 0) :
    ∃ y, goldilocks.goldilocks_inv a = .ok (some y) ∧
      goldilocks.goldilocks_mul a y = .ok 1#u64 := by
  obtain ⟨y, hy, hmul, hne⟩ := goldilocks_inverse_mul_eq_one a ha
  refine ⟨y, ?_, hmul⟩
  simp [goldilocks.goldilocks_inv, hy, hne]

end qsag_verified.proofs
