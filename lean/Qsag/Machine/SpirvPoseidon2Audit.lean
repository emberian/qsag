module
/-
# Qsag.Machine.SpirvPoseidon2Audit — Functional Equivalence of Decoded `poseidon2_perm12.spv` Field Helpers

End-to-end constructive verification (`0 sorry`, `0 bv_decide`, `0 native_decide`, `0 Classical.choice`,
`axioms ⊆ {propext, Quot.sound}`) over the actual 5,478-word (`21,912`-byte) compiled Vulkan/SPIR-V 1.5
production shader `poseidon2Perm12SpvWords` (`SpirvFixtures.lean` + `SpirvSimt.lean`):

1. **Lossless Binary Decode & Branchless/Zero-LDS Profile (`poseidon2Spv_decodes_and_roundtrips`)**:
   Re-exports and composes the kernel-checked `poseidon2Spv_bundle_verified` certificate (`Eq.refl true`),
   certifying `SPIR-V 1.5`, capabilities `[.shader, .int64]`, `LocalSize 64 1 1`, zero `Workgroup`
   shared-memory variables, and branchless constant-time structure across all 9 secret-bearing
   Goldilocks/S-box helper functions (`%10, %15, %19, %22, %26, %30, %33, %40, %43`).
2. **First Binary-Shader-to-`Qsag.Goldilocks` Functional Equivalence (`poseidon2Spv_fp_helpers_refine_goldilocks`)**:
   Executes the decoded SPIR-V `SpirvFunction` bodies of `fp_reduce_u64` (`%10`), `fp_add` (`%15`),
   `fp_sub` (`%19`), and `fp_neg` (`%22`) from `poseidon2Perm12SpvWords` on a total interprocedural
   `Function`-frame operational semantics `evalSpirvScalarCall`, proving exact 64-bit functional
   equivalence against `goldilocksCanon64`, `Goldilocks.add`, `Goldilocks.sub`, and `Goldilocks.neg`
   for **all** `a, b : UInt64`!
-/

public import Qsag.Machine.SpirvFixtures
public import Qsag.Machine.SpirvSimt
import Qsag.Machine.Tactic.KernelRfl
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-! ## 1. Interprocedural `Function`-Frame Operational Semantics for Decoded SPIR-V Scalar Helpers -/

/-- Scalar SSA value in a SPIR-V helper frame (`64`-bit integer or boolean condition). -/
inductive SpirvScalarVal where
  | u64 (v : UInt64)
  | flag (b : Bool)
  deriving DecidableEq, Repr

/-- Association-list lookup keyed by `UInt32` SSA/slot IDs. -/
def assocLookupU32 {α : Type} (key : UInt32) : List (UInt32 × α) → Option α
  | [] => none
  | (k, v) :: rest => if k == key then some v else assocLookupU32 key rest

structure SpirvAssocFrame where
  ssa : List (UInt32 × SpirvScalarVal)
  slots : List (UInt32 × UInt64)

private def readAssocU64? (lookupConst : UInt32 → Option UInt64)
    (fr : SpirvAssocFrame) (id : UInt32) : Option UInt64 :=
  match assocLookupU32 id fr.ssa with
  | some (.u64 v) => some v
  | some (.flag _) => none
  | none => lookupConst id

private def readAssocFlag? (fr : SpirvAssocFrame) (id : UInt32) : Option Bool :=
  match assocLookupU32 id fr.ssa with
  | some (.flag b) => some b
  | _ => none

private def zipParamSlots : List (UInt32 × UInt32) → List UInt64 → Option (List (UInt32 × UInt64))
  | [], [] => some []
  | (_, pid) :: ps, v :: vs =>
    match zipParamSlots ps vs with
    | some tail => some ((pid, v) :: tail)
    | none => none
  | _, _ => none

private def readSlotArgs (slots : List (UInt32 × UInt64)) : List UInt32 → Option (List UInt64)
  | [] => some []
  | p :: ps =>
    match assocLookupU32 p slots, readSlotArgs slots ps with
    | some v, some vs => some (v :: vs)
    | _, _ => none

/-- Straight-line SPIR-V body interpreter parameterized by `callRec` so outer function unfolding
    never unfolds nested callees prematurely. -/
private def evalSpirvBody (lookupConst : UInt32 → Option UInt64)
    (callRec : UInt32 → List UInt64 → Option UInt64) :
    List SpirvInst → SpirvAssocFrame → Option UInt64
  | [], _ => none
  | inst :: rest, fr =>
    match inst with
    | .opLabel _ => evalSpirvBody lookupConst callRec rest fr
    | .opVariable _ res .function none =>
      evalSpirvBody lookupConst callRec rest { fr with slots := (res, 0) :: fr.slots }
    | .opLoad _ res ptr =>
      match assocLookupU32 ptr fr.slots with
      | some v => evalSpirvBody lookupConst callRec rest { fr with ssa := (res, .u64 v) :: fr.ssa }
      | none => none
    | .opStore ptr valId =>
      match readAssocU64? lookupConst fr valId with
      | some v => evalSpirvBody lookupConst callRec rest { fr with slots := (ptr, v) :: fr.slots }
      | none => none
    | .opFunctionCall _ res callee argPtrs =>
      match readSlotArgs fr.slots argPtrs with
      | none => none
      | some calleeArgs =>
        match callRec callee calleeArgs with
        | some retV => evalSpirvBody lookupConst callRec rest { fr with ssa := (res, .u64 retV) :: fr.ssa }
        | none => none
    | .opIAdd _ res aId bId =>
      match readAssocU64? lookupConst fr aId, readAssocU64? lookupConst fr bId with
      | some a, some b => evalSpirvBody lookupConst callRec rest { fr with ssa := (res, .u64 (a + b)) :: fr.ssa }
      | _, _ => none
    | .opISub _ res aId bId =>
      match readAssocU64? lookupConst fr aId, readAssocU64? lookupConst fr bId with
      | some a, some b => evalSpirvBody lookupConst callRec rest { fr with ssa := (res, .u64 (a - b)) :: fr.ssa }
      | _, _ => none
    | .opUGreaterThanEqual _ res aId bId =>
      match readAssocU64? lookupConst fr aId, readAssocU64? lookupConst fr bId with
      | some a, some b =>
        evalSpirvBody lookupConst callRec rest { fr with ssa := (res, .flag (decide (b.toNat ≤ a.toNat))) :: fr.ssa }
      | _, _ => none
    | .opULessThan _ res aId bId =>
      match readAssocU64? lookupConst fr aId, readAssocU64? lookupConst fr bId with
      | some a, some b =>
        evalSpirvBody lookupConst callRec rest { fr with ssa := (res, .flag (decide (a.toNat < b.toNat))) :: fr.ssa }
      | _, _ => none
    | .opSelect _ res cId tId fId =>
      match readAssocFlag? fr cId, readAssocU64? lookupConst fr tId,
            readAssocU64? lookupConst fr fId with
      | some c, some t, some f =>
        evalSpirvBody lookupConst callRec rest { fr with ssa := (res, .u64 (if c then t else f)) :: fr.ssa }
      | _, _, _ => none
    | .opBitwiseAnd _ res aId bId =>
      match readAssocU64? lookupConst fr aId, readAssocU64? lookupConst fr bId with
      | some a, some b => evalSpirvBody lookupConst callRec rest { fr with ssa := (res, .u64 (a &&& b)) :: fr.ssa }
      | _, _ => none
    | .opBitwiseOr _ res aId bId =>
      match readAssocU64? lookupConst fr aId, readAssocU64? lookupConst fr bId with
      | some a, some b => evalSpirvBody lookupConst callRec rest { fr with ssa := (res, .u64 (a ||| b)) :: fr.ssa }
      | _, _ => none
    | .opNot _ res aId =>
      match readAssocU64? lookupConst fr aId with
      | some a => evalSpirvBody lookupConst callRec rest { fr with ssa := (res, .u64 (~~~a)) :: fr.ssa }
      | none => none
    | .opReturnValue retId => readAssocU64? lookupConst fr retId
    | _ => none

/-- Fuel-bounded interprocedural evaluator for straight-line SPIR-V scalar helper functions
    passing `Pointer Function u64` parameters (`glslang` calling convention in `poseidon2_perm12.spv`). -/
def evalSpirvScalarCall (lookupConst : UInt32 → Option UInt64)
    (lookupFn : UInt32 → Option SpirvFunction) :
    Nat → UInt32 → List UInt64 → Option UInt64
  | 0, _, _ => none
  | callFuel + 1, fid, argVals =>
    match lookupFn fid with
    | none => none
    | some fn =>
      match zipParamSlots fn.params argVals with
      | none => none
      | some initSlots =>
        evalSpirvBody lookupConst (evalSpirvScalarCall lookupConst lookupFn callFuel)
          fn.body { ssa := [], slots := initSlots }

/-! ## 2. 64-Bit Predicated Mask Identities & Functional Equivalence to `Qsag.Goldilocks` -/

private theorem u64_and_allOnes (v : UInt64) :
    v &&& ((0 : UInt64) - 1) = v := by
  apply UInt64.eq_of_toBitVec_eq
  change v.toBitVec &&& BitVec.allOnes 64 = v.toBitVec
  apply bv_eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, Qsag.Constructive.getLsbD_allOnes, decide_eq_true hi, Bool.and_true]

private theorem u64_and_zero_right (v : UInt64) :
    v &&& (0 : UInt64) = 0 := by
  apply UInt64.eq_of_toBitVec_eq
  change v.toBitVec &&& 0#64 = 0#64
  simp

private theorem u64_or_zero_right (v : UInt64) :
    v ||| (0 : UInt64) = v := by
  apply UInt64.eq_of_toBitVec_eq
  change v.toBitVec ||| 0#64 = v.toBitVec
  simp

private theorem u64_zero_or (v : UInt64) :
    (0 : UInt64) ||| v = v := by
  apply UInt64.eq_of_toBitVec_eq
  change 0#64 ||| v.toBitVec = v.toBitVec
  simp

private def mockConst (fallback : UInt32 → Option UInt64) (cid : UInt32) : Option UInt64 :=
  if cid = 63 then some (UInt64.ofNat goldilocksPrime)
  else if cid = 64 then some 0
  else if cid = 68 then some 1
  else fallback cid

private theorem lookupConst_eq_mockConst (lookupConst : UInt32 → Option UInt64)
    (hC63 : lookupConst 63 = some (UInt64.ofNat goldilocksPrime))
    (hC64 : lookupConst 64 = some 0)
    (hC68 : lookupConst 68 = some 1) :
    lookupConst = mockConst lookupConst := by
  funext cid
  unfold mockConst
  by_cases h63 : cid = 63
  · subst h63; simp only [↓reduceIte]; exact hC63
  · by_cases h64 : cid = 64
    · subst h64; simp only [h63, ↓reduceIte]; exact hC64
    · by_cases h68 : cid = 68
      · subst h68; simp only [h63, h64, ↓reduceIte]; exact hC68
      · simp only [h63, h64, h68, ↓reduceIte]

private theorem fpReduceU64_eval_eq (lookupConst : UInt32 → Option UInt64)
    (lookupFn : UInt32 → Option SpirvFunction)
    (hC63 : lookupConst 63 = some (UInt64.ofNat goldilocksPrime))
    (hC64 : lookupConst 64 = some 0)
    (hC68 : lookupConst 68 = some 1)
    (hF10 : lookupFn 10 = some expectedFpReduceU64Fn)
    (fuel : Nat) (x : UInt64) :
    evalSpirvScalarCall lookupConst lookupFn (fuel + 1) 10 [x] =
      some (UInt64.ofNat (goldilocksCanon64 x.toNat)) := by
  have hpVal : (UInt64.ofNat goldilocksPrime).toNat = goldilocksPrime := rfl
  have hRed : evalSpirvScalarCall lookupConst lookupFn (fuel + 1) 10 [x] =
      some (x - (UInt64.ofNat goldilocksPrime &&&
        ((0 : UInt64) - (if decide (goldilocksPrime ≤ x.toNat) then 1 else 0)))) := by
    rw [evalSpirvScalarCall, hF10, lookupConst_eq_mockConst lookupConst hC63 hC64 hC68]
    rfl
  rw [hRed]
  congr 1
  obtain ⟨hCanonLt, hCanonMod⟩ := goldilocksCanon64_spec x.toNat_lt
  have hxLt : x.toNat < 2 ^ 64 := x.toNat_lt
  have hPLt64 : goldilocksPrime < 2 ^ 64 := by decide
  by_cases hGe : goldilocksPrime ≤ x.toNat
  · simp only [hGe, decide_true, ↓reduceIte, u64_and_allOnes]
    have hDiffLtP : x.toNat - goldilocksPrime < goldilocksPrime := by
      unfold goldilocksPrime at *; omega
    have hCanonEq : goldilocksCanon64 x.toNat = x.toNat - goldilocksPrime := by
      rw [hCanonMod, Nat.mod_eq_sub_mod hGe, Nat.mod_eq_of_lt hDiffLtP]
    rw [hCanonEq]
    apply UInt64.eq_of_toBitVec_eq
    apply BitVec.eq_of_toNat_eq
    change (x - UInt64.ofNat goldilocksPrime).toNat = (UInt64.ofNat (x.toNat - goldilocksPrime)).toNat
    rw [UInt64.toNat_sub_of_le, hpVal, UInt64.toNat_ofNat',
        Nat.mod_eq_of_lt (Nat.lt_trans hDiffLtP hPLt64)]
    exact UInt64.le_iff_toNat_le.mpr (by rw [hpVal]; exact hGe)
  · have hSub0 : (0 : UInt64) - 0 = 0 := rfl
    have hSubX0 : x - 0 = x := by
      apply UInt64.eq_of_toBitVec_eq
      change x.toBitVec - 0#64 = x.toBitVec
      simp
    simp only [hGe, decide_false, Bool.false_eq_true, ↓reduceIte, hSub0,
      u64_and_zero_right, hSubX0]
    have hCanonEq : goldilocksCanon64 x.toNat = x.toNat := by
      rw [hCanonMod, Nat.mod_eq_of_lt (by omega)]
    rw [hCanonEq]
    exact (UInt64.ofNat_toNat).symm

private def mockCall10 (fallback : UInt32 → List UInt64 → Option UInt64)
    (fid : UInt32) (args : List UInt64) : Option UInt64 :=
  if fid = 10 then
    match args with
    | [z] => some (UInt64.ofNat (goldilocksCanon64 z.toNat))
    | _ => fallback fid args
  else fallback fid args

private theorem call_eq_mockCall10 (lookupConst : UInt32 → Option UInt64)
    (lookupFn : UInt32 → Option SpirvFunction)
    (hC63 : lookupConst 63 = some (UInt64.ofNat goldilocksPrime))
    (hC64 : lookupConst 64 = some 0)
    (hC68 : lookupConst 68 = some 1)
    (hF10 : lookupFn 10 = some expectedFpReduceU64Fn)
    (fuel : Nat) :
    evalSpirvScalarCall lookupConst lookupFn (fuel + 1) =
      mockCall10 (evalSpirvScalarCall lookupConst lookupFn (fuel + 1)) := by
  funext fid args
  unfold mockCall10
  by_cases h10 : fid = 10
  · subst h10
    simp only [↓reduceIte]
    match args with
    | [z] => exact fpReduceU64_eval_eq lookupConst lookupFn hC63 hC64 hC68 hF10 fuel z
    | [] => rfl
    | _ :: _ :: _ => rfl
  · simp only [h10, ↓reduceIte]

private theorem fpSub_eval_eq (lookupConst : UInt32 → Option UInt64)
    (lookupFn : UInt32 → Option SpirvFunction)
    (hC63 : lookupConst 63 = some (UInt64.ofNat goldilocksPrime))
    (hC64 : lookupConst 64 = some 0)
    (hC68 : lookupConst 68 = some 1)
    (hF10 : lookupFn 10 = some expectedFpReduceU64Fn)
    (hF19 : lookupFn 19 = some expectedFpSubFn)
    (fuel : Nat) (x y : UInt64) :
    evalSpirvScalarCall lookupConst lookupFn (fuel + 2) 19 [x, y] =
      some (UInt64.ofNat (Goldilocks.sub (Goldilocks.ofNat x.toNat) (Goldilocks.ofNat y.toNat)).val) := by
  have hStep : evalSpirvScalarCall lookupConst lookupFn (fuel + 2) 19 [x, y] =
      some ((UInt64.ofNat (goldilocksCanon64 x.toNat) - UInt64.ofNat (goldilocksCanon64 y.toNat)) +
        (UInt64.ofNat goldilocksPrime &&&
          ((0 : UInt64) - (if decide ((UInt64.ofNat (goldilocksCanon64 x.toNat)).toNat <
            (UInt64.ofNat (goldilocksCanon64 y.toNat)).toNat) then 1 else 0)))) := by
    rw [evalSpirvScalarCall, hF19,
        call_eq_mockCall10 lookupConst lookupFn hC63 hC64 hC68 hF10 fuel,
        lookupConst_eq_mockConst lookupConst hC63 hC64 hC68]
    rfl
  rw [hStep]
  congr 1
  generalize hCxDef : UInt64.ofNat (goldilocksCanon64 x.toNat) = cx
  generalize hCyDef : UInt64.ofNat (goldilocksCanon64 y.toNat) = cy
  obtain ⟨hCxLtP, hCxMod⟩ := goldilocksCanon64_spec x.toNat_lt
  obtain ⟨hCyLtP, hCyMod⟩ := goldilocksCanon64_spec y.toNat_lt
  have hPLt64 : goldilocksPrime < 2 ^ 64 := by decide
  have hpVal : (UInt64.ofNat goldilocksPrime).toNat = goldilocksPrime := rfl
  have hCxVal : cx.toNat = goldilocksCanon64 x.toNat := by
    rw [← hCxDef, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_trans hCxLtP hPLt64)]
  have hCyVal : cy.toNat = goldilocksCanon64 y.toNat := by
    rw [← hCyDef, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_trans hCyLtP hPLt64)]
  have hSubVal : (Goldilocks.sub (Goldilocks.ofNat x.toNat) (Goldilocks.ofNat y.toNat)).val =
      (cx.toNat + goldilocksPrime - cy.toNat) % goldilocksPrime := by
    rw [Goldilocks.sub_val, Goldilocks.ofNat_val, Goldilocks.ofNat_val, hCxVal, hCyVal,
        hCxMod, hCyMod]
  rw [hSubVal]
  by_cases hLt : cx.toNat < cy.toNat
  · simp only [hLt, decide_true, ↓reduceIte, u64_and_allOnes]
    have hResLtP : cx.toNat + goldilocksPrime - cy.toNat < goldilocksPrime := by omega
    rw [Nat.mod_eq_of_lt hResLtP]
    apply UInt64.eq_of_toBitVec_eq
    apply BitVec.eq_of_toNat_eq
    change ((cx - cy) + UInt64.ofNat goldilocksPrime).toNat =
      (UInt64.ofNat (cx.toNat + goldilocksPrime - cy.toNat)).toNat
    have hWrap : (cx - cy).toNat = 2 ^ 64 + cx.toNat - cy.toNat := by
      change (cx.toBitVec - cy.toBitVec).toNat = _
      rw [BitVec.toNat_sub]
      change (2 ^ 64 - cy.toNat + cx.toNat) % 2 ^ 64 = 2 ^ 64 + cx.toNat - cy.toNat
      have hCxLt64 : cx.toNat < 2 ^ 64 := cx.toNat_lt
      have hCyLt64 : cy.toNat < 2 ^ 64 := cy.toNat_lt
      rw [show 2 ^ 64 - cy.toNat + cx.toNat = 2 ^ 64 + cx.toNat - cy.toNat by omega]
      exact Nat.mod_eq_of_lt (by omega)
    rw [UInt64.toNat_add, hWrap, hpVal, UInt64.toNat_ofNat',
        Nat.mod_eq_of_lt (Nat.lt_trans hResLtP hPLt64)]
    have hSumWrap : (2 ^ 64 + cx.toNat - cy.toNat + goldilocksPrime) =
        (cx.toNat + goldilocksPrime - cy.toNat) + 2 ^ 64 * 1 := by omega
    rw [hSumWrap, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Nat.lt_trans hResLtP hPLt64)]
  · have hSub0 : (0 : UInt64) - 0 = 0 := rfl
    have hAdd0 : ∀ w : UInt64, w + 0 = w := fun w => by
      apply UInt64.eq_of_toBitVec_eq
      change w.toBitVec + 0#64 = w.toBitVec
      simp
    simp only [hLt, decide_false, Bool.false_eq_true, ↓reduceIte, hSub0,
      u64_and_zero_right, hAdd0]
    have hDiffLtP : cx.toNat - cy.toNat < goldilocksPrime := by omega
    have hDecomp : cx.toNat + goldilocksPrime - cy.toNat =
        (cx.toNat - cy.toNat) + goldilocksPrime * 1 := by omega
    rw [hDecomp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hDiffLtP]
    apply UInt64.eq_of_toBitVec_eq
    apply BitVec.eq_of_toNat_eq
    change (cx - cy).toNat = (UInt64.ofNat (cx.toNat - cy.toNat)).toNat
    rw [UInt64.toNat_sub_of_le, UInt64.toNat_ofNat',
        Nat.mod_eq_of_lt (Nat.lt_trans hDiffLtP hPLt64)]
    exact UInt64.le_iff_toNat_le.mpr (by omega)

private def mockCall19 (fallback : UInt32 → List UInt64 → Option UInt64)
    (fid : UInt32) (args : List UInt64) : Option UInt64 :=
  if fid = 19 then
    match args with
    | [x, y] =>
      some (UInt64.ofNat (Goldilocks.sub (Goldilocks.ofNat x.toNat) (Goldilocks.ofNat y.toNat)).val)
    | _ => fallback fid args
  else fallback fid args

private theorem call_eq_mockCall19 (lookupConst : UInt32 → Option UInt64)
    (lookupFn : UInt32 → Option SpirvFunction)
    (hC63 : lookupConst 63 = some (UInt64.ofNat goldilocksPrime))
    (hC64 : lookupConst 64 = some 0)
    (hC68 : lookupConst 68 = some 1)
    (hF10 : lookupFn 10 = some expectedFpReduceU64Fn)
    (hF19 : lookupFn 19 = some expectedFpSubFn)
    (fuel : Nat) :
    evalSpirvScalarCall lookupConst lookupFn (fuel + 2) =
      mockCall19 (evalSpirvScalarCall lookupConst lookupFn (fuel + 2)) := by
  funext fid args
  unfold mockCall19
  by_cases h19 : fid = 19
  · subst h19
    simp only [↓reduceIte]
    match args with
    | [x, y] => exact fpSub_eval_eq lookupConst lookupFn hC63 hC64 hC68 hF10 hF19 fuel x y
    | [] => rfl
    | [_] => rfl
    | _ :: _ :: _ :: _ => rfl
  · simp only [h19, ↓reduceIte]

/-- **End-to-End Functional Equivalence of Decoded `poseidon2_perm12.spv` Field Helpers (`%10`, `%15`, `%19`, `%22`)**:
    Decoding `poseidon2Perm12SpvWords` yields `m : SpirvModule` whose actual SPIR-V functions
    `fp_reduce_u64` (`%10`), `fp_add` (`%15`), `fp_sub` (`%19`), and `fp_neg` (`%22`) execute
    identically to `goldilocksCanon64`, `Goldilocks.add`, `Goldilocks.sub`, and `Goldilocks.neg`
    across all 64-bit machine words `a, b : UInt64`! -/
theorem poseidon2Spv_fp_helpers_refine_goldilocks (a b : UInt64) :
    ∃ m : SpirvModule,
      decodeSpirvModule poseidon2Perm12SpvWords = .ok m ∧
      let run := evalSpirvScalarCall (findSpirvConst64 m) (findSpirvFunction m) 4
      run 10 [a] = some (UInt64.ofNat (goldilocksCanon64 a.toNat)) ∧
      run 15 [a, b] = some (UInt64.ofNat (Goldilocks.add (Goldilocks.ofNat a.toNat) (Goldilocks.ofNat b.toNat)).val) ∧
      run 19 [a, b] = some (UInt64.ofNat (Goldilocks.sub (Goldilocks.ofNat a.toNat) (Goldilocks.ofNat b.toNat)).val) ∧
      run 22 [a] = some (UInt64.ofNat (Goldilocks.neg (Goldilocks.ofNat a.toNat)).val) := by
  obtain ⟨m, hDec, _, _, _, _, _, _, _, hC63, hC64, hC68, hF10, hF15, hF19, hF22⟩ :=
    poseidon2Spv_decodes_and_roundtrips
  refine ⟨m, hDec, ?_⟩
  dsimp only
  have h10a := fpReduceU64_eval_eq (findSpirvConst64 m) (findSpirvFunction m) hC63 hC64 hC68 hF10 3 a
  have h19ab := fpSub_eval_eq (findSpirvConst64 m) (findSpirvFunction m) hC63 hC64 hC68 hF10 hF19 2 a b
  -- Prove `fp_add` (`%15`):
  have h15ab : evalSpirvScalarCall (findSpirvConst64 m) (findSpirvFunction m) 4 15 [a, b] =
      some (UInt64.ofNat (Goldilocks.add (Goldilocks.ofNat a.toNat) (Goldilocks.ofNat b.toNat)).val) := by
    have hStep : evalSpirvScalarCall (findSpirvConst64 m) (findSpirvFunction m) 4 15 [a, b] =
        some (((UInt64.ofNat (goldilocksCanon64 a.toNat) + UInt64.ofNat (goldilocksCanon64 b.toNat)) &&&
                ((0 : UInt64) - (if decide ((UInt64.ofNat (goldilocksCanon64 a.toNat)).toNat <
                  (UInt64.ofNat goldilocksPrime - UInt64.ofNat (goldilocksCanon64 b.toNat)).toNat) then 1 else 0))) |||
              ((UInt64.ofNat (goldilocksCanon64 a.toNat) - (UInt64.ofNat goldilocksPrime - UInt64.ofNat (goldilocksCanon64 b.toNat))) &&&
                ~~~((0 : UInt64) - (if decide ((UInt64.ofNat (goldilocksCanon64 a.toNat)).toNat <
                  (UInt64.ofNat goldilocksPrime - UInt64.ofNat (goldilocksCanon64 b.toNat)).toNat) then 1 else 0)))) := by
      rw [evalSpirvScalarCall, hF15,
          call_eq_mockCall10 (findSpirvConst64 m) (findSpirvFunction m) hC63 hC64 hC68 hF10 2,
          lookupConst_eq_mockConst (findSpirvConst64 m) hC63 hC64 hC68]
      rfl
    rw [hStep]
    congr 1
    generalize hCaDef : UInt64.ofNat (goldilocksCanon64 a.toNat) = ca
    generalize hCbDef : UInt64.ofNat (goldilocksCanon64 b.toNat) = cb
    generalize hRemDef : UInt64.ofNat goldilocksPrime - cb = rem
    obtain ⟨hCaLtP, hCaMod⟩ := goldilocksCanon64_spec a.toNat_lt
    obtain ⟨hCbLtP, hCbMod⟩ := goldilocksCanon64_spec b.toNat_lt
    have hPLt64 : goldilocksPrime < 2 ^ 64 := by decide
    have hpVal : (UInt64.ofNat goldilocksPrime).toNat = goldilocksPrime := rfl
    have hCaVal : ca.toNat = goldilocksCanon64 a.toNat := by
      rw [← hCaDef, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_trans hCaLtP hPLt64)]
    have hCbVal : cb.toNat = goldilocksCanon64 b.toNat := by
      rw [← hCbDef, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_trans hCbLtP hPLt64)]
    have hRemVal : rem.toNat = goldilocksPrime - cb.toNat := by
      rw [← hRemDef, UInt64.toNat_sub_of_le, hpVal]
      exact UInt64.le_iff_toNat_le.mpr (by rw [hpVal, hCbVal]; omega)
    have hAddVal : (Goldilocks.add (Goldilocks.ofNat a.toNat) (Goldilocks.ofNat b.toNat)).val =
        (ca.toNat + cb.toNat) % goldilocksPrime := by
      rw [Goldilocks.add_val, Goldilocks.ofNat_val, Goldilocks.ofNat_val,
          ← hCaMod, ← hCbMod, ← hCaVal, ← hCbVal]
    rw [hAddVal]
    by_cases hLt : ca.toNat < rem.toNat
    · have hNotOnes : ~~~((0 : UInt64) - 1) = 0 := rfl
      simp only [hLt, decide_true, ↓reduceIte, u64_and_allOnes, hNotOnes,
        u64_and_zero_right, u64_or_zero_right]
      have hSumLtP : ca.toNat + cb.toNat < goldilocksPrime := by omega
      rw [Nat.mod_eq_of_lt hSumLtP]
      apply UInt64.eq_of_toBitVec_eq
      apply BitVec.eq_of_toNat_eq
      change (ca + cb).toNat = (UInt64.ofNat (ca.toNat + cb.toNat)).toNat
      rw [UInt64.toNat_add, UInt64.toNat_ofNat',
          Nat.mod_eq_of_lt (Nat.lt_trans hSumLtP hPLt64)]
    · have hSub0 : (0 : UInt64) - 0 = 0 := rfl
      have hNot0 : ~~~(0 : UInt64) = (0 : UInt64) - 1 := rfl
      simp only [hLt, decide_false, Bool.false_eq_true, ↓reduceIte, hSub0,
        u64_and_zero_right, hNot0, u64_and_allOnes, u64_zero_or]
      have hGeP : goldilocksPrime ≤ ca.toNat + cb.toNat := by omega
      have hSubLtP : ca.toNat + cb.toNat - goldilocksPrime < goldilocksPrime := by omega
      rw [Nat.mod_eq_sub_mod hGeP, Nat.mod_eq_of_lt hSubLtP]
      apply UInt64.eq_of_toBitVec_eq
      apply BitVec.eq_of_toNat_eq
      change (ca - rem).toNat = (UInt64.ofNat (ca.toNat + cb.toNat - goldilocksPrime)).toNat
      rw [UInt64.toNat_sub_of_le, UInt64.toNat_ofNat',
          Nat.mod_eq_of_lt (Nat.lt_trans hSubLtP hPLt64)]
      · omega
      · exact UInt64.le_iff_toNat_le.mpr (by omega)
  -- Prove `fp_neg` (`%22`):
  have h22a : evalSpirvScalarCall (findSpirvConst64 m) (findSpirvFunction m) 4 22 [a] =
      some (UInt64.ofNat (Goldilocks.neg (Goldilocks.ofNat a.toNat)).val) := by
    rw [evalSpirvScalarCall, hF22,
        call_eq_mockCall19 (findSpirvConst64 m) (findSpirvFunction m) hC63 hC64 hC68 hF10 hF19 1,
        lookupConst_eq_mockConst (findSpirvConst64 m) hC63 hC64 hC68]
    rfl
  exact ⟨h10a, h15ab, h19ab, h22a⟩

/-- **Tooth (`tooth_poseidon2Spv_rejects_corrupted_magic_and_branchy_helper`)**:
    1. Corrupting word 0 of `poseidon2Perm12SpvWords` fails `verifyPoseidon2SpvWords` (`= false`),
    2. Injecting an `opBranchConditional` into `expectedFpReduceU64Fn` fails `isBranchlessHelperFn`, and
    3. Corrupting constant `%68` (`1 ↦ 0`) in `evalSpirvScalarCall` on `expectedFpReduceU64Fn`
       leaves `x = goldilocksPrime` unreduced (`≠ goldilocksCanon64 goldilocksPrime`)! -/
theorem tooth_poseidon2Spv_rejects_corrupted_magic_and_branchy_helper :
    ∃ x : UInt64,
      verifyPoseidon2SpvWords (0 :: poseidon2Perm12SpvWords.toList.drop 1) = false ∧
      isBranchlessHelperFn
        { expectedFpReduceU64Fn with
          body := .opLabel 11 :: .opBranchConditional 67 11 11 :: expectedFpReduceU64Fn.body } = false ∧
      evalSpirvScalarCall
        (fun cid => if cid = 63 then some (UInt64.ofNat goldilocksPrime) else some 0)
        (fun fid => if fid = 10 then some expectedFpReduceU64Fn else none)
        1 10 [x] ≠
          some (UInt64.ofNat (goldilocksCanon64 x.toNat)) := by
  refine ⟨UInt64.ofNat goldilocksPrime, tooth_poseidon2Spv_corrupted_magic, rfl, ?_⟩
  have hLhs :
      evalSpirvScalarCall
        (fun cid => if cid = 63 then some (UInt64.ofNat goldilocksPrime) else some 0)
        (fun fid => if fid = 10 then some expectedFpReduceU64Fn else none)
        1 10 [UInt64.ofNat goldilocksPrime] =
      some (UInt64.ofNat goldilocksPrime) := rfl
  have hpVal : (UInt64.ofNat goldilocksPrime).toNat = goldilocksPrime := rfl
  have hCanonP : goldilocksCanon64 (UInt64.ofNat goldilocksPrime).toNat = 0 := by
    rw [hpVal, (goldilocksCanon64_spec (by decide : goldilocksPrime < 2 ^ 64)).2, Nat.mod_self]
  rw [hLhs, hCanonP]
  decide

#verify_constructive
  Qsag.poseidon2Spv_fp_helpers_refine_goldilocks
  Qsag.tooth_poseidon2Spv_rejects_corrupted_magic_and_branchy_helper

#tooth_pair
  Qsag.poseidon2Spv_fp_helpers_refine_goldilocks
  vs
  Qsag.tooth_poseidon2Spv_rejects_corrupted_magic_and_branchy_helper

end Qsag
end
