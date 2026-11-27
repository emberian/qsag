module
public import Qsag.Oracle.Qrom
public import Aeneas
public import Qsag.Protocol.Aggregation.PublicHemQuintic128
public section
open Aeneas Aeneas.Std
namespace qsag_whir_verified.proofs

abbrev boundedEnd (len off count width : Nat) : Option Usize :=
  if 0 < width ∧ off + count * width ≤ len then
    some (UScalar.ofNat .Usize (off + count * width)) else none

/-- Canonicality of each little-endian field word in a run. -/
@[expose] def fieldWordRun (word : Nat → Nat) (prime : Nat) (off : Nat) : Nat → Bool
  | 0 => true
  | n+1 => decide (word off < prime) && fieldWordRun word prime (off+8) n

abbrev validWordRegion (word : Nat → Nat) (prime len off stop : Nat) : Bool :=
  decide (off ≤ stop ∧ stop ≤ len ∧ (stop-off)%8 = 0) &&
    fieldWordRun word prime off ((stop-off)/8)

abbrev digestRegion (word : Nat → Nat) (len off count : Nat) :
    Option Qsag.Aggregation.PublicHemQuintic128 → Option Usize
  | some .turboShake400 => boundedEnd len off count 50
  | some .poseidon2Gl24 => do
    let stop ← boundedEnd len off count 56
    if validWordRegion word Qsag.goldilocksPrime len off stop.val then some stop else none
  | none => none

abbrev openingRegion (word : Nat → Nat) (len off depth fold : Nat) (leaves : List Nat)
    (base : Bool) (profile : Option Qsag.Aggregation.PublicHemQuintic128) : Option (Usize × Usize) := do
  if fold > 28 ∨ ¬ (depth ≤ 28 ∧ Qsag.canopyIndicesOk (2^depth) leaves) then none else
    let width ← boundedEnd len 0 (2^fold) (if base then 8 else 40)
    let split ← boundedEnd len off leaves.length width.val
    if validWordRegion word Qsag.goldilocksPrime len off split.val then
      let stop ← digestRegion word len split.val (Qsag.steinerSiblingCount depth leaves) profile
      some (split, stop)
    else none

end qsag_whir_verified.proofs
end
