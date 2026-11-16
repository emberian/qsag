module
public import Qsag.Machine.IsaBanks
public section
namespace Qsag
structure Vec128 where
  w0 : UInt64
  w1 : UInt64
  deriving @[expose] DecidableEq, Repr

@[expose] def Vec128.zero : Vec128 := ⟨0, 0⟩

/-- 256-bit SIMD register (`ymm0..ymm15`). -/
structure Vec256 where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
  deriving @[expose] DecidableEq, Repr

@[expose] def Vec256.zero : Vec256 := ⟨0, 0, 0, 0⟩

/-- Hardware leakage observation emitted at each executed machine instruction (`§5`). -/
structure StepObs where
  pc : Nat
  memAccesses : List (UInt64 × Nat)
  isDoitSafe : Bool
  deriving @[expose] DecidableEq, Repr

/-- Decoded machine instruction paired with its exact byte offset and byte length in `.text`. -/
structure DecodedInstr (Instr : Type) where
  offset : Nat
  byteLen : Nat
  instr : Instr
  deriving @[expose] DecidableEq, Repr


end Qsag
