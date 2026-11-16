module
public import Qsag.Machine.IsaOperational
import Qsag.Tactic.AssuranceKit
public section
namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
  UInt64.instLawfulOrderOrd Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe
set_option autoImplicit false
set_option maxRecDepth 65536
end Qsag
namespace Qsag.SydTv
open Qsag
@[expose] def decodeX86One (code : List UInt8) (pc : Nat) : Option (DecodedInstr X86Instr) :=
  if pc < code.length then decodeX86InstrAt pc (code.drop pc) else none

@[expose] def decodeArm64One (code : List UInt8) (pc : Nat) : Option (DecodedInstr Arm64Instr) :=
  if pc % 4 == 0 && pc + 4 ≤ code.length then
    match readU32LE? (code.drop pc) with
    | some w => (decodeArm64Word pc w).map (fun ins => ⟨pc, 4, ins⟩)
    | none => none
  else none

@[expose] def runX86Fetch (fetch : Nat → Option (DecodedInstr X86Instr)) :
    Nat → X86State → X86State × List StepObs
  | 0, s => (s, [])
  | fuel + 1, s =>
    if s.halted then (s, [])
    else match fetch s.pc with
    | none => ({ s with halted := true }, [])
    | some d =>
      let (s', obs) := stepX86 d s
      let (sFinal, restObs) := runX86Fetch fetch fuel s'
      (sFinal, obs :: restObs)

@[expose] def runX86One (code : List UInt8) : Nat → X86State → X86State × List StepObs :=
  runX86Fetch (decodeX86One code)

@[expose] def runArm64Fetch (fetch : Nat → Option (DecodedInstr Arm64Instr)) :
    Nat → Arm64State → Arm64State × List StepObs
  | 0, s => (s, [])
  | fuel + 1, s =>
    if s.halted then (s, [])
    else match fetch s.pc with
    | none => ({ s with halted := true }, [])
    | some d =>
      let (s', obs) := stepArm64 d s
      let (sFinal, restObs) := runArm64Fetch fetch fuel s'
      (sFinal, obs :: restObs)

@[expose] def runArm64One (code : List UInt8) : Nat → Arm64State → Arm64State × List StepObs :=
  runArm64Fetch (decodeArm64One code)

@[expose] def bcastQword256 (w : UInt64) : Vec256 := ⟨w, w, w, w⟩

@[expose] def bcastByte256 (b : UInt8) : Vec256 :=
  let w := mapBytes64 (fun _ => b)
  ⟨w, w, w, w⟩

@[expose] def clmul256 (v1 v2 : Vec256) (imm : UInt8) : Vec256 :=
  let selLo1 := if (imm &&& 0x01) == 0 then v1.w0 else v1.w1
  let selLo2 := if (imm &&& 0x10) == 0 then v2.w0 else v2.w1
  let pLo := clmul64 selLo1 selLo2
  let selHi1 := if (imm &&& 0x01) == 0 then v1.w2 else v1.w3
  let selHi2 := if (imm &&& 0x10) == 0 then v2.w2 else v2.w3
  let pHi := clmul64 selHi1 selHi2
  ⟨pLo.w0, pLo.w1, pHi.w0, pHi.w1⟩

@[expose] def zeroUpperVec256 (v : Vec256) : Vec256 := ⟨v.w0, v.w1, 0, 0⟩
end Qsag.SydTv
