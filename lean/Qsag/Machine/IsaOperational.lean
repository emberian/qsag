module
public import Qsag.Machine.Arm64AbsTransfer
import Qsag.Tactic.AssuranceKit
public section
namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
  UInt64.instLawfulOrderOrd Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe
set_option autoImplicit false
set_option maxRecDepth 65536
@[expose] def checkX86WithInv (code : List UInt8) (c : FuncContract) (inv : PcMap X86AbsState) : Bool :=
  match decodeX86Stream code with
  | none => false
  | some prog =>
    match prog with
    | [] => false
    | _ :: _ => verifyX86Invariant prog c inv

@[expose] def checkArm64WithInv (code : List UInt8) (c : FuncContract) (inv : PcMap Arm64AbsState) : Bool :=
  match decodeArm64Stream code with
  | none => false
  | some prog =>
    match prog with
    | [] => false
    | _ :: _ => verifyArm64Invariant prog c inv

@[expose] def armGet (g : Bank32 UInt64) (r : Nat) : UInt64 := if r == 31 then 0 else g.get r

@[expose] def armSet (g : Bank32 UInt64) (r : Nat) (v : UInt64) : Bank32 UInt64 := if r == 31 then g else g.set r v

@[expose] def jccPc (taken : Bool) (tgt : Int) (next : Nat) : Nat :=
  if taken && decide (tgt ≥ 0) then tgt.toNat else next
end Qsag
