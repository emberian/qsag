module
public import Qsag.Machine.X86Decode
import Qsag.Tactic.AssuranceKit
public section
namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
  UInt64.instLawfulOrderOrd Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe
set_option autoImplicit false
set_option maxRecDepth 65536

structure X86State where
  pc : Nat
  gpr : Bank16 UInt64
  ymm : Bank16 Vec256
  cf : Bool
  ofFlag : Bool
  zf : Bool
  ymmDirty : Bool
  halted : Bool
  mem : UInt64 → UInt8

@[expose] def readMem64 (mem : UInt64 → UInt8) (addr : UInt64) : UInt64 :=
  (mem addr).toUInt64 |||
  ((mem (addr + 1)).toUInt64 <<< 8) |||
  ((mem (addr + 2)).toUInt64 <<< 16) |||
  ((mem (addr + 3)).toUInt64 <<< 24) |||
  ((mem (addr + 4)).toUInt64 <<< 32) |||
  ((mem (addr + 5)).toUInt64 <<< 40) |||
  ((mem (addr + 6)).toUInt64 <<< 48) |||
  ((mem (addr + 7)).toUInt64 <<< 56)

@[expose] def writeMem8 (mem : UInt64 → UInt8) (addr : UInt64) (b : UInt8) : UInt64 → UInt8 :=
  fun a => if a == addr then b else mem a

@[expose] def writeMem64 (mem : UInt64 → UInt8) (addr : UInt64) (v : UInt64) : UInt64 → UInt8 :=
  let m0 := writeMem8 mem addr v.toUInt8
  let m1 := writeMem8 m0 (addr + 1) (v >>> 8).toUInt8
  let m2 := writeMem8 m1 (addr + 2) (v >>> 16).toUInt8
  let m3 := writeMem8 m2 (addr + 3) (v >>> 24).toUInt8
  let m4 := writeMem8 m3 (addr + 4) (v >>> 32).toUInt8
  let m5 := writeMem8 m4 (addr + 5) (v >>> 40).toUInt8
  let m6 := writeMem8 m5 (addr + 6) (v >>> 48).toUInt8
  writeMem8 m6 (addr + 7) (v >>> 56).toUInt8

@[expose] def readMem128 (mem : UInt64 → UInt8) (addr : UInt64) : Vec128 :=
  ⟨readMem64 mem addr, readMem64 mem (addr + 8)⟩

@[expose] def writeMem128 (mem : UInt64 → UInt8) (addr : UInt64) (v : Vec128) : UInt64 → UInt8 :=
  writeMem64 (writeMem64 mem addr v.w0) (addr + 8) v.w1

@[expose] def readMem256 (mem : UInt64 → UInt8) (addr : UInt64) : Vec256 :=
  ⟨readMem64 mem addr, readMem64 mem (addr + 8), readMem64 mem (addr + 16), readMem64 mem (addr + 24)⟩

@[expose] def writeMem256 (mem : UInt64 → UInt8) (addr : UInt64) (v : Vec256) : UInt64 → UInt8 :=
  let m0 := writeMem64 mem addr v.w0
  let m1 := writeMem64 m0 (addr + 8) v.w1
  let m2 := writeMem64 m1 (addr + 16) v.w2
  writeMem64 m2 (addr + 24) v.w3

@[expose] def evalX86Addr (s : X86State) (nextPc : Nat) : X86MemAddr → UInt64
  | .baseDisp base disp => s.gpr.get base + disp
  | .absDisp disp => disp
  | .ripDisp disp => UInt64.ofNat nextPc + disp
  | .indexedSib baseOpt idx scale disp =>
    let bVal := match baseOpt with | some b => s.gpr.get b | none => 0
    bVal + (s.gpr.get idx <<< UInt64.ofNat scale) + disp

@[expose] def maskGprWidth (is64 : Bool) (v : UInt64) : UInt64 :=
  if is64 then v else v &&& 0xFFFFFFFF

/- Parity of an 8-bit byte (`GFNI` `VGF2P8AFFINEQB` dot-product helper). -/
end Qsag
