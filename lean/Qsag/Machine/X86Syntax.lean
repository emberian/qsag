module
public import Qsag.Machine.IsaVectors
import Qsag.Tactic.AssuranceKit
public section
namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
  UInt64.instLawfulOrderOrd Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe
set_option autoImplicit false
set_option maxRecDepth 65536

@[expose] def signExt8To64 (b : UInt8) : UInt64 :=
  if b.toNat < 128 then UInt64.ofNat b.toNat else 0 - UInt64.ofNat (256 - b.toNat)

@[expose] def signExt32To64 (w : UInt32) : UInt64 :=
  if w.toNat < 0x80000000 then UInt64.ofNat w.toNat else 0 - UInt64.ofNat (0x100000000 - w.toNat)

@[expose] def signExt8ToInt (b : UInt8) : Int :=
  if b.toNat < 128 then Int.ofNat b.toNat else Int.ofNat b.toNat - 256

@[expose] def signExt32ToInt (w : UInt32) : Int :=
  if w.toNat < 0x80000000 then Int.ofNat w.toNat else Int.ofNat w.toNat - 0x100000000

/-- Effective address modes in `x86_64` `ModRM` + `SIB` decoding. -/
inductive X86MemAddr where
  | baseDisp (base : Nat) (disp : UInt64)
  | absDisp (disp : UInt64)
  | ripDisp (disp : UInt64)
  | indexedSib (baseOpt : Option Nat) (idx : Nat) (scaleShift : Nat) (disp : UInt64)
  deriving @[expose] DecidableEq, Repr

inductive X86AluOp where
  | add | adc | sub | sbb | andOp | orOp | xorOp | imul2
  deriving @[expose] DecidableEq, Repr

inductive X86ShiftKind where
  | shl | shr | rol | ror | sar
  deriving @[expose] DecidableEq, Repr

inductive X86VecBinOp where
  | vpxor | vpand | vpandn | vpor | vpaddb | vpcmpgtb | vpshufb | vgf2p8mulb
  deriving @[expose] DecidableEq, Repr

inductive X86VecShiftKind where
  | vpsllq | vpsrlq | vpsrlw | vpslldq | vpsrldq
  | vpshufd | vextracti128
  deriving @[expose] DecidableEq, Repr

/-- Decoded `x86_64` instruction covering all 16 `qsag_asm` `.rlib` kernels + forbidden variable-time classes. -/
inductive X86Instr where
  | nop
  | mfence
  | pushReg (reg : Nat)
  | popReg (reg : Nat)
  | ret
  | movRegReg (is64 : Bool) (dst src : Nat)
  | movImm (is64 : Bool) (dst : Nat) (imm : UInt64)
  | loadGpr (widthBytes : Nat) (is64 : Bool) (dst : Nat) (addr : X86MemAddr)
  | storeGpr (widthBytes : Nat) (src : Nat) (addr : X86MemAddr)
  | aluRegReg (op : X86AluOp) (is64 : Bool) (dst src : Nat)
  | aluLoad64 (op : X86AluOp) (dst : Nat) (addr : X86MemAddr)
  | aluImm (op : X86AluOp) (is64 : Bool) (dst : Nat) (imm : UInt64)
  | incDec (isInc : Bool) (is64 : Bool) (dst : Nat)
  | negReg (is64 : Bool) (dst : Nat)
  | mulOneOp (isSigned : Bool) (is64 : Bool) (src : Nat)
  | shiftImm (kind : X86ShiftKind) (is64 : Bool) (dst : Nat) (cnt : Nat)
  | cmovcc (cc : Nat) (is64 : Bool) (dst src : Nat)
  | testRegReg (is64 : Bool) (r1 r2 : Nat)
  | cmpRegReg (is64 : Bool) (dst src : Nat)
  | cmpImm (is64 : Bool) (dst : Nat) (imm : UInt64)
  | lea (is64 : Bool) (dst : Nat) (addr : X86MemAddr)
  | storeImm8 (addr : X86MemAddr) (imm : UInt8)
  | notReg (is64 : Bool) (dst : Nat)
  | setcc (cc : Nat) (dst : Nat)
  | bswap (is64 : Bool) (dst : Nat)
  | sseMovdquLoad (dst : Nat) (addr : X86MemAddr)
  | ssePcmpeqb (dst src : Nat)
  | ssePand (dst src : Nat)
  | ssePmovmskb (dst src : Nat)
  | mulx (hiDst loDst src : Nat)
  | adcx (dst src : Nat)
  | adox (dst src : Nat)
  | jcc (cc : Nat) (targetPc : Int)
  | jmpRel (targetPc : Int)
  | indirectBr (digit : Nat)
  | divRem (isSigned : Bool)
  | varShiftCl (digit : Nat) (dst : Nat)
  | vzeroupper
  | vzeroall
  | vload (is256 : Bool) (dst : Nat) (addr : X86MemAddr)
  | vstore (is256 : Bool) (src : Nat) (addr : X86MemAddr)
  | vmovGprToXmm (is64 : Bool) (dstVec srcGpr : Nat)
  | vpbroadcast (isQword is256 : Bool) (dst srcVec : Nat)
  | vpbroadcastLoad64 (dst : Nat) (addr : X86MemAddr)
  | vbinOp (op : X86VecBinOp) (is256 : Bool) (dst src1 src2 : Nat)
  | vpxorLoad256 (dst src1 : Nat) (addr : X86MemAddr)
  | vpxorLoad128 (dst src1 : Nat) (addr : X86MemAddr)
  | vshiftImm (kind : X86VecShiftKind) (is256 : Bool) (dst src : Nat) (imm : Nat)
  | vpclmulqdq (is256 : Bool) (dst src1 src2 : Nat) (imm : UInt8)
  | vgf2p8affineqb (is256 : Bool) (dst src1 src2 : Nat) (imm : UInt8)
  | vperm2i128 (dst src1 src2 : Nat) (imm : UInt8)
  | vpgather (op : UInt8) (addr : X86MemAddr)
  deriving @[expose] DecidableEq, Repr

/-- Decoded `ModRM` + optional `SIB` + optional `disp8`/`disp32` operand. -/
inductive ModRMOperand where
  | reg (r : Nat)
  | mem (addr : X86MemAddr)
  deriving @[expose] DecidableEq, Repr


end Qsag
