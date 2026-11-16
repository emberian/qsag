module
public import Qsag.Machine.X86Step
import Qsag.Tactic.AssuranceKit
public section
namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
  UInt64.instLawfulOrderOrd Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe
set_option autoImplicit false
set_option maxRecDepth 65536

inductive Arm64AluOp where
  | add | adds | sub | subs | adc | sbc | andOp | orr | eor | bic
  deriving @[expose] DecidableEq, Repr

/-- Decoded `AArch64` instruction covering all 9 current `qsag_asm` `.rlib` kernels + forbidden variable-time classes. -/
inductive Arm64Instr where
  | nop
  | msrDit (imm : Nat)
  | isb
  | dmbIsh
  | ret
  | aluReg (op : Arm64AluOp) (is64 : Bool) (rd rn rm shiftKind shiftAmt : Nat)
  | aluImm (op : Arm64AluOp) (is64 : Bool) (rd rn : Nat) (imm : UInt64)
  | movWide (isMovn : Bool) (is64 : Bool) (rd : Nat) (imm16 shift : Nat)
  | ubfm (is64 : Bool) (rd rn immr imms : Nat)
  | mulOp (isUmulh : Bool) (rd rn rm : Nat)
  | csel (cond : Nat) (isInv : Bool) (is64 : Bool) (rd rn rm : Nat)
  | ldp64 (rt1 rt2 rn : Nat) (offBytes : UInt64)
  | stp64 (rt1 rt2 rn : Nat) (offBytes : UInt64)
  | strbPost (rt rn : Nat) (postOff : UInt64)
  | ldpQ (rt1 rt2 rn : Nat) (offBytes : UInt64)
  | stpQ (rt1 rt2 rn : Nat) (offBytes : UInt64)
  | vdup2d (vd xn : Nat)
  | vand16b (vd vn vm : Nat)
  | vshift2d (left : Bool) (vd vn amount : Nat)
  | ldrQ (rt rn : Nat) (offBytes : UInt64)
  | strQ (rt rn : Nat) (offBytes : UInt64)
  | fmovDFromX (vd xn : Nat)
  | veor16b (vd vn vm : Nat)
  | vbcax16b (vd vn vm va : Nat)
  | veor3_16b (vd vn vm va : Nat)
  | vrax1_2d (vd vn vm : Nat)
  | vxar_2d (vd vn vm imm6 : Nat)
  | vpmull (isHigh : Bool) (vd vn vm : Nat)
  | vtrn (is128 second : Bool) (elementBytes vd vn vm : Nat)
  | vext16b (vd vn vm imm4 : Nat)
  | bCond (cond : Nat) (targetPc : Int)
  | cbzOrTbz (word : UInt32)
  | udivOrSdiv (word : UInt32)
  | varShiftReg (word : UInt32)
  | regOffsetMem (word : UInt32)
  deriving @[expose] DecidableEq, Repr

/-- ARMv8-A `DecodeBitMasks` logical immediate decoder (`N:immr:imms` $\to$ 64-bit replicated bitmask). -/
@[expose] def decodeArm64BitmaskImm (is64 : Bool) (nBit immr imms : Nat) : Option UInt64 :=
  let len? : Option Nat :=
    if nBit == 1 then (if is64 then some 6 else none)
    else if (imms &&& 0x20) == 0 then some 5
    else if (imms &&& 0x10) == 0 then some 4
    else if (imms &&& 0x08) == 0 then some 3
    else if (imms &&& 0x04) == 0 then some 2
    else if (imms &&& 0x02) == 0 then some 1
    else none
  match len? with
  | none => none
  | some len =>
    let esize := 1 <<< len
    let levels := esize - 1
    let s := imms &&& levels
    let r := immr &&& levels
    if s == levels then none
    else
      let ones : UInt64 := if s + 1 == 64 then 0 - 1 else (1 <<< UInt64.ofNat (s + 1)) - 1
      let rMod := r % esize
      let maskElem : UInt64 := if esize == 64 then 0 - 1 else (1 <<< UInt64.ofNat esize) - 1
      let rotElem :=
        if rMod == 0 then ones
        else ((ones >>> UInt64.ofNat rMod) ||| (ones <<< UInt64.ofNat (esize - rMod))) &&& maskElem
      let rep32 :=
        if esize == 2 then rotElem * 0x5555555555555555
        else if esize == 4 then rotElem * 0x1111111111111111
        else if esize == 8 then rotElem * 0x0101010101010101
        else if esize == 16 then rotElem * 0x0001000100010001
        else if esize == 32 then rotElem ||| (rotElem <<< 32)
        else rotElem
      some (maskGprWidth is64 rep32)

/-- Decode a single 32-bit little-endian `AArch64` instruction word at byte offset `pc`. -/
@[expose] def decodeArm64Word (pc : Nat) (w : UInt32) : Option Arm64Instr :=
  let wn := w.toNat
  let rd := wn &&& 0x1F
  let rn := (wn >>> 5) &&& 0x1F
  let rm := (wn >>> 16) &&& 0x1F
  let ra := (wn >>> 10) &&& 0x1F
  let is64 := ((wn >>> 31) &&& 1) == 1
  if w == 0xD503201F then some .nop
  else if w == 0xD503415F then some (.msrDit 1)
  else if w == 0xD503405F then some (.msrDit 0)
  else if w == 0xD5033FDF then some .isb
  else if w == 0xD5033BBF then some .dmbIsh
  else if w == 0xD65F03C0 then some .ret
  -- Forbidden CBZ/CBNZ (`x34..x35`) & TBZ/TBNZ (`x36..x37`)
  else if (wn &&& 0x7C000000) == 0x34000000 then some (.cbzOrTbz w)
  -- Conditional branch `B.cond` (`01010100 imm19 0 cond`)
  else if (wn &&& 0xFF000010) == 0x54000000 then
    let cond := wn &&& 0xF
    let imm19 := (wn >>> 5) &&& 0x7FFFF
    let signed19 : Int := if imm19 < 0x40000 then Int.ofNat imm19 else Int.ofNat imm19 - 0x80000
    if cond < 4 then some (.bCond cond (Int.ofNat pc + signed19 * 4)) else none
  -- Forbidden UDIV / SDIV (`x011010110 Rm 00001x Rn Rd`)
  else if (wn &&& 0x7FE0FC00) == 0x1AC00800 then some (.udivOrSdiv w)
  -- Forbidden variable shift `LSLV/LSRV/ASRV/RORV` (`x011010110 Rm 0010xx Rn Rd`)
  else if (wn &&& 0x7FE0F000) == 0x1AC02000 then some (.varShiftReg w)
  -- Forbidden register-offset `LDR/STR [Xn, Xm]`
  else if (wn &&& 0x3B200C00) == 0x38200800 then some (.regOffsetMem w)
  -- `MUL Xd, Xn, Xm` (`0x9B007C00`) & `UMULH Xd, Xn, Xm` (`0x9BC07C00`)
  else if (wn &&& 0xFFE0FC00) == 0x9B007C00 then some (.mulOp false rd rn rm)
  else if (wn &&& 0xFFE0FC00) == 0x9BC07C00 then some (.mulOp true rd rn rm)
  -- `ADC` (`0x9A000000`) & `SBC`/`NGC` (`0xDA000000`)
  else if (wn &&& 0x7FE0FC00) == 0x1A000000 then some (.aluReg .adc is64 rd rn rm 0 0)
  else if (wn &&& 0x7FE0FC00) == 0x5A000000 then some (.aluReg .sbc is64 rd rn rm 0 0)
  -- `CSEL` / `CSINV` (`CSETM`)
  else if (wn &&& 0x7FE00C00) == 0x1A800000 then
    let cond := (wn >>> 12) &&& 0xF
    if cond < 4 then some (.csel cond false is64 rd rn rm) else none
  else if (wn &&& 0x7FE00C00) == 0x5A800000 then
    let cond := (wn >>> 12) &&& 0xF
    if cond < 4 then some (.csel cond true is64 rd rn rm) else none
  -- Add/Sub immediate (`x0010001 sh imm12 Rn Rd`)
  else if (wn &&& 0x1F800000) == 0x11000000 then
    let opc := (wn >>> 29) &&& 3
    let sh := ((wn >>> 22) &&& 1) * 12
    let imm12 := ((wn >>> 10) &&& 0xFFF) <<< sh
    let aop : Arm64AluOp :=
      if opc == 0 then .add else if opc == 1 then .adds else if opc == 2 then .sub else .subs
    if rn == 31 || ((opc == 0 || opc == 2) && rd == 31) then none
    else some (.aluImm aop is64 rd rn (UInt64.ofNat imm12))
  -- Add/Sub shifted register (`xx001011 shift 0 Rm imm6 Rn Rd`)
  else if (wn &&& 0x1F200000) == 0x0B000000 then
    let opc := (wn >>> 29) &&& 3
    let shiftKind := (wn >>> 22) &&& 3
    let shiftAmt := (wn >>> 10) &&& 0x3F
    let aop : Arm64AluOp :=
      if opc == 0 then .add else if opc == 1 then .adds else if opc == 2 then .sub else .subs
    -- `shift == 0b11` is reserved for Add/Sub, and `imm6 ≥ 32` is unallocated when `sf = 0`.
    if shiftKind == 3 || (!is64 && shiftAmt ≥ 32) then none
    else some (.aluReg aop is64 rd rn rm shiftKind shiftAmt)
  -- Logical shifted register (`xx001010 shift N Rm imm6 Rn Rd`)
  else if (wn &&& 0x1F000000) == 0x0A000000 then
    let opc := (wn >>> 29) &&& 3
    let nInv := ((wn >>> 21) &&& 1) == 1
    let shiftKind := (wn >>> 22) &&& 3
    let shiftAmt := (wn >>> 10) &&& 0x3F
    if !is64 && shiftAmt ≥ 32 then none
    else if opc == 0 && !nInv then some (.aluReg .andOp is64 rd rn rm shiftKind shiftAmt)
    else if opc == 0 && nInv then some (.aluReg .bic is64 rd rn rm shiftKind shiftAmt)
    else if opc == 1 && !nInv then some (.aluReg .orr is64 rd rn rm shiftKind shiftAmt)
    else if opc == 2 && !nInv then some (.aluReg .eor is64 rd rn rm shiftKind shiftAmt)
    else none
  -- Move wide immediate `MOVN` (`opc=0`) / `MOVZ` (`opc=2`): `xx100101 hw imm16 Rd`
  else if (wn &&& 0x1F800000) == 0x12800000 then
    let opc := (wn >>> 29) &&& 3
    let hw := ((wn >>> 21) &&& 3) * 16
    let imm16 := (wn >>> 5) &&& 0xFFFF
    if opc == 0 || opc == 2 then some (.movWide (opc == 0) is64 rd imm16 hw) else none
  -- Logical immediate (`xx100100 N immr imms Rn Rd`)
  else if (wn &&& 0x1F800000) == 0x12000000 then
    let opc := (wn >>> 29) &&& 3
    let nBit := (wn >>> 22) &&& 1
    let immr := (wn >>> 16) &&& 0x3F
    let imms := (wn >>> 10) &&& 0x3F
    match decodeArm64BitmaskImm is64 nBit immr imms with
    | none => none
    | some imm =>
      if rd == 31 then none
      else if opc == 0 then some (.aluImm .andOp is64 rd rn imm)
      else if opc == 1 then some (.aluImm .orr is64 rd rn imm)
      else if opc == 2 then some (.aluImm .eor is64 rd rn imm)
      else none
  -- `UBFM` (`LSL`/`LSR` immediate): `x10100110 N immr imms Rn Rd`
  else if (wn &&& 0x7F800000) == 0x53000000 then
    let immr := (wn >>> 16) &&& 0x3F
    let imms := (wn >>> 10) &&& 0x3F
    let n := (wn >>> 22) &&& 1
    if (is64 && n == 1) || (!is64 && n == 0 && immr < 32 && imms < 32) then
      some (.ubfm is64 rd rn immr imms)
    else none
  -- `LDP` / `STP` 64-bit signed offset (`101010010 L imm7 Rt2 Rn Rt1`)
  else if (wn &&& 0xFFC00000) == 0xA9400000 || (wn &&& 0xFFC00000) == 0xA9000000 then
    let isLoad := ((wn >>> 22) &&& 1) == 1
    let imm7 := (wn >>> 15) &&& 0x7F
    let off64 : UInt64 :=
      if imm7 < 64 then UInt64.ofNat (imm7 * 8) else 0 - UInt64.ofNat ((128 - imm7) * 8)
    if rn == 31 then none
    else if isLoad then some (.ldp64 rd ra rn off64) else some (.stp64 rd ra rn off64)
  -- Offset-only paired Q accesses; SP and duplicate load destinations are rejected.
  else if (wn &&& 0xFFC00000) == 0xAD400000 || (wn &&& 0xFFC00000) == 0xAD000000 then
    let isLoad := ((wn >>> 22) &&& 1) == 1
    let imm7 := (wn >>> 15) &&& 0x7F
    let off : UInt64 := if imm7 < 64 then UInt64.ofNat (imm7 * 16)
                       else 0 - UInt64.ofNat ((128 - imm7) * 16)
    if rn == 31 || (isLoad && rd == ra) then none
    else if isLoad then some (.ldpQ rd ra rn off) else some (.stpQ rd ra rn off)
  -- DUP Vd.2D, Xn; only the 64-bit element arrangement.
  else if (wn &&& 0xFFFFFC00) == 0x4E080C00 then some (.vdup2d rd rn)
  else if (wn &&& 0xFFE0FC00) == 0x4E201C00 then some (.vand16b rd rn rm)
  -- SHL/USHR Vd.2D, Vn.2D, #imm. Bit 22 selects 64-bit lanes.
  else if (wn &&& 0xFFC0FC00) == 0x4F405400 then
    some (.vshift2d true rd rn ((wn >>> 16) &&& 63))
  else if (wn &&& 0xFFC0FC00) == 0x6F400400 then
    some (.vshift2d false rd rn (64 - ((wn >>> 16) &&& 63)))
  -- `STRB Wt, [Xn], #imm9` post-index (`00111000000 imm9 01 Rn Rt`)
  else if (wn &&& 0xFFE00C00) == 0x38000400 then
    let imm9 := (wn >>> 12) &&& 0x1FF
    let off64 : UInt64 :=
      if imm9 < 256 then UInt64.ofNat imm9 else 0 - UInt64.ofNat (512 - imm9)
    if rn == 31 then none else some (.strbPost rd rn off64)
  -- `LDR Qrt, [Xrn, #imm12*16]` (`0x3DC00000`) & `STR Qrt, [Xrn, #imm12*16]` (`0x3D800000`)
  else if (wn &&& 0xFFC00000) == 0x3DC00000 then
    let imm12 := (wn >>> 10) &&& 0xFFF
    if rn == 31 then none else some (.ldrQ rd rn (UInt64.ofNat (imm12 * 16)))
  else if (wn &&& 0xFFC00000) == 0x3D800000 then
    let imm12 := (wn >>> 10) &&& 0xFFF
    if rn == 31 then none else some (.strQ rd rn (UInt64.ofNat (imm12 * 16)))
  -- `FMOV Dd, Xn` (`0x9E670000`)
  else if (wn &&& 0xFFFFFC00) == 0x9E670000 then
    some (.fmovDFromX rd rn)
  -- `EOR Vd.16B, Vn.16B, Vm.16B` (`0x6E201C00`)
  else if (wn &&& 0xFFE0FC00) == 0x6E201C00 then
    some (.veor16b rd rn rm)
  -- `EOR3` (`0xCE000000`), `BCAX` (`0xCE200000`), `RAX1` (`0xCE608C00`), `XAR` (`0xCE800000`)
  else if (wn &&& 0xFFE08000) == 0xCE000000 then
    some (.veor3_16b rd rn rm ra)
  else if (wn &&& 0xFFE08000) == 0xCE200000 then
    some (.vbcax16b rd rn rm ra)
  else if (wn &&& 0xFFE0FC00) == 0xCE608C00 then
    some (.vrax1_2d rd rn rm)
  else if (wn &&& 0xFFE00000) == 0xCE800000 then
    let imm6 := (wn >>> 10) &&& 0x3F
    some (.vxar_2d rd rn rm imm6)
  -- `PMULL Vd.1Q, Vn.1D, Vm.1D` (`0x0EE0E000`) & `PMULL2 Vd.1Q, Vn.2D, Vm.2D` (`0x4EE0E000`)
  else if (wn &&& 0xBFE0FC00) == 0x0EE0E000 then
    some (.vpmull (((wn >>> 30) &&& 1) == 1) rd rn rm)
  -- TRN1/TRN2: interleave even/odd elements, following LNSym's exec_trn.
  else if (wn &&& 0xBF20BC00) == 0x0E002800 then
    let q := ((wn >>> 30) &&& 1) == 1
    let size := (wn >>> 22) &&& 3
    if !q && size == 3 then none
    else some (.vtrn q (((wn >>> 14) &&& 1) == 1) (1 <<< size) rd rn rm)
  -- `EXT Vd.16B, Vn.16B, Vm.16B, #imm4` (`0x6E000000`)
  else if (wn &&& 0xFFE08400) == 0x6E000000 then
    let imm4 := (wn >>> 11) &&& 0xF
    some (.vext16b rd rn rm imm4)
  else
    none

@[expose] def decodeArm64Loop : Nat → List UInt8 → List (DecodedInstr Arm64Instr) → Option (List (DecodedInstr Arm64Instr))
  | _, [], acc => some acc.reverse
  | pc, b0 :: b1 :: b2 :: b3 :: rest, acc =>
    let w : UInt32 := b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)
    match decodeArm64Word pc w with
    | none => none
    | some ins => decodeArm64Loop (pc + 4) rest (⟨pc, 4, ins⟩ :: acc)
  | _, _ :: _, _ => none

/-- Decode an entire `.text` symbol byte slice into a 32-bit `AArch64` instruction stream. -/
@[expose] def decodeArm64Stream (code : List UInt8) : Option (List (DecodedInstr Arm64Instr)) :=
  decodeArm64Loop 0 code []

/-- Concrete `AArch64` machine state (`X0..X30` + `XZR`, `V0..V31`, `NZCV` flags, `DIT`, byte memory). -/
structure Arm64State where
  pc : Nat
  gpr : Bank32 UInt64
  vec : Bank32 Vec128
  cf : Bool
  zf : Bool
  dit : Bool
  halted : Bool
  mem : UInt64 → UInt8

@[expose] def getArmGpr (s : Arm64State) (r : Nat) : UInt64 :=
  if r == 31 then 0 else s.gpr.get r

@[expose] def setArmGpr (s : Arm64State) (r : Nat) (v : UInt64) : Bank32 UInt64 :=
  if r == 31 then s.gpr else s.gpr.set r v

@[expose] def applyArmShift (is64 : Bool) (v : UInt64) (kind amt : Nat) : UInt64 :=
  let v' := maskGprWidth is64 v
  let w := if is64 then 64 else 32
  let c := amt % w
  if c == 0 then v'
  else if kind == 0 then maskGprWidth is64 (v' <<< UInt64.ofNat c)
  else if kind == 1 then maskGprWidth is64 (v' >>> UInt64.ofNat c)
  else if kind == 2 then
    -- `ASR`: the vacated high `c` bits take the sign bit (bit `w - 1`) of the `w`-bit operand.
    let fill : UInt64 :=
      if (v' >>> UInt64.ofNat (w - 1)) &&& 1 == 1
      then maskGprWidth is64 ((0 - 1 : UInt64) <<< UInt64.ofNat (w - c)) else 0
    (v' >>> UInt64.ofNat c) ||| fill
  else maskGprWidth is64 ((v' >>> UInt64.ofNat c) ||| (v' <<< UInt64.ofNat (w - c)))

@[expose] def evalArmAlu (op : Arm64AluOp) (is64 : Bool) (a b : UInt64) (cfIn zfIn : Bool) : (UInt64 × Bool × Bool) :=
  let bound : Nat := if is64 then 0x10000000000000000 else 0x100000000
  let an := (maskGprWidth is64 a).toNat
  let bn := (maskGprWidth is64 b).toNat
  let cin := if cfIn then 1 else 0
  let invBorrow := if cfIn then 0 else 1
  match op with
  | .add => (maskGprWidth is64 (UInt64.ofNat ((an + bn) % bound)), cfIn, zfIn)
  | .adds =>
    let sum := an + bn
    let res := maskGprWidth is64 (UInt64.ofNat (sum % bound))
    (res, sum ≥ bound, res == 0)
  | .sub => (maskGprWidth is64 (UInt64.ofNat ((an + bound - bn) % bound)), cfIn, zfIn)
  | .subs =>
    let res := maskGprWidth is64 (UInt64.ofNat ((an + bound - bn) % bound))
    (res, an ≥ bn, res == 0)
  | .adc =>
    let res := maskGprWidth is64 (UInt64.ofNat ((an + bn + cin) % bound))
    (res, cfIn, zfIn)
  | .sbc =>
    let res := maskGprWidth is64 (UInt64.ofNat ((an + bound * 2 - bn - invBorrow) % bound))
    (res, cfIn, zfIn)
  | .andOp => (maskGprWidth is64 (a &&& b), cfIn, zfIn)
  | .orr => (maskGprWidth is64 (a ||| b), cfIn, zfIn)
  | .eor => (maskGprWidth is64 (a ^^^ b), cfIn, zfIn)
  | .bic => (maskGprWidth is64 (a &&& (~~~b)), cfIn, zfIn)

@[expose] def evalArmCond (cond : Nat) (s : Arm64State) : Bool :=
  if cond == 0 then s.zf
  else if cond == 1 then !s.zf
  else if cond == 2 then s.cf
  else if cond == 3 then !s.cf
  else s.cf

/- Small-step `AArch64` operational semantics emitting `StepObs` (`pc`, `(addr, bytes)`, `isDoitSafe`). -/
end Qsag
