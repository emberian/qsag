module
public import Qsag.Machine.Arm64Semantics
import Qsag.Tactic.AssuranceKit
public section
namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
  UInt64.instLawfulOrderOrd Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe
set_option autoImplicit false
set_option maxRecDepth 65536

@[expose] def stepArm64 (d : DecodedInstr Arm64Instr) (s : Arm64State) : (Arm64State × StepObs) :=
  let nextPc := d.offset + 4
  match d.instr with
  | .nop | .isb | .dmbIsh =>
    ({ s with pc := nextPc }, ⟨d.offset, [], true⟩)
  | .msrDit imm =>
    ({ s with pc := nextPc, dit := imm != 0 }, ⟨d.offset, [], true⟩)
  | .ret =>
    ({ s with halted := true }, ⟨d.offset, [], true⟩)
  | .aluReg op is64 rd rn rm sk sa =>
    let b := applyArmShift is64 (getArmGpr s rm) sk sa
    let (res, cf', zf') := evalArmAlu op is64 (getArmGpr s rn) b s.cf s.zf
    ({ s with pc := nextPc, gpr := setArmGpr s rd res, cf := cf', zf := zf' }, ⟨d.offset, [], true⟩)
  | .aluImm op is64 rd rn imm =>
    let (res, cf', zf') := evalArmAlu op is64 (getArmGpr s rn) imm s.cf s.zf
    ({ s with pc := nextPc, gpr := setArmGpr s rd res, cf := cf', zf := zf' }, ⟨d.offset, [], true⟩)
  | .movWide isMovn is64 rd imm16 sh =>
    let shifted := UInt64.ofNat imm16 <<< UInt64.ofNat sh
    let raw := if isMovn then ~~~shifted else shifted
    let res := maskGprWidth is64 raw
    ({ s with pc := nextPc, gpr := setArmGpr s rd res }, ⟨d.offset, [], true⟩)
  | .ubfm is64 rd rn immr imms =>
    let w := if is64 then 64 else 32
    let src := maskGprWidth is64 (getArmGpr s rn)
    let res :=
      if imms + 1 == w then maskGprWidth is64 (src >>> UInt64.ofNat immr)
      else if imms + 1 == immr then maskGprWidth is64 (src <<< UInt64.ofNat (w - immr))
      else
        let width := if immr ≤ imms then imms - immr + 1 else imms + 1
        let mask : UInt64 := if width ≥ 64 then 0 - 1 else (1 <<< UInt64.ofNat width) - 1
        if immr ≤ imms then maskGprWidth is64 ((src >>> UInt64.ofNat immr) &&& mask)
        else maskGprWidth is64 ((src &&& mask) <<< UInt64.ofNat (w - immr))
    ({ s with pc := nextPc, gpr := setArmGpr s rd res }, ⟨d.offset, [], true⟩)
  | .mulOp isUmulh rd rn rm =>
    let prod := (getArmGpr s rn).toNat * (getArmGpr s rm).toNat
    let res := if isUmulh then UInt64.ofNat (prod / 0x10000000000000000)
               else UInt64.ofNat (prod % 0x10000000000000000)
    ({ s with pc := nextPc, gpr := setArmGpr s rd res }, ⟨d.offset, [], s.dit⟩)
  | .csel cond isInv is64 rd rn rm =>
    let taken := evalArmCond cond s
    let v := if taken then getArmGpr s rn
             else if isInv then ~~~(getArmGpr s rm) else getArmGpr s rm
    -- `sf = 0` writes the 32-bit result zero-extended into `Xd`; `sf = 1` writes all 64 bits.
    ({ s with pc := nextPc, gpr := setArmGpr s rd (maskGprWidth is64 v) }, ⟨d.offset, [], s.dit⟩)
  | .ldp64 rt1 rt2 rn off =>
    let ea := getArmGpr s rn + off
    let v1 := readMem64 s.mem ea
    let v2 := readMem64 s.mem (ea + 8)
    let s1 := { s with gpr := setArmGpr s rt1 v1 }
    ({ s1 with pc := nextPc, gpr := setArmGpr s1 rt2 v2 }, ⟨d.offset, [(ea, 8), (ea + 8, 8)], true⟩)
  | .stp64 rt1 rt2 rn off =>
    let ea := getArmGpr s rn + off
    let m1 := writeMem64 s.mem ea (getArmGpr s rt1)
    let m2 := writeMem64 m1 (ea + 8) (getArmGpr s rt2)
    ({ s with pc := nextPc, mem := m2 }, ⟨d.offset, [(ea, 8), (ea + 8, 8)], true⟩)
  | .strbPost rt rn postOff =>
    let ea := getArmGpr s rn
    let m' := writeMem8 s.mem ea (getArmGpr s rt).toUInt8
    ({ s with pc := nextPc, gpr := setArmGpr s rn (ea + postOff), mem := m' }, ⟨d.offset, [(ea, 1)], true⟩)
  | .ldpQ rt1 rt2 rn off =>
    let ea := getArmGpr s rn + off
    let v1 := readMem128 s.mem ea
    let v2 := readMem128 s.mem (ea + 16)
    ({ s with pc := nextPc, vec := (s.vec.set rt1 v1).set rt2 v2 },
      ⟨d.offset, [(ea, 16), (ea + 16, 16)], true⟩)
  | .stpQ rt1 rt2 rn off =>
    let ea := getArmGpr s rn + off
    let m := writeMem128 (writeMem128 s.mem ea (s.vec.get rt1)) (ea + 16) (s.vec.get rt2)
    ({ s with pc := nextPc, mem := m }, ⟨d.offset, [(ea, 16), (ea + 16, 16)], true⟩)
  | .vdup2d vd xn =>
    ({ s with pc := nextPc, vec := s.vec.set vd ⟨getArmGpr s xn, getArmGpr s xn⟩ },
      ⟨d.offset, [], true⟩)
  | .vand16b vd vn vm =>
    let a := s.vec.get vn; let b := s.vec.get vm
    ({ s with pc := nextPc, vec := s.vec.set vd ⟨a.w0 &&& b.w0, a.w1 &&& b.w1⟩ },
      ⟨d.offset, [], true⟩)
  | .vshift2d left vd vn amount =>
    let a := s.vec.get vn
    -- UInt64 shifts mask their count; ISA USHR #64 instead yields zero.
    let shift (v : UInt64) := if amount ≥ 64 then 0
      else if left then v <<< UInt64.ofNat amount else v >>> UInt64.ofNat amount
    ({ s with pc := nextPc, vec := s.vec.set vd ⟨shift a.w0, shift a.w1⟩ },
      ⟨d.offset, [], true⟩)
  | .ldrQ rt rn off =>
    let ea := getArmGpr s rn + off
    let v := readMem128 s.mem ea
    ({ s with pc := nextPc, vec := s.vec.set rt v }, ⟨d.offset, [(ea, 16)], true⟩)
  | .strQ rt rn off =>
    let ea := getArmGpr s rn + off
    let m' := writeMem128 s.mem ea (s.vec.get rt)
    ({ s with pc := nextPc, mem := m' }, ⟨d.offset, [(ea, 16)], true⟩)
  | .fmovDFromX vd xn =>
    ({ s with pc := nextPc, vec := s.vec.set vd ⟨getArmGpr s xn, 0⟩ }, ⟨d.offset, [], true⟩)
  | .veor16b vd vn vm =>
    let a := s.vec.get vn; let b := s.vec.get vm
    ({ s with pc := nextPc, vec := s.vec.set vd ⟨a.w0 ^^^ b.w0, a.w1 ^^^ b.w1⟩ }, ⟨d.offset, [], true⟩)
  | .vbcax16b vd vn vm va =>
    let n := s.vec.get vn; let m := s.vec.get vm; let a := s.vec.get va
    ({ s with pc := nextPc, vec := s.vec.set vd ⟨n.w0 ^^^ (m.w0 &&& (~~~a.w0)), n.w1 ^^^ (m.w1 &&& (~~~a.w1))⟩ },
     ⟨d.offset, [], true⟩)
  | .veor3_16b vd vn vm va =>
    let n := s.vec.get vn; let m := s.vec.get vm; let a := s.vec.get va
    ({ s with pc := nextPc, vec := s.vec.set vd ⟨n.w0 ^^^ m.w0 ^^^ a.w0, n.w1 ^^^ m.w1 ^^^ a.w1⟩ },
     ⟨d.offset, [], true⟩)
  | .vrax1_2d vd vn vm =>
    let n := s.vec.get vn; let m := s.vec.get vm
    let rol1 (x : UInt64) := (x <<< 1) ||| (x >>> 63)
    ({ s with pc := nextPc, vec := s.vec.set vd ⟨n.w0 ^^^ rol1 m.w0, n.w1 ^^^ rol1 m.w1⟩ }, ⟨d.offset, [], true⟩)
  | .vxar_2d vd vn vm imm6 =>
    let n := s.vec.get vn; let m := s.vec.get vm
    let ror (x : UInt64) :=
      let c := imm6 % 64
      if c == 0 then x else (x >>> UInt64.ofNat c) ||| (x <<< UInt64.ofNat (64 - c))
    ({ s with pc := nextPc, vec := s.vec.set vd ⟨ror (n.w0 ^^^ m.w0), ror (n.w1 ^^^ m.w1)⟩ }, ⟨d.offset, [], true⟩)
  | .vpmull isHigh vd vn vm =>
    let n := s.vec.get vn; let m := s.vec.get vm
    let p := if isHigh then clmul64 n.w1 m.w1 else clmul64 n.w0 m.w0
    ({ s with pc := nextPc, vec := s.vec.set vd p }, ⟨d.offset, [], s.dit⟩)
  | .vtrn is128 second elementBytes vd vn vm =>
    let n := s.vec.get vn; let m := s.vec.get vm
    let pick (i : Nat) : UInt8 :=
      let elem := i / elementBytes
      let src := if elem % 2 == 0 then n else m
      let k := (2 * (elem / 2) + (if second then 1 else 0)) * elementBytes + i % elementBytes
      if k < 8 then getByte64 src.w0 k else getByte64 src.w1 (k - 8)
    let out : Vec128 := ⟨mapBytes64 pick, if is128 then mapBytes64 (fun i => pick (i+8)) else 0⟩
    ({ s with pc := nextPc, vec := s.vec.set vd out }, ⟨d.offset, [], true⟩)
  | .vext16b vd vn vm imm4 =>
    let n := s.vec.get vn; let m := s.vec.get vm
    let getB (k : Nat) : UInt8 :=
      if k < 8 then getByte64 n.w0 k
      else if k < 16 then getByte64 n.w1 (k - 8)
      else if k < 24 then getByte64 m.w0 (k - 16)
      else getByte64 m.w1 (k - 24)
    let out : Vec128 :=
      ⟨mapBytes64 (fun i => getB (imm4 + i)), mapBytes64 (fun i => getB (imm4 + 8 + i))⟩
    ({ s with pc := nextPc, vec := s.vec.set vd out }, ⟨d.offset, [], true⟩)
  | .bCond cond targetPc =>
    let taken := evalArmCond cond s
    let tgt := if taken && targetPc ≥ 0 then targetPc.toNat else nextPc
    ({ s with pc := tgt }, ⟨d.offset, [], true⟩)
  | .cbzOrTbz _ | .udivOrSdiv _ | .varShiftReg _ | .regOffsetMem _ =>
    ({ s with halted := true }, ⟨d.offset, [], false⟩)

/-- Bounded-fuel `AArch64` execution returning the final state and leakage trace `List StepObs`. -/
@[expose] def runArm64 (prog : List (DecodedInstr Arm64Instr)) : Nat → Arm64State → (Arm64State × List StepObs)
  | 0, s => (s, [])
  | fuel + 1, s =>
    if s.halted then (s, [])
    else match findInstrAtPc s.pc prog with
    | none => ({ s with halted := true }, [])
    | some d =>
      let (s', obs) := stepArm64 d s
      let (sFinal, restObs) := runArm64 prog fuel s'
      (sFinal, obs :: restObs)

end Qsag
