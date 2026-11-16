module
public import Qsag.Machine.X86VectorEval
import Qsag.Tactic.AssuranceKit
public section
namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
  UInt64.instLawfulOrderOrd Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe
set_option autoImplicit false
set_option maxRecDepth 65536

@[expose] def stepX86 (d : DecodedInstr X86Instr) (s : X86State) : (X86State × StepObs) :=
  let nextPc := d.offset + d.byteLen
  match d.instr with
  | .nop | .mfence =>
    ({ s with pc := nextPc }, ⟨d.offset, [], true⟩)
  | .pushReg r =>
    let sp' := s.gpr.get 4 - 8
    let mem' := writeMem64 s.mem sp' (s.gpr.get r)
    ({ s with pc := nextPc, gpr := s.gpr.set 4 sp', mem := mem' }, ⟨d.offset, [(sp', 8)], true⟩)
  | .popReg r =>
    let sp := s.gpr.get 4
    let v := readMem64 s.mem sp
    let gpr' := (s.gpr.set 4 (sp + 8)).set r v
    ({ s with pc := nextPc, gpr := gpr' }, ⟨d.offset, [(sp, 8)], true⟩)
  | .ret =>
    let sp := s.gpr.get 4
    let retRip := readMem64 s.mem sp
    ({ s with pc := retRip.toNat, gpr := s.gpr.set 4 (sp + 8), halted := true },
      ⟨d.offset, [(sp, 8)], true⟩)
  | .movRegReg is64 dst src =>
    let v := maskGprWidth is64 (s.gpr.get src)
    ({ s with pc := nextPc, gpr := s.gpr.set dst v }, ⟨d.offset, [], true⟩)
  | .movImm is64 dst imm =>
    let v := maskGprWidth is64 imm
    ({ s with pc := nextPc, gpr := s.gpr.set dst v }, ⟨d.offset, [], true⟩)
  | .loadGpr wBytes is64 dst addr =>
    let ea := evalX86Addr s nextPc addr
    let raw := if wBytes == 1 then (s.mem ea).toUInt64 else readMem64 s.mem ea
    let v := maskGprWidth is64 raw
    ({ s with pc := nextPc, gpr := s.gpr.set dst v }, ⟨d.offset, [(ea, wBytes)], true⟩)
  | .storeGpr wBytes src addr =>
    let ea := evalX86Addr s nextPc addr
    let mem' := if wBytes == 1 then writeMem8 s.mem ea (s.gpr.get src).toUInt8
                else writeMem64 s.mem ea (s.gpr.get src)
    ({ s with pc := nextPc, mem := mem' }, ⟨d.offset, [(ea, wBytes)], true⟩)
  | .aluRegReg op is64 dst src =>
    let a := s.gpr.get dst
    let b := s.gpr.get src
    let (res, cf', zf') := evalX86Alu op is64 a b s.cf
    let of' := evalX86AluOf op is64 a b s.cf
    ({ s with pc := nextPc, gpr := s.gpr.set dst res, cf := cf', ofFlag := of', zf := zf' }, ⟨d.offset, [], true⟩)
  | .aluLoad64 op dst addr =>
    let ea := evalX86Addr s nextPc addr
    let a := s.gpr.get dst
    let mval := readMem64 s.mem ea
    let (res, cf', zf') := evalX86Alu op true a mval s.cf
    let of' := evalX86AluOf op true a mval s.cf
    ({ s with pc := nextPc, gpr := s.gpr.set dst res, cf := cf', ofFlag := of', zf := zf' }, ⟨d.offset, [(ea, 8)], true⟩)
  | .aluImm op is64 dst imm =>
    let a := s.gpr.get dst
    let (res, cf', zf') := evalX86Alu op is64 a imm s.cf
    let of' := evalX86AluOf op is64 a imm s.cf
    ({ s with pc := nextPc, gpr := s.gpr.set dst res, cf := cf', ofFlag := of', zf := zf' }, ⟨d.offset, [], true⟩)
  | .incDec isInc is64 dst =>
    let cur := s.gpr.get dst
    let delta : UInt64 := if isInc then 1 else 0 - 1
    let res := maskGprWidth is64 (maskGprWidth is64 cur + delta)
    let of' := evalX86IncDecOf isInc is64 cur
    ({ s with pc := nextPc, gpr := s.gpr.set dst res, ofFlag := of', zf := res == 0 }, ⟨d.offset, [], true⟩)
  | .negReg is64 dst =>
    let cur := maskGprWidth is64 (s.gpr.get dst)
    let res := maskGprWidth is64 (0 - cur)
    let of' := cur == (if is64 then 0x8000000000000000 else 0x80000000)
    ({ s with pc := nextPc, gpr := s.gpr.set dst res, cf := cur != 0, ofFlag := of', zf := res == 0 }, ⟨d.offset, [], true⟩)
  | .mulOneOp isSigned is64 src =>
    -- `MUL` / `IMUL` with one operand: `rDX:rAX := rAX * src` at the operand width `w`. `raw` is
    -- the `2w`-bit product pattern (two's complement when signed). `CF = OF` is set when the
    -- upper half is significant: nonzero for `MUL`, not the sign extension of the lower half for
    -- `IMUL`.
    let bound : Nat := if is64 then 0x10000000000000000 else 0x100000000
    let a := (maskGprWidth is64 (s.gpr.get 0)).toNat
    let b := (maskGprWidth is64 (s.gpr.get src)).toNat
    let raw : Nat :=
      if isSigned then
        ((signedOfBound bound a * signedOfBound bound b) % ((bound * bound : Nat) : Int)).toNat
      else a * b
    let lo := maskGprWidth is64 (UInt64.ofNat (raw % bound))
    let hi := maskGprWidth is64 (UInt64.ofNat (raw / bound))
    let ovf := if isSigned then imulSignedOverflow bound a b else decide (raw / bound ≠ 0)
    ({ s with pc := nextPc, gpr := (s.gpr.set 0 lo).set 2 hi, cf := ovf, ofFlag := ovf },
      ⟨d.offset, [], true⟩)
  | .shiftImm sk is64 dst cnt =>
    let (res, cf', of', zf') := evalX86Shift sk is64 (s.gpr.get dst) cnt s.cf s.ofFlag s.zf
    ({ s with pc := nextPc, gpr := s.gpr.set dst res, cf := cf', ofFlag := of', zf := zf' }, ⟨d.offset, [], true⟩)
  | .cmovcc cc is64 dst src =>
    -- `X86State` has no `DOITM` bit, so the observation cannot depend on the mode: `true` here
    -- means "data-operand-independent when `DOITM` is set". The mode assumption is carried by
    -- `FuncContract.doitEnabled`, and `transferX86Instr` rejects `cmovcc` without it.
    -- Per Intel SDM, 32-bit `CMOVcc` in 64-bit mode zero-extends `dst[31:0]` into `dst[63:0]`
    -- even when the condition is false (`!taken`).
    let taken := evalX86Cond cc s
    let chosen := if taken then s.gpr.get src else s.gpr.get dst
    let gpr' := s.gpr.set dst (maskGprWidth is64 chosen)
    ({ s with pc := nextPc, gpr := gpr' }, ⟨d.offset, [], true⟩)
  | .testRegReg is64 r1 r2 =>
    let res := maskGprWidth is64 ((s.gpr.get r1) &&& (s.gpr.get r2))
    ({ s with pc := nextPc, cf := false, ofFlag := false, zf := res == 0 }, ⟨d.offset, [], true⟩)
  | .cmpRegReg is64 dst src =>
    let a := s.gpr.get dst
    let b := s.gpr.get src
    let (_, cf', zf') := evalX86Alu .sub is64 a b false
    let of' := evalX86AluOf .sub is64 a b false
    ({ s with pc := nextPc, cf := cf', ofFlag := of', zf := zf' }, ⟨d.offset, [], true⟩)
  | .cmpImm is64 dst imm =>
    let a := s.gpr.get dst
    let (_, cf', zf') := evalX86Alu .sub is64 a imm false
    let of' := evalX86AluOf .sub is64 a imm false
    ({ s with pc := nextPc, cf := cf', ofFlag := of', zf := zf' }, ⟨d.offset, [], true⟩)
  | .lea is64 dst addr =>
    let v := maskGprWidth is64 (evalX86Addr s nextPc addr)
    ({ s with pc := nextPc, gpr := s.gpr.set dst v }, ⟨d.offset, [], true⟩)
  | .storeImm8 addr imm =>
    let ea := evalX86Addr s nextPc addr
    ({ s with pc := nextPc, mem := writeMem8 s.mem ea imm }, ⟨d.offset, [(ea, 1)], true⟩)
  | .notReg is64 dst =>
    let res := maskGprWidth is64 (~~~(s.gpr.get dst))
    ({ s with pc := nextPc, gpr := s.gpr.set dst res }, ⟨d.offset, [], true⟩)
  | .setcc cc dst =>
    let taken := evalX86Cond cc s
    let cur := s.gpr.get dst
    let v := (cur &&& 0xFFFFFFFFFFFFFF00) ||| (if taken then 1 else 0)
    ({ s with pc := nextPc, gpr := s.gpr.set dst v }, ⟨d.offset, [], true⟩)
  | .bswap is64 dst =>
    let res := evalX86Bswap is64 (s.gpr.get dst)
    ({ s with pc := nextPc, gpr := s.gpr.set dst res }, ⟨d.offset, [], true⟩)
  | .sseMovdquLoad dst addr =>
    let ea := evalX86Addr s nextPc addr
    let q := readMem128 s.mem ea
    let old := s.ymm.get dst
    ({ s with pc := nextPc, ymm := s.ymm.set dst ⟨q.w0, q.w1, old.w2, old.w3⟩ },
     ⟨d.offset, [(ea, 16)], true⟩)
  | .ssePcmpeqb dst src =>
    let vd := s.ymm.get dst
    let vs := s.ymm.get src
    let eqWord (w1 w2 : UInt64) : UInt64 :=
      mapBytes64 (fun i => if getByte64 w1 i == getByte64 w2 i then 0xFF else 0x00)
    ({ s with pc := nextPc, ymm := s.ymm.set dst ⟨eqWord vd.w0 vs.w0, eqWord vd.w1 vs.w1, vd.w2, vd.w3⟩ },
     ⟨d.offset, [], true⟩)
  | .ssePand dst src =>
    let vd := s.ymm.get dst
    let vs := s.ymm.get src
    ({ s with pc := nextPc, ymm := s.ymm.set dst ⟨vd.w0 &&& vs.w0, vd.w1 &&& vs.w1, vd.w2, vd.w3⟩ },
     ⟨d.offset, [], true⟩)
  | .ssePmovmskb dst src =>
    let mask := evalPmovmskb128 (s.ymm.get src)
    ({ s with pc := nextPc, gpr := s.gpr.set dst mask }, ⟨d.offset, [], true⟩)
  | .mulx hiDst loDst src =>
    let prod := (s.gpr.get 2).toNat * (s.gpr.get src).toNat
    let lo := UInt64.ofNat (prod % 0x10000000000000000)
    let hi := UInt64.ofNat (prod / 0x10000000000000000)
    let gpr' := (s.gpr.set loDst lo).set hiDst hi
    ({ s with pc := nextPc, gpr := gpr' }, ⟨d.offset, [], true⟩)
  | .adcx dst src =>
    let sum := (s.gpr.get dst).toNat + (s.gpr.get src).toNat + (if s.cf then 1 else 0)
    let res := UInt64.ofNat (sum % 0x10000000000000000)
    ({ s with pc := nextPc, gpr := s.gpr.set dst res, cf := sum ≥ 0x10000000000000000 }, ⟨d.offset, [], true⟩)
  | .adox dst src =>
    let sum := (s.gpr.get dst).toNat + (s.gpr.get src).toNat + (if s.ofFlag then 1 else 0)
    let res := UInt64.ofNat (sum % 0x10000000000000000)
    ({ s with pc := nextPc, gpr := s.gpr.set dst res, ofFlag := sum ≥ 0x10000000000000000 }, ⟨d.offset, [], true⟩)
  | .jcc cc targetPc =>
    let taken := evalX86Cond cc s
    let tgt := if taken && targetPc ≥ 0 then targetPc.toNat else nextPc
    ({ s with pc := tgt }, ⟨d.offset, [], true⟩)
  | .jmpRel targetPc =>
    let tgt := if targetPc ≥ 0 then targetPc.toNat else nextPc
    ({ s with pc := tgt }, ⟨d.offset, [], true⟩)
  | .indirectBr _ | .divRem _ | .varShiftCl _ _ =>
    ({ s with halted := true }, ⟨d.offset, [], false⟩)
  | .vpgather _ addr =>
    let ea := evalX86Addr s nextPc addr
    ({ s with halted := true }, ⟨d.offset, [(ea, 32)], false⟩)
  | .vzeroupper =>
    let ymm' := Bank16.ofFn (fun i => let v := s.ymm.get i; ⟨v.w0, v.w1, 0, 0⟩)
    ({ s with pc := nextPc, ymm := ymm', ymmDirty := false }, ⟨d.offset, [], true⟩)
  | .vzeroall =>
    ({ s with pc := nextPc, ymm := Bank16.ofFn (fun _ => Vec256.zero), ymmDirty := false },
      ⟨d.offset, [], true⟩)
  | .vload is256 dst addr =>
    let ea := evalX86Addr s nextPc addr
    let v := if is256 then readMem256 s.mem ea
             else let q := readMem128 s.mem ea; ⟨q.w0, q.w1, 0, 0⟩
    ({ s with pc := nextPc, ymm := s.ymm.set dst v, ymmDirty := s.ymmDirty || is256 },
     ⟨d.offset, [(ea, if is256 then 32 else 16)], true⟩)
  | .vstore is256 src addr =>
    let ea := evalX86Addr s nextPc addr
    let v := s.ymm.get src
    let mem' := if is256 then writeMem256 s.mem ea v else writeMem128 s.mem ea ⟨v.w0, v.w1⟩
    ({ s with pc := nextPc, mem := mem' }, ⟨d.offset, [(ea, if is256 then 32 else 16)], true⟩)
  | .vmovGprToXmm is64 dstVec srcGpr =>
    let v := maskGprWidth is64 (s.gpr.get srcGpr)
    ({ s with pc := nextPc, ymm := s.ymm.set dstVec ⟨v, 0, 0, 0⟩ }, ⟨d.offset, [], true⟩)
  | .vpbroadcast isQword is256 dst srcVec =>
    let sv := s.ymm.get srcVec
    let w := if isQword then sv.w0 else mapBytes64 (fun _ => sv.w0.toUInt8)
    -- `VEX.L = 0` writes `xmm` and zeroes bits `[255:128]`; `VEX.L = 1` writes all of `ymm`.
    ({ s with pc := nextPc, ymm := s.ymm.set dst (clampVecWidth is256 ⟨w, w, w, w⟩),
              ymmDirty := s.ymmDirty || is256 }, ⟨d.offset, [], true⟩)
  | .vpbroadcastLoad64 dst addr =>
    let ea := evalX86Addr s nextPc addr
    let w := readMem64 s.mem ea
    ({ s with pc := nextPc, ymm := s.ymm.set dst ⟨w, w, w, w⟩, ymmDirty := true }, ⟨d.offset, [(ea, 8)], true⟩)
  | .vbinOp op is256 dst src1 src2 =>
    let res := clampVecWidth is256 (evalVecBin256 op (s.ymm.get src1) (s.ymm.get src2))
    ({ s with pc := nextPc, ymm := s.ymm.set dst res, ymmDirty := s.ymmDirty || is256 }, ⟨d.offset, [], true⟩)
  | .vpxorLoad128 dst src1 addr =>
    let ea := evalX86Addr s nextPc addr
    let mvec := readMem128 s.mem ea
    let res := clampVecWidth false (evalVecBin256 .vpxor (s.ymm.get src1) ⟨mvec.w0, mvec.w1, 0, 0⟩)
    ({ s with pc := nextPc, ymm := s.ymm.set dst res }, ⟨d.offset, [(ea, 16)], true⟩)
  | .vpxorLoad256 dst src1 addr =>
    let ea := evalX86Addr s nextPc addr
    let mvec := readMem256 s.mem ea
    let res := evalVecBin256 .vpxor (s.ymm.get src1) mvec
    ({ s with pc := nextPc, ymm := s.ymm.set dst res, ymmDirty := true }, ⟨d.offset, [(ea, 32)], true⟩)
  | .vshiftImm sk is256 dst src imm =>
    let res := clampVecWidth is256 (evalVecShift256 sk (s.ymm.get src) imm)
    ({ s with pc := nextPc, ymm := s.ymm.set dst res, ymmDirty := s.ymmDirty || is256 }, ⟨d.offset, [], true⟩)
  | .vpclmulqdq is256 dst src1 src2 imm =>
    let v1 := s.ymm.get src1
    let v2 := s.ymm.get src2
    let selLo1 := if (imm &&& 0x01) == 0 then v1.w0 else v1.w1
    let selLo2 := if (imm &&& 0x10) == 0 then v2.w0 else v2.w1
    let pLo := clmul64 selLo1 selLo2
    let pHi := if is256 then
                 let selHi1 := if (imm &&& 0x01) == 0 then v1.w2 else v1.w3
                 let selHi2 := if (imm &&& 0x10) == 0 then v2.w2 else v2.w3
                 clmul64 selHi1 selHi2
               else Vec128.zero
    ({ s with pc := nextPc, ymm := s.ymm.set dst ⟨pLo.w0, pLo.w1, pHi.w0, pHi.w1⟩, ymmDirty := s.ymmDirty || is256 },
     ⟨d.offset, [], true⟩)
  | .vgf2p8affineqb is256 dst src1 src2 imm =>
    let res := clampVecWidth is256 (gfniAffineVec256 (s.ymm.get src1) (s.ymm.get src2) imm)
    ({ s with pc := nextPc, ymm := s.ymm.set dst res, ymmDirty := s.ymmDirty || is256 }, ⟨d.offset, [], true⟩)
  | .vperm2i128 dst src1 src2 imm =>
    let v1 := s.ymm.get src1
    let v2 := s.ymm.get src2
    let pick128 (sel : UInt8) : Vec128 :=
      if (sel &&& 0x08) != 0 then Vec128.zero
      else match (sel &&& 0x03).toNat with
      | 0 => ⟨v1.w0, v1.w1⟩
      | 1 => ⟨v1.w2, v1.w3⟩
      | 2 => ⟨v2.w0, v2.w1⟩
      | _ => ⟨v2.w2, v2.w3⟩
    let lo := pick128 (imm &&& 0x0F)
    let hi := pick128 ((imm >>> 4) &&& 0x0F)
    ({ s with pc := nextPc, ymm := s.ymm.set dst ⟨lo.w0, lo.w1, hi.w0, hi.w1⟩, ymmDirty := true }, ⟨d.offset, [], true⟩)

/-- Bounded-fuel `x86_64` execution returning the final state and leakage trace `List StepObs`. -/
@[expose] def runX86 (prog : List (DecodedInstr X86Instr)) : Nat → X86State → (X86State × List StepObs)
  | 0, s => (s, [])
  | fuel + 1, s =>
    if s.halted then (s, [])
    else match findInstrAtPc s.pc prog with
    | none => ({ s with halted := true }, [])
    | some d =>
      let (s', obs) := stepX86 d s
      let (sFinal, restObs) := runX86 prog fuel s'
      (sFinal, obs :: restObs)

/-! ## §4. Fixed-Width 32-Bit `AArch64` Machine-Code Decoder + Semantics -/


end Qsag
