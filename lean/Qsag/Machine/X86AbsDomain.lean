module
public import Qsag.Machine.IsaPcMap
import Qsag.Tactic.AssuranceKit
public section
namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
  UInt64.instLawfulOrderOrd Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe
set_option autoImplicit false
set_option maxRecDepth 65536

structure X86AbsState where
  gpr : Bank16 RegOrigin
  ymm : Bank16 VecOrigin
  cfPub : Bool
  ofPub : Bool
  zfPub : Bool
  ymmDirty : Bool
  memUnmodified : Bool
  rbpSaved : Bool
  stackZeroLoop : Nat
  deriving DecidableEq, Repr

@[expose] def X86AbsState.le (a b : X86AbsState) : Bool :=
  a.gpr.allIdx (fun i oa => oa.le (b.gpr.get i)) &&
  a.ymm.allIdx (fun i va => va.le (b.ymm.get i)) &&
  (!b.cfPub || a.cfPub) &&
  (!b.ofPub || a.ofPub) &&
  (!b.zfPub || a.zfPub) &&
  (b.ymmDirty || !a.ymmDirty) &&
  (!b.memUnmodified || a.memUnmodified) &&
  (!b.rbpSaved || a.rbpSaved) &&
  (b.stackZeroLoop == 0 || a.stackZeroLoop == b.stackZeroLoop)

@[expose] def X86AbsState.join (a b : X86AbsState) : X86AbsState :=
  { gpr := Bank16.ofFn (fun i => RegOrigin.join (a.gpr.get i) (b.gpr.get i))
    ymm := Bank16.ofFn (fun i => VecOrigin.join (a.ymm.get i) (b.ymm.get i))
    cfPub := a.cfPub && b.cfPub
    ofPub := a.ofPub && b.ofPub
    zfPub := a.zfPub && b.zfPub
    ymmDirty := a.ymmDirty || b.ymmDirty
    memUnmodified := a.memUnmodified && b.memUnmodified
    rbpSaved := a.rbpSaved && b.rbpSaved
    stackZeroLoop := if a.stackZeroLoop == b.stackZeroLoop then a.stackZeroLoop else 0 }

@[expose] def isX86CalleeSavedGpr (r : Nat) : Bool :=
  r == 3 || r == 5 || r == 12 || r == 13 || r == 14 || r == 15

@[expose] def initX86AbsState (c : FuncContract) : X86AbsState :=
  { gpr := Bank16.ofFn (fun r =>
      if r ∈ c.pubGprs then .initSame r
      else if isX86CalleeSavedGpr r then .initOwn r
      else .secretVal)
    ymm := Bank16.ofFn VecOrigin.initVec
    cfPub := false
    ofPub := false
    zfPub := false
    ymmDirty := false
    memUnmodified := true
    rbpSaved := false
    stackZeroLoop := 0 }

@[expose] def x86AddrIsPublic (st : X86AbsState) : X86MemAddr → Bool
  | .baseDisp base _ => (st.gpr.get base).isPublic
  | .absDisp _ => true
  | .ripDisp _ => true
  | .indexedSib baseOpt idx _ _ =>
    (st.gpr.get idx).isPublic && match baseOpt with | none => true | some b => (st.gpr.get b).isPublic

@[expose] def isInPubMemRegion (c : FuncContract) (st : X86AbsState) (addr : X86MemAddr) (widthBytes : Nat) : Bool :=
  if !st.memUnmodified then false
  else match addr with
  | .baseDisp base disp =>
    match st.gpr.get base with
    | .initSame r =>
      r ∈ c.pubGprs &&
      c.pubMemRegions.any (fun (ptrReg, regionLen) =>
        ptrReg == r && disp.toNat + widthBytes ≤ regionLen)
    | _ => false
  | _ => false

@[expose] def storePreservesSavedRbp (c : FuncContract) (st : X86AbsState) (addr : X86MemAddr) (widthBytes : Nat) : Bool :=
  if !st.rbpSaved then false
  else if !c.usesRbpFrame then false
  else match addr with
  | .baseDisp base disp =>
    if st.gpr.get base == .frameSp && disp.toNat + widthBytes ≤ 0x320 then true
    else if st.gpr.get base == .initSame c.outPtrReg &&
            c.outBytes == 0x320 && disp.toNat + widthBytes ≤ 0x320 then true
    else if base == 0 && disp == 0 && widthBytes == 32 && st.stackZeroLoop == 1 then true
    else false
  | _ => false

/-- Publicity of a condition code, fail-closed: codes `2, 3` read `CF`, codes `4, 5` read `ZF`,
    and every other code is treated as secret-dependent because it reads flags the abstract
    state does not track (`SF`, `PF`, or `CF` and `ZF` together). -/
@[expose] def x86CondIsPublic (cc : Nat) (st : X86AbsState) : Bool :=
  if cc == 2 || cc == 3 then st.cfPub
  else if cc == 4 || cc == 5 then st.zfPub
  else false

/-- A condition code can be classified public only if its semantics are modelled. -/
theorem x86CondIsPublic_supported {cc : Nat} {st : X86AbsState}
    (h : x86CondIsPublic cc st = true) : x86CondSupported cc = true := by
  unfold x86CondIsPublic at h
  unfold x86CondSupported
  by_cases c2 : cc == 2 <;> by_cases c3 : cc == 3 <;> by_cases c4 : cc == 4 <;>
    by_cases c5 : cc == 5 <;> simp_all

@[expose] def x86AddrRegsValid : X86MemAddr → Bool
  | .baseDisp base _ => base < 16
  | .absDisp _ => true
  | .ripDisp _ => true
  | .indexedSib baseOpt idx _ _ =>
    idx < 16 && match baseOpt with | none => true | some b => b < 16

@[expose] def x86InstrRegsValid : X86Instr → Bool
  | .nop | .mfence | .ret | .vzeroupper | .vzeroall | .jcc _ _ | .jmpRel _ | .indirectBr _ | .divRem _ => true
  | .pushReg r | .popReg r | .movImm _ r _ | .aluImm _ _ r _ | .cmpImm _ r _ | .incDec _ _ r
  | .negReg _ r | .notReg _ r | .setcc _ r | .bswap _ r | .mulOneOp _ _ r | .shiftImm _ _ r _ | .varShiftCl _ r => r < 16
  | .movRegReg _ d s | .aluRegReg _ _ d s | .testRegReg _ d s | .cmpRegReg _ d s | .cmovcc _ _ d s | .adcx d s | .adox d s
  | .ssePcmpeqb d s | .ssePand d s | .ssePmovmskb d s
  | .vmovGprToXmm _ d s | .vpbroadcast _ _ d s | .vshiftImm _ _ d s _ => d < 16 && s < 16
  | .mulx h l s | .vbinOp _ _ h l s | .vpclmulqdq _ h l s _
  | .vgf2p8affineqb _ h l s _ | .vperm2i128 h l s _ => h < 16 && l < 16 && s < 16
  | .loadGpr w _ r a | .storeGpr w r a => (w == 1 || w == 8) && r < 16 && x86AddrRegsValid a
  | .lea _ r a | .sseMovdquLoad r a
  | .aluLoad64 _ r a
  | .vload _ r a | .vstore _ r a | .vpbroadcastLoad64 r a => r < 16 && x86AddrRegsValid a
  | .storeImm8 a _ => x86AddrRegsValid a
  | .vpxorLoad128 d s a | .vpxorLoad256 d s a => d < 16 && s < 16 && x86AddrRegsValid a
  | .vpgather _ a => x86AddrRegsValid a

/- Abstract transfer function for one `x86_64` instruction, returning successor `(pc, state)` pairs,
    or `none` if any constant-time (`PC-NI`, `Mem-NI`, `DOIT-NI`) or ABI hygiene rule is violated. -/
end Qsag
