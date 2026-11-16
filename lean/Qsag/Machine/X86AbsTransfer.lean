module
public import Qsag.Machine.X86Policy
import Qsag.Tactic.AssuranceKit
public section
namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
  UInt64.instLawfulOrderOrd Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe
set_option autoImplicit false
set_option maxRecDepth 65536

@[expose] def transferX86Instr (c : FuncContract) (d : DecodedInstr X86Instr) (st : X86AbsState) :
    Option (List (Nat × X86AbsState)) :=
  if x86ViolatesPolicy c d.instr st then none else
  if !x86InstrRegsValid d.instr then none
  else
  let nextPc := d.offset + d.byteLen
  let stNoLoop := { st with stackZeroLoop := 0 }
  -- Used by the epilogue steps that write no memory: a completed frame wipe (`4`) stays valid.
  let stKeep := { st with stackZeroLoop := if st.stackZeroLoop == 4 then 4 else 0 }
  match d.instr with
  | .nop | .mfence =>
    some [(nextPc, stNoLoop)]
  | .pushReg r =>
    if c.usesRbpFrame && r == 5 && st.gpr.get 4 == .initSame 4 && st.gpr.get 5 == .initOwn 5 &&
       4 ∈ c.pubGprs && !st.rbpSaved then
      some [(nextPc, { stNoLoop with
        gpr := st.gpr.set 4 .spMinus8
        memUnmodified := false
        rbpSaved := true })]
    else none
  | .popReg r =>
    if c.usesRbpFrame && r == 5 && st.gpr.get 4 == .spMinus8 && st.rbpSaved then
      some [(nextPc, { stKeep with
        gpr := (st.gpr.set 4 (.initSame 4)).set 5 (.initOwn 5) })]
    else none
  | .ret =>
    let spOk := st.gpr.get 4 == .initSame 4 && 4 ∈ c.pubGprs
    let calleeOk :=
      (st.gpr.get 3).le (.initOwn 3) || st.gpr.get 3 == .initSame 3
    let allCalleeOk :=
      calleeOk &&
      ([3, 5, 12, 13, 14, 15].all (fun r =>
        st.gpr.get r == .initOwn r || st.gpr.get r == .initSame r))
    let ymmClean := !st.ymmDirty
    let vecWiped := st.ymm.allIdx (fun _ vo => vo != .secretVal && vo != .pubVal)
    let gprWiped := c.wipedScratchGprs.all (fun r => st.gpr.get r == .zeroConst)
    -- A frame-allocating kernel may only return once its spill area has been wiped.
    let frameOk := !c.usesRbpFrame || st.stackZeroLoop == 4
    if spOk && allCalleeOk && ymmClean && vecWiped && gprWiped && frameOk then some [] else none
  | .movRegReg is64 dst src =>
    if is64 && dst == 0 && src == 4 && st.gpr.get 4 == .frameSp &&
       st.gpr.get 1 == .constVal 25 then
      some [(nextPc, { stNoLoop with
        gpr := (st.gpr.set 0 .pubVal).set 1 .pubVal
        stackZeroLoop := 1 })]
    else
      let orig :=
        if is64 then st.gpr.get src
        else if (st.gpr.get src).isPublic then .pubVal else .secretVal
      some [(nextPc, { stKeep with gpr := st.gpr.set dst orig })]
  | .movImm is64 dst imm =>
    let v := maskGprWidth is64 imm
    let orig : RegOrigin := if v == 0 then .zeroConst else .constVal v
    some [(nextPc, { stNoLoop with gpr := st.gpr.set dst orig })]
  | .loadGpr wBytes _is64 dst addr =>
    if !x86AddrIsPublic st addr then none
    else
      let orig : RegOrigin := if isInPubMemRegion c st addr wBytes then .pubVal else .secretVal
      some [(nextPc, { stNoLoop with gpr := st.gpr.set dst orig })]
  | .storeGpr wBytes _src addr =>
    if !x86AddrIsPublic st addr then none
    else
      let rbpOk := if st.rbpSaved then storePreservesSavedRbp c st addr wBytes else false
      some [(nextPc, { stNoLoop with memUnmodified := false, rbpSaved := rbpOk })]
  | .aluRegReg op _is64 dst src =>
    if op == .xorOp && dst == src then
      some [(nextPc, { stKeep with
        gpr := st.gpr.set dst .zeroConst
        cfPub := true, ofPub := true, zfPub := true })]
    else if op == .sbb && dst == src then
      let resOrig : RegOrigin := if st.cfPub then .pubVal else .secretVal
      some [(nextPc, { stNoLoop with
        gpr := st.gpr.set dst resOrig
        cfPub := st.cfPub, zfPub := st.cfPub })]
    else
      let aPub := (st.gpr.get dst).isPublic
      let bPub := (st.gpr.get src).isPublic
      let carryNeed := if op == .adc || op == .sbb then st.cfPub else true
      let bothPub := aPub && bPub && carryNeed
      let of' := if op == .andOp || op == .orOp || op == .xorOp then true else false
      some [(nextPc, { stNoLoop with
        gpr := st.gpr.set dst (if bothPub then .pubVal else .secretVal)
        cfPub := bothPub, ofPub := of', zfPub := bothPub })]
  | .aluLoad64 op dst addr =>
    if !x86AddrIsPublic st addr then none
    else
      let mPub := isInPubMemRegion c st addr 8
      let bothPub := (st.gpr.get dst).isPublic && mPub &&
                     (if op == .adc || op == .sbb then st.cfPub else true)
      let of' := if op == .andOp || op == .orOp || op == .xorOp then true else false
      some [(nextPc, { stNoLoop with
        gpr := st.gpr.set dst (if bothPub then .pubVal else .secretVal)
        cfPub := bothPub, ofPub := of', zfPub := bothPub })]
  | .aluImm op is64 dst imm =>
    if is64 && op == .andOp && dst == 4 && imm == 0xFFFFFFFFFFFFFFE0 && st.gpr.get 4 == .spMinus8 then
      some [(nextPc, { stNoLoop with
        gpr := st.gpr.set 4 .spAligned32
        cfPub := true, ofPub := true, zfPub := true })]
    else if is64 && op == .sub && dst == 4 && imm == 0x340 && st.gpr.get 4 == .spAligned32 then
      some [(nextPc, { stNoLoop with
        gpr := st.gpr.set 4 .frameSp
        cfPub := true, ofPub := false, zfPub := true })]
    else if is64 && op == .add && dst == 0 && imm == 0x20 && st.stackZeroLoop == 5 then
      some [(nextPc, { st with
        gpr := st.gpr.set 0 .pubVal
        cfPub := true, ofPub := false, zfPub := true
        stackZeroLoop := 2 })]
    else
      let aPub := (st.gpr.get dst).isPublic
      let carryNeed := if op == .adc || op == .sbb then st.cfPub else true
      let bothPub := aPub && carryNeed
      let of' := if op == .andOp || op == .orOp || op == .xorOp then true else false
      some [(nextPc, { stNoLoop with
        gpr := st.gpr.set dst (if bothPub then .pubVal else .secretVal)
        cfPub := bothPub, ofPub := of', zfPub := bothPub })]
  | .incDec isInc is64 dst =>
    if !isInc && !is64 && dst == 1 && st.stackZeroLoop == 2 then
      some [(nextPc, { st with
        gpr := st.gpr.set 1 .pubVal
        ofPub := true
        zfPub := true
        stackZeroLoop := 3 })]
    else
      let p := (st.gpr.get dst).isPublic
      some [(nextPc, { stNoLoop with
        gpr := st.gpr.set dst (if p then .pubVal else .secretVal)
        ofPub := p
        zfPub := p })]
  | .negReg _is64 dst =>
    let p := (st.gpr.get dst).isPublic
    some [(nextPc, { stNoLoop with
      gpr := st.gpr.set dst (if p then .pubVal else .secretVal)
      cfPub := p, ofPub := p, zfPub := p })]
  | .mulOneOp _isSigned _is64 src =>
    let p := (st.gpr.get 0).isPublic && (st.gpr.get src).isPublic
    let o : RegOrigin := if p then .pubVal else .secretVal
    some [(nextPc, { stNoLoop with
      gpr := (st.gpr.set 0 o).set 2 o
      cfPub := false, ofPub := false, zfPub := false })]
  | .shiftImm sk is64 dst cnt =>
    let p := (st.gpr.get dst).isPublic
    some [(nextPc, { stNoLoop with
      gpr := st.gpr.set dst (if p then .pubVal else .secretVal)
      cfPub := false, ofPub := false,
      zfPub := if x86ShiftPreservesZf sk is64 cnt then st.zfPub else p })]
  | .cmovcc cc _is64 dst src =>
    -- Rejected unless the condition code is modelled and the contract assumes `DOITM`:
    -- `CMOVcc` is data-operand-independent only in that mode.
    if !x86CondSupported cc || !c.doitEnabled then none
    else
      let cPub := x86CondIsPublic cc st
      let p := cPub && (st.gpr.get dst).isPublic && (st.gpr.get src).isPublic
      some [(nextPc, { stNoLoop with gpr := st.gpr.set dst (if p then .pubVal else .secretVal) })]
  | .testRegReg _is64 r1 r2 =>
    let p := (st.gpr.get r1).isPublic && (st.gpr.get r2).isPublic
    some [(nextPc, { stNoLoop with cfPub := true, ofPub := true, zfPub := p })]
  | .cmpRegReg _is64 dst src =>
    let p := (st.gpr.get dst).isPublic && (st.gpr.get src).isPublic
    some [(nextPc, { stNoLoop with cfPub := p, ofPub := p, zfPub := p })]
  | .cmpImm _is64 dst _imm =>
    let p := (st.gpr.get dst).isPublic
    some [(nextPc, { stNoLoop with cfPub := p, ofPub := p, zfPub := p })]
  | .lea _is64 dst addr =>
    let p := x86AddrIsPublic st addr
    some [(nextPc, { stNoLoop with gpr := st.gpr.set dst (if p then .pubVal else .secretVal) })]
  | .storeImm8 addr _imm =>
    if !x86AddrIsPublic st addr then none
    else
      let rbpOk := if st.rbpSaved then storePreservesSavedRbp c st addr 1 else false
      some [(nextPc, { stNoLoop with memUnmodified := false, rbpSaved := rbpOk })]
  | .notReg _is64 dst =>
    let p := (st.gpr.get dst).isPublic
    some [(nextPc, { stNoLoop with gpr := st.gpr.set dst (if p then .pubVal else .secretVal) })]
  | .setcc cc dst =>
    if !x86CondSupported cc then none
    else
      let p := x86CondIsPublic cc st && (st.gpr.get dst).isPublic
      some [(nextPc, { stNoLoop with gpr := st.gpr.set dst (if p then .pubVal else .secretVal) })]
  | .bswap _is64 dst =>
    let p := (st.gpr.get dst).isPublic
    some [(nextPc, { stNoLoop with gpr := st.gpr.set dst (if p then .pubVal else .secretVal) })]
  | .sseMovdquLoad dst addr =>
    if !x86AddrIsPublic st addr then none
    else
      some [(nextPc, { stNoLoop with ymm := st.ymm.set dst .secretVal })]
  | .ssePcmpeqb dst _src =>
    some [(nextPc, { stNoLoop with ymm := st.ymm.set dst .secretVal })]
  | .ssePand dst _src =>
    some [(nextPc, { stNoLoop with ymm := st.ymm.set dst .secretVal })]
  | .ssePmovmskb dst src =>
    let p := (st.ymm.get src).isPublic
    some [(nextPc, { stNoLoop with gpr := st.gpr.set dst (if p then .pubVal else .secretVal) })]
  | .mulx hiDst loDst src =>
    let p := (st.gpr.get 2).isPublic && (st.gpr.get src).isPublic
    let o : RegOrigin := if p then .pubVal else .secretVal
    some [(nextPc, { stNoLoop with gpr := (st.gpr.set loDst o).set hiDst o })]
  | .adcx dst src =>
    let p := (st.gpr.get dst).isPublic && (st.gpr.get src).isPublic && st.cfPub
    some [(nextPc, { stNoLoop with
      gpr := st.gpr.set dst (if p then .pubVal else .secretVal)
      cfPub := p })]
  | .adox dst src =>
    let p := (st.gpr.get dst).isPublic && (st.gpr.get src).isPublic && st.ofPub
    some [(nextPc, { stNoLoop with
      gpr := st.gpr.set dst (if p then .pubVal else .secretVal)
      ofPub := p })]
  | .jcc cc targetPc =>
    if !x86CondIsPublic cc st || targetPc < 0 || targetPc.toNat ≥ 8192 then none
    else if st.stackZeroLoop == 3 && cc == 5 then
      some [(targetPc.toNat, { st with stackZeroLoop := 1 }), (nextPc, { st with stackZeroLoop := 4 })]
    else
      some [(targetPc.toNat, stNoLoop), (nextPc, stNoLoop)]
  | .jmpRel targetPc =>
    if targetPc < 0 || targetPc.toNat ≥ 8192 then none
    else some [(targetPc.toNat, stNoLoop)]
  | .indirectBr _ | .divRem _ | .varShiftCl _ _ | .vpgather _ _ =>
    none
  | .vzeroupper =>
    let ymmPreserved := Bank16.ofFn (fun i =>
      match st.ymm.get i with
      | .zeroConst => VecOrigin.zeroConst
      | .pubVal => VecOrigin.pubVal
      | .initVec r => VecOrigin.initVec r
      | .secretVal => VecOrigin.secretVal)
    some [(nextPc, { stKeep with ymm := ymmPreserved, ymmDirty := false })]
  | .vzeroall =>
    some [(nextPc, { stKeep with ymm := Bank16.ofFn (fun _ => .zeroConst), ymmDirty := false })]
  | .vload is256 dst addr =>
    if !x86AddrIsPublic st addr then none
    else
      let w := if is256 then 32 else 16
      let vo : VecOrigin := if isInPubMemRegion c st addr w then .pubVal else .secretVal
      some [(nextPc, { stNoLoop with
        ymm := st.ymm.set dst vo
        ymmDirty := st.ymmDirty || is256 })]
  | .vstore is256 src addr =>
    if !x86AddrIsPublic st addr then none
    else
      let w := if is256 then 32 else 16
      let rbpOk := if st.rbpSaved then storePreservesSavedRbp c st addr w else false
      let nextLoop :=
        if st.stackZeroLoop == 1 && addr == .baseDisp 0 0 && is256 && st.ymm.get src == .zeroConst
        then 5 else 0
      some [(nextPc, { st with
        memUnmodified := false
        rbpSaved := rbpOk
        stackZeroLoop := nextLoop })]
  | .vmovGprToXmm _is64 dstVec srcGpr =>
    let vo : VecOrigin :=
      if st.gpr.get srcGpr == .zeroConst then .zeroConst
      else if (st.gpr.get srcGpr).isPublic then .pubVal
      else .secretVal
    some [(nextPc, { stNoLoop with ymm := st.ymm.set dstVec vo })]
  | .vpbroadcast _isQword is256 dst srcVec =>
    let svo := st.ymm.get srcVec
    let vo : VecOrigin :=
      if svo == .zeroConst then .zeroConst else if svo.isPublic then .pubVal else .secretVal
    some [(nextPc, { stNoLoop with ymm := st.ymm.set dst vo, ymmDirty := st.ymmDirty || is256 })]
  | .vpbroadcastLoad64 dst addr =>
    if !x86AddrIsPublic st addr then none
    else
      let vo : VecOrigin := if isInPubMemRegion c st addr 8 then .pubVal else .secretVal
      some [(nextPc, { stNoLoop with ymm := st.ymm.set dst vo, ymmDirty := true })]
  | .vbinOp op is256 dst src1 src2 =>
    if op == .vpxor && src1 == src2 then
      some [(nextPc, { stKeep with
        ymm := st.ymm.set dst .zeroConst
        ymmDirty := st.ymmDirty || is256 })]
    else
      let p := (st.ymm.get src1).isPublic && (st.ymm.get src2).isPublic
      some [(nextPc, { stKeep with
        ymm := st.ymm.set dst (if p then .pubVal else .secretVal)
        ymmDirty := st.ymmDirty || is256 })]
  | .vpxorLoad128 dst src1 addr =>
    if !x86AddrIsPublic st addr then none
    else
      let p := (st.ymm.get src1).isPublic && isInPubMemRegion c st addr 16
      some [(nextPc, { stNoLoop with
        ymm := st.ymm.set dst (if p then .pubVal else .secretVal)
        ymmDirty := st.ymmDirty })]
  | .vpxorLoad256 dst src1 addr =>
    if !x86AddrIsPublic st addr then none
    else
      let p := (st.ymm.get src1).isPublic && isInPubMemRegion c st addr 32
      some [(nextPc, { stNoLoop with
        ymm := st.ymm.set dst (if p then .pubVal else .secretVal)
        ymmDirty := true })]
  | .vshiftImm _sk is256 dst src _imm =>
    let svo := st.ymm.get src
    let vo : VecOrigin :=
      if svo == .zeroConst then .zeroConst else if svo.isPublic then .pubVal else .secretVal
    some [(nextPc, { stNoLoop with
      ymm := st.ymm.set dst vo
      ymmDirty := st.ymmDirty || is256 })]
  | .vpclmulqdq is256 dst src1 src2 _imm =>
    let p := (st.ymm.get src1).isPublic && (st.ymm.get src2).isPublic
    some [(nextPc, { stNoLoop with
      ymm := st.ymm.set dst (if p then .pubVal else .secretVal)
      ymmDirty := st.ymmDirty || is256 })]
  | .vgf2p8affineqb is256 dst src1 src2 _imm =>
    let p := (st.ymm.get src1).isPublic && (st.ymm.get src2).isPublic
    some [(nextPc, { stNoLoop with
      ymm := st.ymm.set dst (if p then .pubVal else .secretVal)
      ymmDirty := st.ymmDirty || is256 })]
  | .vperm2i128 dst src1 src2 _imm =>
    let p := (st.ymm.get src1).isPublic && (st.ymm.get src2).isPublic
    some [(nextPc, { stNoLoop with
      ymm := st.ymm.set dst (if p then .pubVal else .secretVal)
      ymmDirty := true })]

@[expose] def mergeX86Succs (inv : PcMap X86AbsState) : List (Nat × X86AbsState) → PcMap X86AbsState
  | [] => inv
  | (pc, stNew) :: rest =>
    let merged := match inv.get pc with
      | none => stNew
      | some stOld => X86AbsState.join stOld stNew
    mergeX86Succs (inv.set pc merged) rest

@[expose] def propagateX86Pass (c : FuncContract) : List (DecodedInstr X86Instr) → PcMap X86AbsState → Option (PcMap X86AbsState)
  | [], inv => some inv
  | d :: ds, inv =>
    match inv.get d.offset with
    | none => propagateX86Pass c ds inv
    | some st =>
      match transferX86Instr c d st with
      | none => none
      | some succs => propagateX86Pass c ds (mergeX86Succs inv succs)

@[expose] def buildProgMap {Instr : Type} : List (DecodedInstr Instr) → PcMap (DecodedInstr Instr)
  | [] => PcMap.empty
  | d :: ds => (buildProgMap ds).set d.offset d

@[expose] def inferX86Invariant (prog : List (DecodedInstr X86Instr)) (c : FuncContract) : Option (PcMap X86AbsState) := do
  let inv0 := PcMap.empty.set 0 (initX86AbsState c)
  let inv1 ← propagateX86Pass c prog inv0
  let inv2 ← propagateX86Pass c prog inv1
  let inv3 ← propagateX86Pass c prog inv2
  propagateX86Pass c prog inv3

@[expose] def verifyX86Invariant (prog : List (DecodedInstr X86Instr)) (c : FuncContract) (inv : PcMap X86AbsState) : Bool :=
  let progMap := buildProgMap prog
  let entryOk := match inv.get 0 with
    | none => false
    | some st0 => (initX86AbsState c).le st0
  entryOk &&
  inv.all (fun pc st =>
    match progMap.get pc with
    | none => false
    | some d =>
      match transferX86Instr c d st with
      | none => false
      | some succs =>
        succs.all (fun (npc, nst) =>
          match inv.get npc with
          | none => false
          | some dstSt => nst.le dstSt))

/-- Certified `x86_64` 3-Way Constant-Time NI + ABI Hygiene verifier. -/
@[expose] def checkX86ThreeWayNI (code : List UInt8) (c : FuncContract) : Bool :=
  match decodeX86Stream code with
  | none => false
  | some prog =>
    match prog with
    | [] => false
    | _ :: _ =>
      match inferX86Invariant prog c with
      | none => false
      | some inv => verifyX86Invariant prog c inv

/-! ### `AArch64` Abstract Domain, Invariant Synthesis & Deductive Certificate Checker -/


end Qsag
