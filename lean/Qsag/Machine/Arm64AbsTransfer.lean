module
public import Qsag.Machine.Arm64AbsDomain
import Qsag.Tactic.AssuranceKit
public section
namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
  UInt64.instLawfulOrderOrd Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe
set_option autoImplicit false
set_option maxRecDepth 65536

@[expose] def arm64InstrRegsValid : Arm64Instr → Bool
  | .nop | .msrDit _ | .isb | .dmbIsh | .ret | .bCond _ _
  | .cbzOrTbz _ | .udivOrSdiv _ | .varShiftReg _ | .regOffsetMem _ => true
  | .movWide _ _ rd _ _ => rd < 32
  | .aluImm _ _ rd rn _ | .ubfm _ rd rn _ _ | .strbPost rd rn _
  | .ldrQ rd rn _ | .strQ rd rn _ | .fmovDFromX rd rn | .vdup2d rd rn
  | .vshift2d _ rd rn _ => rd < 32 && rn < 32
  | .aluReg _ _ rd rn rm _ _ | .mulOp _ rd rn rm | .csel _ _ _ rd rn rm
  | .ldp64 rd rn rm _ | .stp64 rd rn rm _ | .veor16b rd rn rm
  | .ldpQ rd rn rm _ | .stpQ rd rn rm _ | .vand16b rd rn rm
  | .vtrn _ _ _ rd rn rm | .vrax1_2d rd rn rm | .vxar_2d rd rn rm _ | .vpmull _ rd rn rm | .vext16b rd rn rm _ =>
    rd < 32 && rn < 32 && rm < 32
  | .vbcax16b vd vn vm va | .veor3_16b vd vn vm va =>
    vd < 32 && vn < 32 && vm < 32 && va < 32



@[expose] def armRequiresDit : Arm64Instr → Bool
  | .mulOp _ _ _ _ | .csel _ _ _ _ _ _ | .vpmull _ _ _ _ => true
  | _ => false

@[expose] def transferArm64Instr (c : FuncContract) (d : DecodedInstr Arm64Instr) (st : Arm64AbsState) :
    Option (List (Nat × Arm64AbsState)) :=
  if armRequiresDit d.instr && !st.dit then none
  else if !arm64InstrRegsValid d.instr then none
  else
  let nextPc := d.offset + 4
  match d.instr with
  | .msrDit imm => some [(nextPc, { st with dit := imm != 0 })]
  | .nop | .isb | .dmbIsh =>
    some [(nextPc, st)]
  | .ret =>
    let calleeGprOk :=
      [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30].all (fun r =>
        st.gpr.get r == .initOwn r || st.gpr.get r == .initSame r)
    let calleeVecOk :=
      [8, 9, 10, 11, 12, 13, 14, 15].all (fun v => st.vec.get v == .initVec v)
    let vecWiped := st.vec.allIdx (fun _ vo => vo != .secretVal && vo != .pubVal)
    let gprWiped := c.wipedScratchGprs.all (fun r => r < 32 && getArmAbsGpr st r == .zeroConst)
    if calleeGprOk && calleeVecOk && vecWiped && gprWiped then some [] else none
  | .aluReg op _is64 rd rn rm _sk sa =>
    if op == .eor && rn == rm && sa == 0 then
      some [(nextPc, { st with gpr := setArmAbsGpr st rd .zeroConst })]
    else
      let aPub := (getArmAbsGpr st rn).isPublic
      let bPub := (getArmAbsGpr st rm).isPublic
      let cNeed := if op == .adc || op == .sbc then st.cfPub else true
      let p := aPub && bPub && cNeed
      let setsFlags := op == .adds || op == .subs
      some [(nextPc, { st with
        gpr := setArmAbsGpr st rd (if p then .pubVal else .secretVal)
        cfPub := if setsFlags then p else st.cfPub
        zfPub := if setsFlags then p else st.zfPub })]
  | .aluImm op _is64 rd rn _imm =>
    let cNeed := if op == .adc || op == .sbc then st.cfPub else true
    let p := (getArmAbsGpr st rn).isPublic && cNeed
    let setsFlags := op == .adds || op == .subs
    some [(nextPc, { st with
      gpr := setArmAbsGpr st rd (if p then .pubVal else .secretVal)
      cfPub := if setsFlags then p else st.cfPub
      zfPub := if setsFlags then p else st.zfPub })]
  | .movWide isMovn _is64 rd imm16 _sh =>
    let o : ArmRegOrigin := if !isMovn && imm16 == 0 then .zeroConst else .pubVal
    some [(nextPc, { st with gpr := setArmAbsGpr st rd o })]
  | .ubfm _is64 rd rn _immr _imms =>
    let p := (getArmAbsGpr st rn).isPublic
    some [(nextPc, { st with gpr := setArmAbsGpr st rd (if p then .pubVal else .secretVal) })]
  | .mulOp _isUmulh rd rn rm =>
    let p := (getArmAbsGpr st rn).isPublic && (getArmAbsGpr st rm).isPublic
    some [(nextPc, { st with gpr := setArmAbsGpr st rd (if p then .pubVal else .secretVal) })]
  | .csel cond _isInv _is64 rd rn rm =>
    let p := armCondIsPublic cond st && (getArmAbsGpr st rn).isPublic && (getArmAbsGpr st rm).isPublic
    some [(nextPc, { st with gpr := setArmAbsGpr st rd (if p then .pubVal else .secretVal) })]
  | .ldp64 rt1 rt2 rn _off =>
    if !(getArmAbsGpr st rn).isPublic then none
    else
      let s1 := setArmAbsGpr st rt1 .secretVal
      some [(nextPc, { st with gpr := if rt2 == 31 then s1 else s1.set rt2 .secretVal })]
  | .stp64 _rt1 _rt2 rn _off =>
    if !(getArmAbsGpr st rn).isPublic then none else some [(nextPc, st)]
  | .strbPost _rt rn _postOff =>
    if !(getArmAbsGpr st rn).isPublic then none
    else some [(nextPc, { st with gpr := setArmAbsGpr st rn .pubVal })]
  | .ldpQ rt1 rt2 rn _off =>
    if !(getArmAbsGpr st rn).isPublic then none
    else some [(nextPc, { st with vec := (st.vec.set rt1 .secretVal).set rt2 .secretVal })]
  | .stpQ _rt1 _rt2 rn _off =>
    if !(getArmAbsGpr st rn).isPublic then none else some [(nextPc, st)]
  | .vshift2d _ vd vn _ =>
    some [(nextPc, { st with vec := st.vec.set vd (if (st.vec.get vn).isPublic then .pubVal else .secretVal) })]
  | .ldrQ rt rn _off =>
    if !(getArmAbsGpr st rn).isPublic then none
    else some [(nextPc, { st with vec := st.vec.set rt .secretVal })]
  | .strQ _rt rn _off =>
    if !(getArmAbsGpr st rn).isPublic then none else some [(nextPc, st)]
  | .fmovDFromX vd xn | .vdup2d vd xn =>
    let o := getArmAbsGpr st xn
    let vo : VecOrigin :=
      if o == .zeroConst then .zeroConst else if o.isPublic then .pubVal else .secretVal
    some [(nextPc, { st with vec := st.vec.set vd vo })]
  | .veor16b vd vn vm =>
    if vn == vm then
      some [(nextPc, { st with vec := st.vec.set vd .zeroConst })]
    else
      let p := (st.vec.get vn).isPublic && (st.vec.get vm).isPublic
      some [(nextPc, { st with vec := st.vec.set vd (if p then .pubVal else .secretVal) })]
  | .vbcax16b vd vn vm va | .veor3_16b vd vn vm va =>
    let p := (st.vec.get vn).isPublic && (st.vec.get vm).isPublic && (st.vec.get va).isPublic
    some [(nextPc, { st with vec := st.vec.set vd (if p then .pubVal else .secretVal) })]
  | .vand16b vd vn vm | .vtrn _ _ _ vd vn vm | .vrax1_2d vd vn vm | .vxar_2d vd vn vm _ | .vpmull _ vd vn vm | .vext16b vd vn vm _ =>
    let p := (st.vec.get vn).isPublic && (st.vec.get vm).isPublic
    some [(nextPc, { st with vec := st.vec.set vd (if p then .pubVal else .secretVal) })]
  | .bCond cond targetPc =>
    if !armCondIsPublic cond st || targetPc < 0 || targetPc.toNat ≥ 8192 then none
    else some [(targetPc.toNat, st), (nextPc, st)]
  | .cbzOrTbz _ | .udivOrSdiv _ | .varShiftReg _ | .regOffsetMem _ =>
    none

@[expose] def mergeArm64Succs (inv : PcMap Arm64AbsState) : List (Nat × Arm64AbsState) → PcMap Arm64AbsState
  | [] => inv
  | (pc, stNew) :: rest =>
    let merged := match inv.get pc with
      | none => stNew
      | some stOld => Arm64AbsState.join stOld stNew
    mergeArm64Succs (inv.set pc merged) rest

@[expose] def propagateArm64Pass (c : FuncContract) :
    List (DecodedInstr Arm64Instr) → PcMap Arm64AbsState → Option (PcMap Arm64AbsState)
  | [], inv => some inv
  | d :: ds, inv =>
    match inv.get d.offset with
    | none => propagateArm64Pass c ds inv
    | some st =>
      match transferArm64Instr c d st with
      | none => none
      | some succs => propagateArm64Pass c ds (mergeArm64Succs inv succs)

@[expose] def inferArm64Invariant (prog : List (DecodedInstr Arm64Instr)) (c : FuncContract) :
    Option (PcMap Arm64AbsState) :=
  let inv0 := PcMap.empty.set 0 (initArm64AbsState c)
  match propagateArm64Pass c prog inv0 with
  | none => none
  | some inv1 => propagateArm64Pass c prog inv1

@[expose] def verifyArm64Invariant (prog : List (DecodedInstr Arm64Instr)) (c : FuncContract)
    (inv : PcMap Arm64AbsState) : Bool :=
  let progMap := buildProgMap prog
  let entryOk := match inv.get 0 with
    | none => false
    | some st0 => (initArm64AbsState c).le st0
  entryOk &&
  inv.all (fun pc st =>
    match progMap.get pc with
    | none => false
    | some d =>
      match transferArm64Instr c d st with
      | none => false
      | some succs =>
        succs.all (fun (npc, nst) =>
          match inv.get npc with
          | none => false
          | some dstSt => nst.le dstSt))

/-- Certified `AArch64` 3-Way Constant-Time NI + ABI Hygiene verifier. -/
@[expose] def checkArm64ThreeWayNI (code : List UInt8) (c : FuncContract) : Bool :=
  match decodeArm64Stream code with
  | none => false
  | some prog =>
    match prog with
    | [] => false
    | _ :: _ =>
      match inferArm64Invariant prog c with
      | none => false
      | some inv => verifyArm64Invariant prog c inv


/-! ### §5b. Deductive Soundness Proofs (`checkElfFuncThreeWayNI_sound`) & Inhabitedness Witnesses -/

end Qsag
