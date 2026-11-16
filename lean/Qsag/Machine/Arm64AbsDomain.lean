module
public import Qsag.Machine.X86AbsTransfer
import Qsag.Tactic.AssuranceKit
public section
namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
  UInt64.instLawfulOrderOrd Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe
set_option autoImplicit false
set_option maxRecDepth 65536

inductive ArmRegOrigin where
  | initSame (r : Nat)
  | initOwn  (r : Nat)
  | zeroConst
  | pubVal
  | secretVal
  deriving @[expose] DecidableEq, Repr

@[expose] def ArmRegOrigin.isPublic : ArmRegOrigin → Bool
  | .initSame _ | .zeroConst | .pubVal => true
  | .initOwn _ | .secretVal => false

@[expose] def ArmRegOrigin.le (a b : ArmRegOrigin) : Bool :=
  a == b || b == .secretVal || (b == .pubVal && a.isPublic)

@[expose] def ArmRegOrigin.join (a b : ArmRegOrigin) : ArmRegOrigin :=
  if a == b then a
  else if a.isPublic && b.isPublic then .pubVal
  else .secretVal

structure Arm64AbsState where
  dit : Bool := true
  gpr : Bank32 ArmRegOrigin
  vec : Bank32 VecOrigin
  cfPub : Bool
  zfPub : Bool
  deriving DecidableEq, Repr

@[expose] def Arm64AbsState.le (a b : Arm64AbsState) : Bool :=
  (a.dit == b.dit) && a.gpr.allIdx (fun i oa => oa.le (b.gpr.get i)) &&
  a.vec.allIdx (fun i va => va.le (b.vec.get i)) &&
  (!b.cfPub || a.cfPub) &&
  (!b.zfPub || a.zfPub)

@[expose] def Arm64AbsState.join (a b : Arm64AbsState) : Arm64AbsState :=
  { dit := a.dit && b.dit
    gpr := Bank32.ofFn (fun i => ArmRegOrigin.join (a.gpr.get i) (b.gpr.get i))
    vec := Bank32.ofFn (fun i => VecOrigin.join (a.vec.get i) (b.vec.get i))
    cfPub := a.cfPub && b.cfPub
    zfPub := a.zfPub && b.zfPub }

@[expose] def isArm64CalleeSavedGpr (r : Nat) : Bool :=
  19 ≤ r && r ≤ 30

@[expose] def isArm64CalleeSavedVec (v : Nat) : Bool :=
  8 ≤ v && v ≤ 15

@[expose] def initArm64AbsState (c : FuncContract) : Arm64AbsState :=
  { dit := c.doitEnabled
    gpr := Bank32.ofFn (fun r =>
      if r == 31 then .zeroConst
      else if r ∈ c.pubGprs then .initSame r
      else if isArm64CalleeSavedGpr r then .initOwn r
      else .secretVal)
    vec := Bank32.ofFn VecOrigin.initVec
    cfPub := false
    zfPub := false }

@[expose] def getArmAbsGpr (st : Arm64AbsState) (r : Nat) : ArmRegOrigin :=
  if r == 31 then .zeroConst else st.gpr.get r

@[expose] def setArmAbsGpr (st : Arm64AbsState) (r : Nat) (o : ArmRegOrigin) : Bank32 ArmRegOrigin :=
  if r == 31 then st.gpr else st.gpr.set r o

@[expose] def armCondIsPublic (cond : Nat) (st : Arm64AbsState) : Bool :=
  if cond == 0 || cond == 1 then st.zfPub else st.cfPub

end Qsag
