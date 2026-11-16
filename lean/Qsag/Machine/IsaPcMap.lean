module
public import Qsag.Machine.Arm64Step
import Qsag.Tactic.AssuranceKit
public section
namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
  UInt64.instLawfulOrderOrd Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe
set_option autoImplicit false
set_option maxRecDepth 65536

/-- 3-level 32×16×16 radix map (`0 .. 8191`) giving `O(1)` 3-step PC lookup in kernel `decide`. -/
structure PcMap (α : Type) where
  root : Bank32 (Option (Bank16 (Option (Bank16 (Option α)))))

@[expose] def PcMap.empty {α : Type} : PcMap α :=
  ⟨Bank32.const none⟩

@[expose] def PcMap.get {α : Type} (m : PcMap α) (pc : Nat) : Option α :=
  if pc ≥ 8192 then none
  else
    match Bank32.get m.root (pc / 256) with
    | none => none
    | some p1 =>
      match Bank16.get p1 ((pc / 16) % 16) with
      | none => none
      | some p0 => Bank16.get p0 (pc % 16)

@[expose] def PcMap.set {α : Type} (m : PcMap α) (pc : Nat) (v : α) : PcMap α :=
  if pc ≥ 8192 then m
  else
    let i2 := pc / 256
    let i1 := (pc / 16) % 16
    let i0 := pc % 16
    let p1 := match Bank32.get m.root i2 with | some b => b | none => Bank16.const none
    let p0 := match Bank16.get p1 i1 with | some b => b | none => Bank16.const none
    let p0' := Bank16.set p0 i0 (some v)
    let p1' := Bank16.set p1 i1 (some p0')
    ⟨Bank32.set m.root i2 (some p1')⟩

@[expose] def PcMap.all {α : Type} (pred : Nat → α → Bool) (m : PcMap α) : Bool :=
  Bank32.allIdx (fun i2 opt1 =>
    match opt1 with
    | none => true
    | some p1 =>
      Bank16.allIdx (fun i1 opt0 =>
        match opt0 with
        | none => true
        | some p0 =>
          Bank16.allIdx (fun i0 optV =>
            match optV with
            | none => true
            | some v => pred (i2 * 256 + i1 * 16 + i0) v) p0) p1) m.root

/-- Function-level constant-time & ABI hygiene contract $\Gamma$.

    `doitEnabled` records whether the contract assumes the processor runs the function in
    data-operand-independent-timing mode (`IA32_UARCH_MISC_CTL[DOITM] = 1` on `x86_64`). User-mode
    code cannot change that bit, so it is an assumption about the execution environment and not
    part of `X86State`. The `x86_64` checker consults it: `transferX86Instr` rejects `cmovcc`
    when it is `false`. `AArch64` tracks `PSTATE.DIT` in its machine state instead. -/
structure FuncContract where
  symName : String
  pubGprs : List Nat
  pubMemRegions : List (Nat × Nat)
  wipedScratchGprs : List Nat
  usesRbpFrame : Bool
  outPtrReg : Nat
  outBytes : Nat
  doitEnabled : Bool := true
  deriving DecidableEq, Repr

/-- Abstract origin lattice for `x86_64` GPRs tracking relational publicity + callee-saved/frame origins. -/
inductive RegOrigin where
  | initSame (r : Nat)
  | initOwn  (r : Nat)
  | spMinus8
  | spAligned32
  | frameSp
  | zeroConst
  | constVal (c : UInt64)
  | pubVal
  | secretVal
  deriving @[expose] DecidableEq, Repr

@[expose] def RegOrigin.isPublic : RegOrigin → Bool
  | .initSame _ | .spMinus8 | .spAligned32 | .frameSp | .zeroConst | .constVal _ | .pubVal => true
  | .initOwn _ | .secretVal => false

@[expose] def RegOrigin.le (a b : RegOrigin) : Bool :=
  a == b || b == .secretVal || (b == .pubVal && a.isPublic)

@[expose] def RegOrigin.join (a b : RegOrigin) : RegOrigin :=
  if a == b then a
  else if a.isPublic && b.isPublic then .pubVal
  else .secretVal

/-- Abstract origin lattice for SIMD vector registers (`ymm0..ymm15` / `v0..v31`). -/
inductive VecOrigin where
  | initVec (r : Nat)
  | zeroConst
  | pubVal
  | secretVal
  deriving @[expose] DecidableEq, Repr

@[expose] def VecOrigin.isPublic : VecOrigin → Bool
  | .zeroConst | .pubVal => true
  | .initVec _ | .secretVal => false

@[expose] def VecOrigin.le (a b : VecOrigin) : Bool :=
  a == b || b == .secretVal || (b == .pubVal && a.isPublic)

@[expose] def VecOrigin.join (a b : VecOrigin) : VecOrigin :=
  if a == b then a
  else if a.isPublic && b.isPublic then .pubVal
  else .secretVal

/- Abstract relational state at a single `x86_64` PC. -/
end Qsag
