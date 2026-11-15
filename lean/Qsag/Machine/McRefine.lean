module
/-
# Qsag.Machine.McRefine — input/output refinement of decoded `qsag-asm` machine code

Each `*_mc_refines` theorem looks a symbol up in the extracted fixture slices, decodes its bytes
with the `ElfBinaryVerify` decoders, and relates the final state of the bounded-fuel machine run
(`runX86` / `runArm64`) to a specification stated over the initial registers and memory only.
-/

public import Qsag.Machine.ElfBinaryVerify
import all Qsag.Machine.ElfBinaryVerify
import all Qsag.Machine.ElfParse
import Qsag.Math.Constructive
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd

set_option autoImplicit false

/-! ## §1. Run laws: one-step unfolding and halting -/

theorem runX86_halted_fst (prog : List (DecodedInstr X86Instr)) (fuel : Nat) (s : X86State)
    (h : s.halted = true) : (runX86 prog fuel s).1 = s := by
  cases fuel with
  | zero => rfl
  | succ k =>
    have e : runX86 prog (k + 1) s = (if s.halted then (s, []) else
        match findInstrAtPc s.pc prog with
        | none => ({ s with halted := true }, [])
        | some d =>
          let (s', obs) := stepX86 d s
          let (sFinal, restObs) := runX86 prog k s'
          (sFinal, obs :: restObs)) := by rfl
    rw [e, h]
    rfl

theorem runX86_step_fst (prog : List (DecodedInstr X86Instr)) (fuel : Nat) (s : X86State)
    (d : DecodedInstr X86Instr) (hh : s.halted = false) (hf : findInstrAtPc s.pc prog = some d) :
    (runX86 prog (fuel + 1) s).1 = (runX86 prog fuel (stepX86 d s).1).1 := by
  have e : runX86 prog (fuel + 1) s = (if s.halted then (s, []) else
      match findInstrAtPc s.pc prog with
      | none => ({ s with halted := true }, [])
      | some d =>
        let (s', obs) := stepX86 d s
        let (sFinal, restObs) := runX86 prog fuel s'
        (sFinal, obs :: restObs)) := by rfl
  rw [e, hh, hf]
  rfl

theorem runArm64_halted_fst (prog : List (DecodedInstr Arm64Instr)) (fuel : Nat) (s : Arm64State)
    (h : s.halted = true) : (runArm64 prog fuel s).1 = s := by
  cases fuel with
  | zero => rfl
  | succ k =>
    have e : runArm64 prog (k + 1) s = (if s.halted then (s, []) else
        match findInstrAtPc s.pc prog with
        | none => ({ s with halted := true }, [])
        | some d =>
          let (s', obs) := stepArm64 d s
          let (sFinal, restObs) := runArm64 prog k s'
          (sFinal, obs :: restObs)) := by rfl
    rw [e, h]
    rfl

theorem runArm64_step_fst (prog : List (DecodedInstr Arm64Instr)) (fuel : Nat) (s : Arm64State)
    (d : DecodedInstr Arm64Instr) (hh : s.halted = false) (hf : findInstrAtPc s.pc prog = some d) :
    (runArm64 prog (fuel + 1) s).1 = (runArm64 prog fuel (stepArm64 d s).1).1 := by
  have e : runArm64 prog (fuel + 1) s = (if s.halted then (s, []) else
      match findInstrAtPc s.pc prog with
      | none => ({ s with halted := true }, [])
      | some d =>
        let (s', obs) := stepArm64 d s
        let (sFinal, restObs) := runArm64 prog fuel s'
        (sFinal, obs :: restObs)) := by rfl
  rw [e, hh, hf]
  rfl

/-! ## §2. Register-bank literals -/

section BankLits
variable {α : Type} (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 v : α)

theorem b16get_0 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 0 = r0 := by rfl
theorem b16get_1 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 1 = r1 := by rfl
theorem b16get_2 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 2 = r2 := by rfl
theorem b16get_3 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 3 = r3 := by rfl
theorem b16get_4 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 4 = r4 := by rfl
theorem b16get_5 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 5 = r5 := by rfl
theorem b16get_6 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 6 = r6 := by rfl
theorem b16get_7 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 7 = r7 := by rfl
theorem b16get_8 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 8 = r8 := by rfl
theorem b16get_9 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 9 = r9 := by rfl
theorem b16get_10 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 10 = r10 := by rfl
theorem b16get_11 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 11 = r11 := by rfl
theorem b16get_12 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 12 = r12 := by rfl
theorem b16get_13 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 13 = r13 := by rfl
theorem b16get_14 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 14 = r14 := by rfl
theorem b16get_15 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 15 = r15 := by rfl
theorem b16set_0 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 0 v = Bank16.mk v r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 := by rfl
theorem b16set_1 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 1 v = Bank16.mk r0 v r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 := by rfl
theorem b16set_2 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 2 v = Bank16.mk r0 r1 v r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 := by rfl
theorem b16set_3 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 3 v = Bank16.mk r0 r1 r2 v r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 := by rfl
theorem b16set_4 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 4 v = Bank16.mk r0 r1 r2 r3 v r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 := by rfl
theorem b16set_5 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 5 v = Bank16.mk r0 r1 r2 r3 r4 v r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 := by rfl
theorem b16set_6 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 6 v = Bank16.mk r0 r1 r2 r3 r4 r5 v r7 r8 r9 r10 r11 r12 r13 r14 r15 := by rfl
theorem b16set_7 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 7 v = Bank16.mk r0 r1 r2 r3 r4 r5 r6 v r8 r9 r10 r11 r12 r13 r14 r15 := by rfl
theorem b16set_8 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 8 v = Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 v r9 r10 r11 r12 r13 r14 r15 := by rfl
theorem b16set_9 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 9 v = Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 v r10 r11 r12 r13 r14 r15 := by rfl
theorem b16set_10 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 10 v = Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 v r11 r12 r13 r14 r15 := by rfl
theorem b16set_11 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 11 v = Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 v r12 r13 r14 r15 := by rfl
theorem b16set_12 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 12 v = Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 v r13 r14 r15 := by rfl
theorem b16set_13 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 13 v = Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 v r14 r15 := by rfl
theorem b16set_14 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 14 v = Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 v r15 := by rfl
theorem b16set_15 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 15 v = Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 v := by rfl
end BankLits

/-- AArch64 register read with `x31` as the zero register (the bank-level form of `getArmGpr`). -/
def armGet (g : Bank32 UInt64) (r : Nat) : UInt64 := if r == 31 then 0 else g.get r

/-- AArch64 register write discarding writes to `x31` (the bank-level form of `setArmGpr`). -/
def armSet (g : Bank32 UInt64) (r : Nat) (v : UInt64) : Bank32 UInt64 := if r == 31 then g else g.set r v

theorem armGet_31 (g : Bank32 UInt64) : armGet g 31 = 0 := by rfl
theorem armSet_31 (g : Bank32 UInt64) (v : UInt64) : armSet g 31 v = g := by rfl

section ArmBankLits
variable (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 v : UInt64) (hi : Bank16 UInt64)

theorem armGet_0 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 0 = r0 := by rfl
theorem armGet_1 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 1 = r1 := by rfl
theorem armGet_2 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 2 = r2 := by rfl
theorem armGet_3 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 3 = r3 := by rfl
theorem armGet_4 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 4 = r4 := by rfl
theorem armGet_5 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 5 = r5 := by rfl
theorem armGet_6 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 6 = r6 := by rfl
theorem armGet_7 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 7 = r7 := by rfl
theorem armGet_8 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 8 = r8 := by rfl
theorem armGet_9 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 9 = r9 := by rfl
theorem armGet_10 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 10 = r10 := by rfl
theorem armGet_11 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 11 = r11 := by rfl
theorem armGet_12 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 12 = r12 := by rfl
theorem armGet_13 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 13 = r13 := by rfl
theorem armGet_14 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 14 = r14 := by rfl
theorem armGet_15 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 15 = r15 := by rfl
theorem armSet_0 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 0 v = Bank32.mk (Bank16.mk v r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi := by rfl
theorem armSet_1 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 1 v = Bank32.mk (Bank16.mk r0 v r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi := by rfl
theorem armSet_2 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 2 v = Bank32.mk (Bank16.mk r0 r1 v r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi := by rfl
theorem armSet_3 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 3 v = Bank32.mk (Bank16.mk r0 r1 r2 v r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi := by rfl
theorem armSet_4 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 4 v = Bank32.mk (Bank16.mk r0 r1 r2 r3 v r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi := by rfl
theorem armSet_5 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 5 v = Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 v r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi := by rfl
theorem armSet_6 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 6 v = Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 v r7 r8 r9 r10 r11 r12 r13 r14 r15) hi := by rfl
theorem armSet_7 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 7 v = Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 v r8 r9 r10 r11 r12 r13 r14 r15) hi := by rfl
theorem armSet_8 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 8 v = Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 v r9 r10 r11 r12 r13 r14 r15) hi := by rfl
theorem armSet_9 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 9 v = Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 v r10 r11 r12 r13 r14 r15) hi := by rfl
theorem armSet_10 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 10 v = Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 v r11 r12 r13 r14 r15) hi := by rfl
theorem armSet_11 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 11 v = Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 v r12 r13 r14 r15) hi := by rfl
theorem armSet_12 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 12 v = Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 v r13 r14 r15) hi := by rfl
theorem armSet_13 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 13 v = Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 v r14 r15) hi := by rfl
theorem armSet_14 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 14 v = Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 v r15) hi := by rfl
theorem armSet_15 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 15 v = Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 v) hi := by rfl
end ArmBankLits

/-! ## §3. `x86_64` step lemmas, one per instruction form, on a state given by its fields -/

/-- Program counter after a conditional jump. -/
def jccPc (taken : Bool) (tgt : Int) (next : Nat) : Nat :=
  if taken && decide (tgt ≥ 0) then tgt.toNat else next

theorem jccPc_false (tgt : Int) (next : Nat) : jccPc false tgt next = next := by rfl
theorem jccPc_true_5 (next : Nat) : jccPc true 5 next = 5 := by rfl
theorem jccPc_true_0 (next : Nat) : jccPc true 0 next = 0 := by rfl
theorem maskGprWidth_true (v : UInt64) : maskGprWidth true v = v := by rfl

section X86Steps
variable (off len pc : Nat) (g : Bank16 UInt64) (y : Bank16 Vec256) (cf o zf dy : Bool)
  (m : UInt64 → UInt8)

theorem stepX86_load64 (dst base : Nat) (disp : UInt64) :
    (stepX86 ⟨off, len, .loadGpr 8 true dst (.baseDisp base disp)⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (readMem64 m (g.get base + disp)), y, cf, o, zf, dy, false, m⟩ := by rfl

theorem stepX86_load8 (dst base : Nat) (disp : UInt64) :
    (stepX86 ⟨off, len, .loadGpr 1 false dst (.baseDisp base disp)⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (maskGprWidth false (m (g.get base + disp)).toUInt64), y, cf, o, zf, dy, false, m⟩ := by
  rfl

theorem stepX86_store8 (src base : Nat) (disp : UInt64) :
    (stepX86 ⟨off, len, .storeGpr 1 src (.baseDisp base disp)⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g, y, cf, o, zf, dy, false, writeMem8 m (g.get base + disp) (g.get src).toUInt8⟩ := by rfl

theorem stepX86_xorLoad64 (dst base : Nat) (disp : UInt64) :
    (stepX86 ⟨off, len, .aluLoad64 .xorOp dst (.baseDisp base disp)⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (g.get dst ^^^ readMem64 m (g.get base + disp)), y, false, false,
        (g.get dst ^^^ readMem64 m (g.get base + disp)) == 0, dy, false, m⟩ := by rfl

theorem stepX86_xorRR (is64 : Bool) (dst src : Nat) :
    (stepX86 ⟨off, len, .aluRegReg .xorOp is64 dst src⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (maskGprWidth is64 (g.get dst ^^^ g.get src)), y, false, false,
        maskGprWidth is64 (g.get dst ^^^ g.get src) == 0, dy, false, m⟩ := by rfl

theorem stepX86_orRR (is64 : Bool) (dst src : Nat) :
    (stepX86 ⟨off, len, .aluRegReg .orOp is64 dst src⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (maskGprWidth is64 (g.get dst ||| g.get src)), y, false, false,
        maskGprWidth is64 (g.get dst ||| g.get src) == 0, dy, false, m⟩ := by rfl

theorem stepX86_xorImm (is64 : Bool) (dst : Nat) (imm : UInt64) :
    (stepX86 ⟨off, len, .aluImm .xorOp is64 dst imm⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (maskGprWidth is64 (g.get dst ^^^ imm)), y, false, false,
        maskGprWidth is64 (g.get dst ^^^ imm) == 0, dy, false, m⟩ := by rfl

theorem stepX86_subImm32 (dst : Nat) (imm : UInt64) :
    (stepX86 ⟨off, len, .aluImm .sub false dst imm⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len,
        g.set dst (maskGprWidth false (UInt64.ofNat (((maskGprWidth false (g.get dst)).toNat + 0x100000000 -
          (maskGprWidth false imm).toNat) % 0x100000000))), y,
        decide ((maskGprWidth false (g.get dst)).toNat < (maskGprWidth false imm).toNat),
        evalX86AluOf .sub false (g.get dst) imm cf,
        maskGprWidth false (UInt64.ofNat (((maskGprWidth false (g.get dst)).toNat + 0x100000000 -
          (maskGprWidth false imm).toNat) % 0x100000000)) == 0, dy, false, m⟩ := by rfl

theorem stepX86_addRR64 (dst src : Nat) :
    (stepX86 ⟨off, len, .aluRegReg .add true dst src⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len,
        g.set dst (UInt64.ofNat (((g.get dst).toNat + (g.get src).toNat) % 0x10000000000000000)), y,
        decide ((g.get dst).toNat + (g.get src).toNat ≥ 0x10000000000000000),
        evalX86AluOf .add true (g.get dst) (g.get src) cf,
        UInt64.ofNat (((g.get dst).toNat + (g.get src).toNat) % 0x10000000000000000) == 0,
        dy, false, m⟩ := by rfl

theorem stepX86_subRR64 (dst src : Nat) :
    (stepX86 ⟨off, len, .aluRegReg .sub true dst src⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len,
        g.set dst (UInt64.ofNat (((g.get dst).toNat + 0x10000000000000000 - (g.get src).toNat) %
          0x10000000000000000)), y,
        decide ((g.get dst).toNat < (g.get src).toNat),
        evalX86AluOf .sub true (g.get dst) (g.get src) cf,
        UInt64.ofNat (((g.get dst).toNat + 0x10000000000000000 - (g.get src).toNat) %
          0x10000000000000000) == 0, dy, false, m⟩ := by rfl

theorem stepX86_sbbRR (is64 : Bool) (dst src : Nat) :
    (stepX86 ⟨off, len, .aluRegReg .sbb is64 dst src⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (evalX86Alu .sbb is64 (g.get dst) (g.get src) cf).1, y,
        (evalX86Alu .sbb is64 (g.get dst) (g.get src) cf).2.1,
        evalX86AluOf .sbb is64 (g.get dst) (g.get src) cf,
        (evalX86Alu .sbb is64 (g.get dst) (g.get src) cf).2.2, dy, false, m⟩ := by rfl

theorem stepX86_andRR (is64 : Bool) (dst src : Nat) :
    (stepX86 ⟨off, len, .aluRegReg .andOp is64 dst src⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (maskGprWidth is64 (g.get dst &&& g.get src)), y, false, false,
        maskGprWidth is64 (g.get dst &&& g.get src) == 0, dy, false, m⟩ := by rfl

theorem stepX86_movImm (is64 : Bool) (dst : Nat) (imm : UInt64) :
    (stepX86 ⟨off, len, .movImm is64 dst imm⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (maskGprWidth is64 imm), y, cf, o, zf, dy, false, m⟩ := by rfl

theorem stepX86_mulx (hiDst loDst src : Nat) :
    (stepX86 ⟨off, len, .mulx hiDst loDst src⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len,
        (g.set loDst (UInt64.ofNat (((g.get 2).toNat * (g.get src).toNat) % 0x10000000000000000))).set hiDst
          (UInt64.ofNat (((g.get 2).toNat * (g.get src).toNat) / 0x10000000000000000)),
        y, cf, o, zf, dy, false, m⟩ := by rfl

theorem stepX86_shl64 (dst cnt : Nat) :
    (stepX86 ⟨off, len, .shiftImm .shl true dst cnt⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (evalX86Shift .shl true (g.get dst) cnt cf o zf).1, y,
        (evalX86Shift .shl true (g.get dst) cnt cf o zf).2.1,
        (evalX86Shift .shl true (g.get dst) cnt cf o zf).2.2.1,
        (evalX86Shift .shl true (g.get dst) cnt cf o zf).2.2.2,
        dy, false, m⟩ := by rfl

theorem stepX86_movRR (is64 : Bool) (dst src : Nat) :
    (stepX86 ⟨off, len, .movRegReg is64 dst src⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (maskGprWidth is64 (g.get src)), y, cf, o, zf, dy, false, m⟩ := by rfl

theorem stepX86_neg (is64 : Bool) (dst : Nat) :
    (stepX86 ⟨off, len, .negReg is64 dst⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (maskGprWidth is64 (0 - maskGprWidth is64 (g.get dst))), y,
        maskGprWidth is64 (g.get dst) != 0,
        maskGprWidth is64 (g.get dst) == (if is64 then 0x8000000000000000 else 0x80000000),
        maskGprWidth is64 (0 - maskGprWidth is64 (g.get dst)) == 0, dy, false, m⟩ := by rfl

theorem stepX86_shr64 (dst cnt : Nat) :
    (stepX86 ⟨off, len, .shiftImm .shr true dst cnt⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (evalX86Shift .shr true (g.get dst) cnt cf o zf).1, y,
        (evalX86Shift .shr true (g.get dst) cnt cf o zf).2.1,
        (evalX86Shift .shr true (g.get dst) cnt cf o zf).2.2.1,
        (evalX86Shift .shr true (g.get dst) cnt cf o zf).2.2.2,
        dy, false, m⟩ := by rfl

theorem stepX86_shr32 (dst cnt : Nat) :
    (stepX86 ⟨off, len, .shiftImm .shr false dst cnt⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (evalX86Shift .shr false (g.get dst) cnt cf o zf).1, y,
        (evalX86Shift .shr false (g.get dst) cnt cf o zf).2.1,
        (evalX86Shift .shr false (g.get dst) cnt cf o zf).2.2.1,
        (evalX86Shift .shr false (g.get dst) cnt cf o zf).2.2.2,
        dy, false, m⟩ := by rfl

theorem stepX86_inc (is64 : Bool) (dst : Nat) :
    (stepX86 ⟨off, len, .incDec true is64 dst⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (maskGprWidth is64 (maskGprWidth is64 (g.get dst) + 1)), y, cf,
        evalX86IncDecOf true is64 (g.get dst),
        maskGprWidth is64 (maskGprWidth is64 (g.get dst) + 1) == 0, dy, false, m⟩ := by rfl

theorem stepX86_dec (is64 : Bool) (dst : Nat) :
    (stepX86 ⟨off, len, .incDec false is64 dst⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (maskGprWidth is64 (maskGprWidth is64 (g.get dst) + (0 - 1))), y, cf,
        evalX86IncDecOf false is64 (g.get dst),
        maskGprWidth is64 (maskGprWidth is64 (g.get dst) + (0 - 1)) == 0, dy, false, m⟩ := by rfl

theorem stepX86_jnz (tgt : Int) :
    (stepX86 ⟨off, len, .jcc 5 tgt⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨jccPc (!zf) tgt (off + len), g, y, cf, o, zf, dy, false, m⟩ := by rfl

theorem stepX86_mfence :
    (stepX86 ⟨off, len, .mfence⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g, y, cf, o, zf, dy, false, m⟩ := by rfl

theorem stepX86_ret :
    (stepX86 ⟨off, len, .ret⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨pc, g, y, cf, o, zf, dy, true, m⟩ := by rfl

end X86Steps

/-! ## §4. `AArch64` step lemmas -/

section Arm64Steps
variable (off len pc : Nat) (g : Bank32 UInt64) (v : Bank32 Vec128) (cf zf dit : Bool)
  (m : UInt64 → UInt8)

theorem stepArm64_ldp (rt1 rt2 rn : Nat) (disp : UInt64) :
    (stepArm64 ⟨off, len, .ldp64 rt1 rt2 rn disp⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet (armSet g rt1 (readMem64 m (armGet g rn + disp))) rt2
        (readMem64 m (armGet g rn + disp + 8)), v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_eorRR (rd rn rm : Nat) :
    (stepArm64 ⟨off, len, .aluReg .eor true rd rn rm 0 0⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (armGet g rn ^^^ armGet g rm), v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_orrRR (rd rn rm : Nat) :
    (stepArm64 ⟨off, len, .aluReg .orr true rd rn rm 0 0⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (armGet g rn ||| armGet g rm), v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_subRR (rd rn rm : Nat) :
    (stepArm64 ⟨off, len, .aluReg .sub true rd rn rm 0 0⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (UInt64.ofNat (((armGet g rn).toNat + 0x10000000000000000 - (armGet g rm).toNat) %
        0x10000000000000000)), v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_lsr64 (rd rn immr : Nat) :
    (stepArm64 ⟨off, len, .ubfm true rd rn immr 63⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (armGet g rn >>> UInt64.ofNat immr), v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_eorImm (rd rn : Nat) (imm : UInt64) :
    (stepArm64 ⟨off, len, .aluImm .eor true rd rn imm⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (armGet g rn ^^^ imm), v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_subsImm (rd rn : Nat) (imm : UInt64) :
    (stepArm64 ⟨off, len, .aluImm .subs true rd rn imm⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (UInt64.ofNat (((armGet g rn).toNat + 0x10000000000000000 - imm.toNat) %
          0x10000000000000000)), v, decide ((armGet g rn).toNat ≥ imm.toNat),
        UInt64.ofNat (((armGet g rn).toNat + 0x10000000000000000 - imm.toNat) % 0x10000000000000000) == 0,
        dit, false, m⟩ := by rfl

theorem stepArm64_mul (rd rn rm : Nat) :
    (stepArm64 ⟨off, len, .mulOp false rd rn rm⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (UInt64.ofNat (((armGet g rn).toNat * (armGet g rm).toNat) %
        0x10000000000000000)), v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_umulh (rd rn rm : Nat) :
    (stepArm64 ⟨off, len, .mulOp true rd rn rm⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (UInt64.ofNat (((armGet g rn).toNat * (armGet g rm).toNat) /
        0x10000000000000000)), v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_lsl32 (rd rn : Nat) :
    (stepArm64 ⟨off, len, .ubfm true rd rn 32 31⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (armGet g rn <<< UInt64.ofNat (64 - 32)), v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_andImm (rd rn : Nat) (imm : UInt64) :
    (stepArm64 ⟨off, len, .aluImm .andOp true rd rn imm⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (armGet g rn &&& imm), v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_andRR (rd rn rm : Nat) :
    (stepArm64 ⟨off, len, .aluReg .andOp true rd rn rm 0 0⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (armGet g rn &&& armGet g rm), v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_movn32 (rd imm16 sh : Nat) :
    (stepArm64 ⟨off, len, .movWide true false rd imm16 sh⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (maskGprWidth false (~~~(UInt64.ofNat imm16 <<< UInt64.ofNat sh))),
        v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_addRR (rd rn rm : Nat) :
    (stepArm64 ⟨off, len, .aluReg .add true rd rn rm 0 0⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (UInt64.ofNat (((armGet g rn).toNat + (armGet g rm).toNat) %
        0x10000000000000000)), v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_addsRR (rd rn rm : Nat) :
    (stepArm64 ⟨off, len, .aluReg .adds true rd rn rm 0 0⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (UInt64.ofNat (((armGet g rn).toNat + (armGet g rm).toNat) %
          0x10000000000000000)), v,
        decide ((armGet g rn).toNat + (armGet g rm).toNat ≥ 0x10000000000000000),
        UInt64.ofNat (((armGet g rn).toNat + (armGet g rm).toNat) % 0x10000000000000000) == 0,
        dit, false, m⟩ := by rfl

theorem stepArm64_subsRR (rd rn rm : Nat) :
    (stepArm64 ⟨off, len, .aluReg .subs true rd rn rm 0 0⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (UInt64.ofNat (((armGet g rn).toNat + 0x10000000000000000 -
          (armGet g rm).toNat) % 0x10000000000000000)), v,
        decide ((armGet g rn).toNat ≥ (armGet g rm).toNat),
        UInt64.ofNat (((armGet g rn).toNat + 0x10000000000000000 - (armGet g rm).toNat) %
          0x10000000000000000) == 0, dit, false, m⟩ := by rfl

theorem stepArm64_adcRR (rd rn rm : Nat) :
    (stepArm64 ⟨off, len, .aluReg .adc true rd rn rm 0 0⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (UInt64.ofNat (((armGet g rn).toNat + (armGet g rm).toNat +
        (if cf then 1 else 0)) % 0x10000000000000000)), v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_sbcRR (rd rn rm : Nat) :
    (stepArm64 ⟨off, len, .aluReg .sbc true rd rn rm 0 0⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (UInt64.ofNat (((armGet g rn).toNat + 0x10000000000000000 * 2 -
        (armGet g rm).toNat - (if cf then 0 else 1)) % 0x10000000000000000)),
        v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_movz (rd imm16 sh : Nat) :
    (stepArm64 ⟨off, len, .movWide false true rd imm16 sh⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (UInt64.ofNat imm16 <<< UInt64.ofNat sh), v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_strbPost (rt rn : Nat) (post : UInt64) :
    (stepArm64 ⟨off, len, .strbPost rt rn post⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rn (armGet g rn + post), v, cf, zf, dit, false,
        writeMem8 m (armGet g rn) (armGet g rt).toUInt8⟩ := by rfl

theorem stepArm64_bne (tgt : Int) :
    (stepArm64 ⟨off, len, .bCond 1 tgt⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨jccPc (!zf) tgt (off + 4), g, v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_dmb :
    (stepArm64 ⟨off, len, .dmbIsh⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, g, v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_ret :
    (stepArm64 ⟨off, len, .ret⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨pc, g, v, cf, zf, dit, true, m⟩ := by rfl

end Arm64Steps

/-! ## §5. Word and byte arithmetic used by the specifications -/

theorem u64_eq_of_toNat {a b : UInt64} (h : a.toNat = b.toNat) : a = b :=
  UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)

theorem u8_eq_of_toNat {a b : UInt8} (h : a.toNat = b.toNat) : a = b :=
  UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)

theorem mask32_xor_self (x : UInt64) : maskGprWidth false (x ^^^ x) = 0 := by
  rw [UInt64.xor_self]; decide

theorem u64_zero_beq_zero : ((0 : UInt64) == 0) = true := by decide

theorem u64_shl_zero_zero : UInt64.ofNat 0 <<< UInt64.ofNat 0 = 0 := by decide

theorem u64_zero_toUInt8 : (0 : UInt64).toUInt8 = 0 := by decide

/-- `((x | -x) >> 63) ^ 1` is the zero test of a 64-bit word. -/
theorem zeroTest64 (x : UInt64) :
    ((x ||| (0 - x)) >>> UInt64.ofNat 63) ^^^ 1 = if x = 0 then 1 else 0 := by
  if hx : x = 0 then
    subst hx; rw [ite_eq_left rfl]; decide
  else
    rw [ite_eq_right hx]
    have hpos : 0 < x.toNat := Nat.pos_of_ne_zero (fun h => hx (u64_eq_of_toNat h))
    have hlt : x.toNat < 18446744073709551616 := x.toNat_lt
    have hneg : (0 - x).toNat = 18446744073709551616 - x.toNat := by
      have h0 : (0 : UInt64).toNat = 0 := rfl
      have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
      rw [UInt64.toNat_sub, h0, h64]
      omega
    have hl : x.toNat ≤ x.toNat ||| (0 - x).toNat := Nat.left_le_or
    have hr : (0 - x).toNat ≤ x.toNat ||| (0 - x).toNat := Nat.right_le_or
    have hor : (x ||| (0 - x)).toNat = x.toNat ||| (0 - x).toNat := UInt64.toNat_or _ _
    have horLt : (x ||| (0 - x)).toNat < 18446744073709551616 := (x ||| (0 - x)).toNat_lt
    have hsh : (x ||| (0 - x)) >>> UInt64.ofNat 63 = 1 := by
      apply u64_eq_of_toNat
      have h63 : (UInt64.ofNat 63).toNat % 64 = 63 := rfl
      rw [UInt64.toNat_shiftRight, h63, Nat.shiftRight_eq_div_pow]
      show (x ||| (0 - x)).toNat / 9223372036854775808 = 1
      omega
    rw [hsh]; decide

theorem zeroTest64_masked (x : UInt64) :
    maskGprWidth false (((x ||| (0 - x)) >>> UInt64.ofNat 63) ^^^ 1) = if x = 0 then 1 else 0 := by
  rw [zeroTest64]
  if hx : x = 0 then rw [ite_eq_left hx]; decide else rw [ite_eq_right hx]; decide

theorem or_shl_eq_add (x y i : Nat) (hx : x < 2 ^ i) : x ||| y <<< i = x + y * 2 ^ i := by
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq, Nat.add_comm]

theorem byte_shl_toNat (b : UInt8) (c : UInt64) (n : Nat) (hc : c.toNat = n) (hn : n ≤ 56) :
    (b.toUInt64 <<< c).toNat = b.toNat <<< n := by
  have hb := b.toNat_lt
  have hlt : b.toNat <<< n < 2 ^ 64 := by
    rw [Nat.shiftLeft_eq]
    calc b.toNat * 2 ^ n < 2 ^ 8 * 2 ^ n := Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos n)
      _ = 2 ^ (8 + n) := (Nat.pow_add 2 8 n).symm
      _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
  rw [UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64, hc, Nat.mod_eq_of_lt (show n < 64 by omega),
    Nat.mod_eq_of_lt hlt]

/-- Little-endian value of the eight bytes read by `readMem64`. -/
theorem readMem64_toNat (m : UInt64 → UInt8) (a : UInt64) :
    (readMem64 m a).toNat =
      (m a).toNat + (m (a + 1)).toNat * 256 + (m (a + 2)).toNat * 65536 +
      (m (a + 3)).toNat * 16777216 + (m (a + 4)).toNat * 4294967296 +
      (m (a + 5)).toNat * 1099511627776 + (m (a + 6)).toNat * 281474976710656 +
      (m (a + 7)).toNat * 72057594037927936 := by
  have b0 : (m a).toNat < 256 := (m a).toNat_lt
  have b1 : (m (a + 1)).toNat < 256 := (m (a + 1)).toNat_lt
  have b2 : (m (a + 2)).toNat < 256 := (m (a + 2)).toNat_lt
  have b3 : (m (a + 3)).toNat < 256 := (m (a + 3)).toNat_lt
  have b4 : (m (a + 4)).toNat < 256 := (m (a + 4)).toNat_lt
  have b5 : (m (a + 5)).toNat < 256 := (m (a + 5)).toNat_lt
  have b6 : (m (a + 6)).toNat < 256 := (m (a + 6)).toNat_lt
  unfold readMem64
  rw [UInt64.toNat_or, UInt64.toNat_or, UInt64.toNat_or, UInt64.toNat_or, UInt64.toNat_or,
    UInt64.toNat_or, UInt64.toNat_or, UInt8.toNat_toUInt64,
    byte_shl_toNat _ 8 8 rfl (by decide), byte_shl_toNat _ 16 16 rfl (by decide),
    byte_shl_toNat _ 24 24 rfl (by decide), byte_shl_toNat _ 32 32 rfl (by decide),
    byte_shl_toNat _ 40 40 rfl (by decide), byte_shl_toNat _ 48 48 rfl (by decide),
    byte_shl_toNat _ 56 56 rfl (by decide)]
  have e1 := or_shl_eq_add (m a).toNat (m (a + 1)).toNat 8 b0
  rw [e1]
  have e2 := or_shl_eq_add ((m a).toNat + (m (a + 1)).toNat * 2 ^ 8) (m (a + 2)).toNat 16
    (by show _ < 65536; omega)
  rw [e2]
  have e3 := or_shl_eq_add ((m a).toNat + (m (a + 1)).toNat * 2 ^ 8 + (m (a + 2)).toNat * 2 ^ 16)
    (m (a + 3)).toNat 24 (by show _ + _ * 256 + _ * 65536 < 16777216; omega)
  rw [e3]
  have e4 := or_shl_eq_add ((m a).toNat + (m (a + 1)).toNat * 2 ^ 8 + (m (a + 2)).toNat * 2 ^ 16 +
    (m (a + 3)).toNat * 2 ^ 24) (m (a + 4)).toNat 32
    (by show _ + _ * 256 + _ * 65536 + _ * 16777216 < 4294967296; omega)
  rw [e4]
  have e5 := or_shl_eq_add ((m a).toNat + (m (a + 1)).toNat * 2 ^ 8 + (m (a + 2)).toNat * 2 ^ 16 +
    (m (a + 3)).toNat * 2 ^ 24 + (m (a + 4)).toNat * 2 ^ 32) (m (a + 5)).toNat 40
    (by show _ + _ * 256 + _ * 65536 + _ * 16777216 + _ * 4294967296 < 1099511627776; omega)
  rw [e5]
  have e6 := or_shl_eq_add ((m a).toNat + (m (a + 1)).toNat * 2 ^ 8 + (m (a + 2)).toNat * 2 ^ 16 +
    (m (a + 3)).toNat * 2 ^ 24 + (m (a + 4)).toNat * 2 ^ 32 + (m (a + 5)).toNat * 2 ^ 40)
    (m (a + 6)).toNat 48
    (by show _ + _ * 256 + _ * 65536 + _ * 16777216 + _ * 4294967296 + _ * 1099511627776 <
          281474976710656; omega)
  rw [e6]
  have e7 := or_shl_eq_add ((m a).toNat + (m (a + 1)).toNat * 2 ^ 8 + (m (a + 2)).toNat * 2 ^ 16 +
    (m (a + 3)).toNat * 2 ^ 24 + (m (a + 4)).toNat * 2 ^ 32 + (m (a + 5)).toNat * 2 ^ 40 +
    (m (a + 6)).toNat * 2 ^ 48) (m (a + 7)).toNat 56
    (by show _ + _ * 256 + _ * 65536 + _ * 16777216 + _ * 4294967296 + _ * 1099511627776 +
          _ * 281474976710656 < 72057594037927936; omega)
  rw [e7]

/-- `readMem64` is injective on the eight bytes it reads. -/
theorem readMem64_inj {m m' : UInt64 → UInt8} {a b : UInt64} (h : readMem64 m a = readMem64 m' b) :
    m a = m' b ∧ m (a + 1) = m' (b + 1) ∧ m (a + 2) = m' (b + 2) ∧ m (a + 3) = m' (b + 3) ∧
    m (a + 4) = m' (b + 4) ∧ m (a + 5) = m' (b + 5) ∧ m (a + 6) = m' (b + 6) ∧
    m (a + 7) = m' (b + 7) := by
  have hn := congrArg UInt64.toNat h
  rw [readMem64_toNat, readMem64_toNat] at hn
  have a0 : (m a).toNat < 256 := (m a).toNat_lt
  have a1 : (m (a + 1)).toNat < 256 := (m (a + 1)).toNat_lt
  have a2 : (m (a + 2)).toNat < 256 := (m (a + 2)).toNat_lt
  have a3 : (m (a + 3)).toNat < 256 := (m (a + 3)).toNat_lt
  have a4 : (m (a + 4)).toNat < 256 := (m (a + 4)).toNat_lt
  have a5 : (m (a + 5)).toNat < 256 := (m (a + 5)).toNat_lt
  have a6 : (m (a + 6)).toNat < 256 := (m (a + 6)).toNat_lt
  have a7 : (m (a + 7)).toNat < 256 := (m (a + 7)).toNat_lt
  have c0 : (m' b).toNat < 256 := (m' b).toNat_lt
  have c1 : (m' (b + 1)).toNat < 256 := (m' (b + 1)).toNat_lt
  have c2 : (m' (b + 2)).toNat < 256 := (m' (b + 2)).toNat_lt
  have c3 : (m' (b + 3)).toNat < 256 := (m' (b + 3)).toNat_lt
  have c4 : (m' (b + 4)).toNat < 256 := (m' (b + 4)).toNat_lt
  have c5 : (m' (b + 5)).toNat < 256 := (m' (b + 5)).toNat_lt
  have c6 : (m' (b + 6)).toNat < 256 := (m' (b + 6)).toNat_lt
  have c7 : (m' (b + 7)).toNat < 256 := (m' (b + 7)).toNat_lt
  exact ⟨u8_eq_of_toNat (by omega), u8_eq_of_toNat (by omega), u8_eq_of_toNat (by omega),
    u8_eq_of_toNat (by omega), u8_eq_of_toNat (by omega), u8_eq_of_toNat (by omega),
    u8_eq_of_toNat (by omega), u8_eq_of_toNat (by omega)⟩

theorem addr_split (a : UInt64) (d j : Nat) :
    a + UInt64.ofNat d + UInt64.ofNat j = a + UInt64.ofNat (d + j) := by
  rw [UInt64.add_assoc, ← UInt64.ofNat_add]

theorem readMem64_eq_iff (m : UInt64 → UInt8) (a b : UInt64) :
    readMem64 m a = readMem64 m b ↔
      ∀ j : Nat, j < 8 → m (a + UInt64.ofNat j) = m (b + UInt64.ofNat j) := by
  have e0 : ∀ x : UInt64, x + UInt64.ofNat 0 = x := fun x => UInt64.add_zero x
  constructor
  · intro h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := readMem64_inj h
    intro j hj
    match j, hj with
    | 0, _ => rw [e0, e0]; exact h0
    | 1, _ => exact h1
    | 2, _ => exact h2
    | 3, _ => exact h3
    | 4, _ => exact h4
    | 5, _ => exact h5
    | 6, _ => exact h6
    | 7, _ => exact h7
    | n + 8, hn => exact absurd hn (by omega)
  · intro h
    have h0 : m a = m b := by
      have := h 0 (by decide)
      rw [e0, e0] at this
      exact this
    have h1 : m (a + 1) = m (b + 1) := h 1 (by decide)
    have h2 : m (a + 2) = m (b + 2) := h 2 (by decide)
    have h3 : m (a + 3) = m (b + 3) := h 3 (by decide)
    have h4 : m (a + 4) = m (b + 4) := h 4 (by decide)
    have h5 : m (a + 5) = m (b + 5) := h 5 (by decide)
    have h6 : m (a + 6) = m (b + 6) := h 6 (by decide)
    have h7 : m (a + 7) = m (b + 7) := h 7 (by decide)
    unfold readMem64
    rw [h0, h1, h2, h3, h4, h5, h6, h7]

theorem block_of_bytes (m : UInt64 → UInt8) (a b : UInt64) (n d : Nat)
    (h : ∀ i : Nat, i < n → m (a + UInt64.ofNat i) = m (b + UInt64.ofNat i)) (hd : d + 8 ≤ n) :
    readMem64 m (a + UInt64.ofNat d) = readMem64 m (b + UInt64.ofNat d) :=
  (readMem64_eq_iff _ _ _).mpr (fun j hj => by
    rw [addr_split, addr_split]; exact h (d + j) (by omega))

theorem bytes_of_block (m : UInt64 → UInt8) (a b : UInt64) (d : Nat)
    (h : readMem64 m (a + UInt64.ofNat d) = readMem64 m (b + UInt64.ofNat d))
    (i : Nat) (h1 : d ≤ i) (h2 : i < d + 8) :
    m (a + UInt64.ofNat i) = m (b + UInt64.ofNat i) := by
  have := (readMem64_eq_iff _ _ _).mp h (i - d) (by omega)
  rw [addr_split, addr_split, show d + (i - d) = i from by omega] at this
  exact this

/-- The OR of the four XOR-ed 64-bit words vanishes exactly when the two 32-byte buffers agree. -/
theorem xorOr4_eq_zero_iff (m : UInt64 → UInt8) (a b a0 a1 a2 a3 b0 b1 b2 b3 : UInt64)
    (ha0 : a0 = a + UInt64.ofNat 0) (ha1 : a1 = a + UInt64.ofNat 8)
    (ha2 : a2 = a + UInt64.ofNat 16) (ha3 : a3 = a + UInt64.ofNat 24)
    (hb0 : b0 = b + UInt64.ofNat 0) (hb1 : b1 = b + UInt64.ofNat 8)
    (hb2 : b2 = b + UInt64.ofNat 16) (hb3 : b3 = b + UInt64.ofNat 24) :
    (readMem64 m a0 ^^^ readMem64 m b0 ||| readMem64 m a1 ^^^ readMem64 m b1) |||
      (readMem64 m a2 ^^^ readMem64 m b2 ||| readMem64 m a3 ^^^ readMem64 m b3) = 0 ↔
    ∀ i : Nat, i < 32 → m (a + UInt64.ofNat i) = m (b + UInt64.ofNat i) := by
  subst ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
  rw [UInt64.or_eq_zero_iff, UInt64.or_eq_zero_iff, UInt64.or_eq_zero_iff,
    UInt64.xor_eq_zero_iff, UInt64.xor_eq_zero_iff, UInt64.xor_eq_zero_iff, UInt64.xor_eq_zero_iff]
  constructor
  · intro ⟨⟨h0, h1⟩, h2, h3⟩ i hi
    if c1 : i < 8 then exact bytes_of_block m a b 0 h0 i (by omega) (by omega)
    else if c2 : i < 16 then exact bytes_of_block m a b 8 h1 i (by omega) (by omega)
    else if c3 : i < 24 then exact bytes_of_block m a b 16 h2 i (by omega) (by omega)
    else exact bytes_of_block m a b 24 h3 i (by omega) (by omega)
  · intro h
    exact ⟨⟨block_of_bytes m a b 32 0 h (by decide), block_of_bytes m a b 32 8 h (by decide)⟩,
      block_of_bytes m a b 32 16 h (by decide), block_of_bytes m a b 32 24 h (by decide)⟩

/-- Unpack a successful "find slice, then decode" computation. -/
theorem slice_decode_x86 {slices : List ElfFuncSlice} {nm : List UInt8}
    {prog : List (DecodedInstr X86Instr)}
    (h : (findSliceByNameBytes slices nm).bind (fun sl => decodeX86Stream sl.code) = some prog) :
    ∃ slice, findSliceByNameBytes slices nm = some slice ∧ decodeX86Stream slice.code = some prog := by
  cases hf : findSliceByNameBytes slices nm with
  | none => rw [hf] at h; cases h
  | some sl => rw [hf] at h; exact ⟨sl, rfl, h⟩

theorem slice_decode_arm64 {slices : List ElfFuncSlice} {nm : List UInt8}
    {prog : List (DecodedInstr Arm64Instr)}
    (h : (findSliceByNameBytes slices nm).bind (fun sl => decodeArm64Stream sl.code) = some prog) :
    ∃ slice, findSliceByNameBytes slices nm = some slice ∧ decodeArm64Stream slice.code = some prog := by
  cases hf : findSliceByNameBytes slices nm with
  | none => rw [hf] at h; cases h
  | some sl => rw [hf] at h; exact ⟨sl, rfl, h⟩

/-! ## §6. `qsag_asm_ct_eq_32_x86_64`: 32-byte equality, straight-line -/

/-- ASCII bytes of the symbol name `qsag_asm_ct_eq_32_x86_64`. -/
@[expose] def ctEq32X86Name : List UInt8 :=
  [0x71, 0x73, 0x61, 0x67, 0x5f, 0x61, 0x73, 0x6d, 0x5f, 0x63, 0x74, 0x5f, 0x65, 0x71, 0x5f, 0x33,
   0x32, 0x5f, 0x78, 0x38, 0x36, 0x5f, 0x36, 0x34]

def ctEq32X86Prog : List (DecodedInstr X86Instr) := [
  ⟨0, 3, .loadGpr 8 true 0 (.baseDisp 7 0)⟩,
  ⟨3, 3, .aluLoad64 .xorOp 0 (.baseDisp 6 0)⟩,
  ⟨6, 4, .loadGpr 8 true 1 (.baseDisp 7 8)⟩,
  ⟨10, 4, .aluLoad64 .xorOp 1 (.baseDisp 6 8)⟩,
  ⟨14, 4, .loadGpr 8 true 2 (.baseDisp 7 16)⟩,
  ⟨18, 4, .aluLoad64 .xorOp 2 (.baseDisp 6 16)⟩,
  ⟨22, 4, .loadGpr 8 true 8 (.baseDisp 7 24)⟩,
  ⟨26, 4, .aluLoad64 .xorOp 8 (.baseDisp 6 24)⟩,
  ⟨30, 3, .aluRegReg .orOp true 0 1⟩,
  ⟨33, 3, .aluRegReg .orOp true 2 8⟩,
  ⟨36, 3, .aluRegReg .orOp true 0 2⟩,
  ⟨39, 3, .movRegReg true 1 0⟩,
  ⟨42, 3, .negReg true 1⟩,
  ⟨45, 3, .aluRegReg .orOp true 0 1⟩,
  ⟨48, 4, .shiftImm .shr true 0 63⟩,
  ⟨52, 3, .aluImm .xorOp false 0 1⟩,
  ⟨55, 2, .aluRegReg .xorOp false 1 1⟩,
  ⟨57, 2, .aluRegReg .xorOp false 2 2⟩,
  ⟨59, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨62, 1, .ret⟩]

theorem ctEq32X86_decodes :
    (findSliceByNameBytes x86ExtractedSlices ctEq32X86Name).bind (fun sl => decodeX86Stream sl.code)
      = some ctEq32X86Prog := by
  decide +kernel

/-- The OR of the four XOR-ed words as the x86 kernel computes it. -/
def ctEq32WordX86 (m : UInt64 → UInt8) (a b : UInt64) : UInt64 :=
  (readMem64 m (a + 0) ^^^ readMem64 m (b + 0) ||| readMem64 m (a + 8) ^^^ readMem64 m (b + 8)) |||
    (readMem64 m (a + 16) ^^^ readMem64 m (b + 16) ||| readMem64 m (a + 24) ^^^ readMem64 m (b + 24))

theorem ctEq32X86_run (k : Nat) (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    (runX86 ctEq32X86Prog (k + 20)
      ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨62, ⟨maskGprWidth false (((ctEq32WordX86 m r7 r6 ||| (0 - ctEq32WordX86 m r7 r6)) >>>
              UInt64.ofNat 63) ^^^ 1),
          0, 0, r3, r4, r5, r6, r7, 0, r9, r10, r11, r12, r13, r14, r15⟩,
        y, false, false, true, dy, true, m⟩ := by
  iterate 20
    refine Eq.trans (runX86_step_fst _ _ _ _ rfl rfl) ?_
    simp only [stepX86_load64, stepX86_xorLoad64, stepX86_orRR, stepX86_movRR, stepX86_neg, stepX86_shr64,
      stepX86_xorImm, stepX86_xorRR, stepX86_ret, maskGprWidth_true, mask32_xor_self, u64_zero_beq_zero,
      b16get_0, b16get_1, b16get_2, b16get_6, b16get_7, b16get_8,
      b16set_0, b16set_1, b16set_2, b16set_8]
  refine Eq.trans (runX86_halted_fst _ _ _ rfl) ?_
  rfl

/-- **Machine-code refinement of `qsag_asm_ct_eq_32_x86_64`.** From any entry state, at most 20
steps halt with `rax = 1` when the 32 bytes at `rdi` equal the 32 bytes at `rsi` and `rax = 0`
otherwise (addresses wrap modulo `2^64`); memory is untouched and `rcx`, `rdx`, `r8` are wiped. -/
theorem ct_eq_32_x86_64_mc_refines :
    ∃ slice prog, findSliceByNameBytes x86ExtractedSlices ctEq32X86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 20 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        (runX86 prog fuel s).1.gpr.get 0 =
          (if ∀ i : Nat, i < 32 →
              s.mem (s.gpr.get 7 + UInt64.ofNat i) = s.mem (s.gpr.get 6 + UInt64.ofNat i)
            then 1 else 0) ∧
        (runX86 prog fuel s).1.mem = s.mem ∧
        (runX86 prog fuel s).1.gpr.get 1 = 0 ∧ (runX86 prog fuel s).1.gpr.get 2 = 0 ∧
        (runX86 prog fuel s).1.gpr.get 8 = 0 := by
  obtain ⟨sl, hf, hd⟩ := slice_decode_x86 ctEq32X86_decodes
  refine ⟨sl, ctEq32X86Prog, hf, hd, ?_⟩
  intro s fuel hpc hh hfuel
  obtain ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
    y, cf, o, zf, dy, hlt, m⟩ := s
  have hpc' : pc = 0 := hpc
  have hh' : hlt = false := hh
  subst hpc' hh'
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hfuel
  rw [Nat.add_comm 20 k, ctEq32X86_run]
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
  show maskGprWidth false (((ctEq32WordX86 m r7 r6 ||| (0 - ctEq32WordX86 m r7 r6)) >>>
      UInt64.ofNat 63) ^^^ 1) =
    if ∀ i : Nat, i < 32 → m (r7 + UInt64.ofNat i) = m (r6 + UInt64.ofNat i) then 1 else 0
  have hiff : ctEq32WordX86 m r7 r6 = 0 ↔
      ∀ i : Nat, i < 32 → m (r7 + UInt64.ofNat i) = m (r6 + UInt64.ofNat i) :=
    xorOr4_eq_zero_iff m r7 r6 _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl
  rw [zeroTest64_masked]
  if hW : ctEq32WordX86 m r7 r6 = 0 then
    rw [ite_eq_left hW, ite_eq_left (hiff.mp hW)]
  else
    rw [ite_eq_right hW, ite_eq_right (fun h => hW (hiff.mpr h))]

/-- The preconditions of `ct_eq_32_x86_64_mc_refines` are satisfiable. -/
theorem ct_eq_32_x86_64_pre_inhabited : ∃ s : X86State, s.pc = 0 ∧ s.halted = false :=
  ⟨⟨0, Bank16.const 0, Bank16.const Vec256.zero, false, false, false, false, false, fun _ => 0⟩, rfl, rfl⟩

/-! ## §7. `qsag_asm_ct_eq_32_aarch64` -/

/-- ASCII bytes of the symbol name `qsag_asm_ct_eq_32_aarch64`. -/
@[expose] def ctEq32ArmName : List UInt8 :=
  [0x71, 0x73, 0x61, 0x67, 0x5f, 0x61, 0x73, 0x6d, 0x5f, 0x63, 0x74, 0x5f, 0x65, 0x71, 0x5f, 0x33,
   0x32, 0x5f, 0x61, 0x61, 0x72, 0x63, 0x68, 0x36, 0x34]

def ctEq32ArmProg : List (DecodedInstr Arm64Instr) := [
  ⟨0, 4, .ldp64 2 3 0 0⟩,
  ⟨4, 4, .ldp64 4 5 1 0⟩,
  ⟨8, 4, .aluReg .eor true 2 2 4 0 0⟩,
  ⟨12, 4, .aluReg .eor true 3 3 5 0 0⟩,
  ⟨16, 4, .aluReg .orr true 2 2 3 0 0⟩,
  ⟨20, 4, .ldp64 4 5 0 16⟩,
  ⟨24, 4, .ldp64 6 7 1 16⟩,
  ⟨28, 4, .aluReg .eor true 4 4 6 0 0⟩,
  ⟨32, 4, .aluReg .eor true 5 5 7 0 0⟩,
  ⟨36, 4, .aluReg .orr true 4 4 5 0 0⟩,
  ⟨40, 4, .aluReg .orr true 2 2 4 0 0⟩,
  ⟨44, 4, .aluReg .sub true 3 31 2 0 0⟩,
  ⟨48, 4, .aluReg .orr true 2 2 3 0 0⟩,
  ⟨52, 4, .ubfm true 0 2 63 63⟩,
  ⟨56, 4, .aluImm .eor true 0 0 1⟩,
  ⟨60, 4, .movWide false true 2 0 0⟩,
  ⟨64, 4, .movWide false true 3 0 0⟩,
  ⟨68, 4, .movWide false true 4 0 0⟩,
  ⟨72, 4, .movWide false true 5 0 0⟩,
  ⟨76, 4, .movWide false true 6 0 0⟩,
  ⟨80, 4, .movWide false true 7 0 0⟩,
  ⟨84, 4, .ret⟩]

theorem ctEq32Arm_decodes :
    (findSliceByNameBytes aarch64ExtractedSlices ctEq32ArmName).bind
      (fun sl => decodeArm64Stream sl.code) = some ctEq32ArmProg := by
  decide +kernel

/-- The OR of the four XOR-ed words as the AArch64 kernel computes it. -/
def ctEq32WordArm (m : UInt64 → UInt8) (a b : UInt64) : UInt64 :=
  (readMem64 m (a + 0) ^^^ readMem64 m (b + 0) |||
      readMem64 m (a + 0 + 8) ^^^ readMem64 m (b + 0 + 8)) |||
    (readMem64 m (a + 16) ^^^ readMem64 m (b + 16) |||
      readMem64 m (a + 16 + 8) ^^^ readMem64 m (b + 16 + 8))

theorem ctEq32Arm_run (k : Nat) (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (hi : Bank16 UInt64) (v : Bank32 Vec128) (cf zf dit : Bool) (m : UInt64 → UInt8) :
    (runArm64 ctEq32ArmProg (k + 22)
      ⟨0, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        v, cf, zf, dit, false, m⟩).1 =
      ⟨84, ⟨⟨((ctEq32WordArm m r0 r1 ||| (0 - ctEq32WordArm m r0 r1)) >>> UInt64.ofNat 63) ^^^ 1,
          r1, 0, 0, 0, 0, 0, 0, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        v, cf, zf, dit, true, m⟩ := by
  iterate 22
    refine Eq.trans (runArm64_step_fst _ _ _ _ rfl rfl) ?_
    simp only [stepArm64_ldp, stepArm64_eorRR, stepArm64_orrRR, stepArm64_subRR, stepArm64_lsr64,
      stepArm64_eorImm, stepArm64_movz, stepArm64_ret, u64_shl_zero_zero, uint64_evalSub_eq,
      armGet_31, armGet_0, armGet_1, armGet_2, armGet_3, armGet_4, armGet_5, armGet_6, armGet_7,
      armSet_0, armSet_2, armSet_3, armSet_4, armSet_5, armSet_6, armSet_7]
  refine Eq.trans (runArm64_halted_fst _ _ _ rfl) ?_
  rfl

/-- **Machine-code refinement of `qsag_asm_ct_eq_32_aarch64`.** From any entry state, at most 22
steps halt with `x0 = 1` when the 32 bytes at `x0` equal the 32 bytes at `x1` and `x0 = 0`
otherwise; memory is untouched and `x2..x7` are wiped. -/
theorem ct_eq_32_aarch64_mc_refines :
    ∃ slice prog, findSliceByNameBytes aarch64ExtractedSlices ctEq32ArmName = some slice ∧
      decodeArm64Stream slice.code = some prog ∧
      ∀ (s : Arm64State) (fuel : Nat), s.pc = 0 → s.halted = false → 22 ≤ fuel →
        (runArm64 prog fuel s).1.halted = true ∧
        (runArm64 prog fuel s).1.gpr.get 0 =
          (if ∀ i : Nat, i < 32 →
              s.mem (s.gpr.get 0 + UInt64.ofNat i) = s.mem (s.gpr.get 1 + UInt64.ofNat i)
            then 1 else 0) ∧
        (runArm64 prog fuel s).1.mem = s.mem ∧
        (∀ r : Nat, 2 ≤ r → r ≤ 7 → (runArm64 prog fuel s).1.gpr.get r = 0) := by
  obtain ⟨sl, hf, hd⟩ := slice_decode_arm64 ctEq32Arm_decodes
  refine ⟨sl, ctEq32ArmProg, hf, hd, ?_⟩
  intro s fuel hpc hh hfuel
  obtain ⟨pc, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
    v, cf, zf, dit, hlt, m⟩ := s
  have hpc' : pc = 0 := hpc
  have hh' : hlt = false := hh
  subst hpc' hh'
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hfuel
  rw [Nat.add_comm 22 k, ctEq32Arm_run]
  refine ⟨rfl, ?_, rfl, ?_⟩
  · show ((ctEq32WordArm m r0 r1 ||| (0 - ctEq32WordArm m r0 r1)) >>> UInt64.ofNat 63) ^^^ 1 =
      if ∀ i : Nat, i < 32 → m (r0 + UInt64.ofNat i) = m (r1 + UInt64.ofNat i) then 1 else 0
    have e8 : ∀ x : UInt64, x + 0 + 8 = x + UInt64.ofNat 8 := fun x => by rw [UInt64.add_zero]; rfl
    have e24 : ∀ x : UInt64, x + 16 + 8 = x + UInt64.ofNat 24 := fun x => by
      rw [UInt64.add_assoc]; rfl
    have hiff : ctEq32WordArm m r0 r1 = 0 ↔
        ∀ i : Nat, i < 32 → m (r0 + UInt64.ofNat i) = m (r1 + UInt64.ofNat i) :=
      xorOr4_eq_zero_iff m r0 r1 _ _ _ _ _ _ _ _ rfl (e8 r0) rfl (e24 r0) rfl (e8 r1) rfl (e24 r1)
    rw [zeroTest64]
    if hW : ctEq32WordArm m r0 r1 = 0 then
      rw [ite_eq_left hW, ite_eq_left (hiff.mp hW)]
    else
      rw [ite_eq_right hW, ite_eq_right (fun h => hW (hiff.mpr h))]
  · intro r h2 h7
    match r, h2, h7 with
    | 2, _, _ => rfl
    | 3, _, _ => rfl
    | 4, _, _ => rfl
    | 5, _, _ => rfl
    | 6, _, _ => rfl
    | 7, _, _ => rfl
    | 0, h, _ => exact absurd h (by decide)
    | 1, h, _ => exact absurd h (by decide)
    | n + 8, _, h => exact absurd h (by omega)

/-- The preconditions of `ct_eq_32_aarch64_mc_refines` are satisfiable. -/
theorem ct_eq_32_aarch64_pre_inhabited : ∃ s : Arm64State, s.pc = 0 ∧ s.halted = false :=
  ⟨⟨0, Bank32.const 0, Bank32.const Vec128.zero, false, false, false, false, fun _ => 0⟩, rfl, rfl⟩

/-! ## §8. `ct_memzero`: byte-granular wipe loops -/

/-- Memory after writing `0` to the `k` consecutive addresses `p, p + 1, …` (wrapping). -/
def zeroRange : Nat → (UInt64 → UInt8) → UInt64 → UInt64 → UInt8
  | 0, m, _ => m
  | k + 1, m, p => zeroRange k (writeMem8 m p 0) (p + 1)

theorem addr_succ (p : UInt64) (i : Nat) : p + 1 + UInt64.ofNat i = p + UInt64.ofNat (i + 1) := by
  have h := addr_split p 1 i
  rw [Nat.add_comm 1 i] at h
  exact h

theorem addr_zero (p : UInt64) : p + UInt64.ofNat 0 = p := UInt64.add_zero p

theorem zeroRange_outside (k : Nat) : ∀ (m : UInt64 → UInt8) (p a : UInt64),
    (∀ i : Nat, i < k → a ≠ p + UInt64.ofNat i) → zeroRange k m p a = m a := by
  induction k with
  | zero => intro m p a _; rfl
  | succ k ih =>
    intro m p a h
    show zeroRange k (writeMem8 m p 0) (p + 1) a = m a
    rw [ih (writeMem8 m p 0) (p + 1) a (fun i hi => by rw [addr_succ]; exact h (i + 1) (by omega))]
    have h0 : a ≠ p := by
      have := h 0 (by omega)
      rw [addr_zero] at this
      exact this
    exact writeMem8_ne m 0 h0

theorem zeroRange_zero_stays (k : Nat) : ∀ (m : UInt64 → UInt8) (p a : UInt64),
    m a = 0 → zeroRange k m p a = 0 := by
  induction k with
  | zero => intro m p a h; exact h
  | succ k ih =>
    intro m p a h
    show zeroRange k (writeMem8 m p 0) (p + 1) a = 0
    apply ih
    if hap : a = p then
      subst hap; exact writeMem8_eq m a 0
    else
      rw [writeMem8_ne m 0 hap]; exact h

theorem zeroRange_inside (k : Nat) : ∀ (m : UInt64 → UInt8) (p : UInt64) (i : Nat),
    i < k → zeroRange k m p (p + UInt64.ofNat i) = 0 := by
  induction k with
  | zero => intro m p i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ k ih =>
    intro m p i hi
    show zeroRange k (writeMem8 m p 0) (p + 1) (p + UInt64.ofNat i) = 0
    cases i with
    | zero =>
      apply zeroRange_zero_stays
      rw [addr_zero]
      exact writeMem8_eq m p 0
    | succ j =>
      rw [← addr_succ]
      exact ih (writeMem8 m p 0) (p + 1) j (by omega)

theorem u64_add_neg_one (x : UInt64) : x + (0 - 1) = x - 1 := by
  apply u64_eq_of_toNat
  have h0 : (0 : UInt64).toNat = 0 := rfl
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  have hx : x.toNat < 18446744073709551616 := x.toNat_lt
  rw [UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_sub, h0, h1, h64]
  omega

theorem u64_pred_toNat (c : UInt64) (k : Nat) (hc : c.toNat = k + 1 + 1) : (c - 1).toNat = k + 1 := by
  have hlt : c.toNat < 18446744073709551616 := c.toNat_lt
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  rw [UInt64.toNat_sub, h1, h64]
  omega

theorem u64_ne_zero_of_toNat_succ (c : UInt64) (k : Nat) (hc : c.toNat = k + 1) : c ≠ 0 := by
  intro h
  rw [h] at hc
  exact Nat.succ_ne_zero k hc.symm

theorem u64_one_sub_one : (1 : UInt64) - 1 = 0 := by decide

/-- ASCII bytes of the symbol name `qsag_asm_ct_memzero_x86_64`. -/
@[expose] def ctMemzeroX86Name : List UInt8 :=
  [0x71, 0x73, 0x61, 0x67, 0x5f, 0x61, 0x73, 0x6d, 0x5f, 0x63, 0x74, 0x5f, 0x6d, 0x65, 0x6d, 0x7a,
   0x65, 0x72, 0x6f, 0x5f, 0x78, 0x38, 0x36, 0x5f, 0x36, 0x34]

def ctMemzeroX86Prog : List (DecodedInstr X86Instr) := [
  ⟨0, 3, .movRegReg true 1 6⟩,
  ⟨3, 2, .aluRegReg .xorOp false 0 0⟩,
  ⟨5, 2, .storeGpr 1 0 (.baseDisp 7 0)⟩,
  ⟨7, 3, .incDec true true 7⟩,
  ⟨10, 3, .incDec false true 1⟩,
  ⟨13, 2, .jcc 5 5⟩,
  ⟨15, 3, .mfence⟩,
  ⟨18, 1, .ret⟩]

theorem ctMemzeroX86_decodes :
    (findSliceByNameBytes x86ExtractedSlices ctMemzeroX86Name).bind
      (fun sl => decodeX86Stream sl.code) = some ctMemzeroX86Prog := by
  decide +kernel

section MemzeroX86
variable {r2 r3 r4 r5 r6 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64} {y : Bank16 Vec256} {cf dy : Bool}

/-- One trip round the store loop (four instructions). -/
theorem ctMemzeroX86_body (c p : UInt64) (o zf : Bool) (m : UInt64 → UInt8) (fuel : Nat) :
    (runX86 ctMemzeroX86Prog (fuel + 4)
      ⟨5, ⟨0, c, r2, r3, r4, r5, r6, p, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, m⟩).1 =
    (runX86 ctMemzeroX86Prog fuel
      ⟨jccPc (!(c - 1 == 0)) 5 15, ⟨0, c - 1, r2, r3, r4, r5, r6, p + 1, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        y, cf, evalX86IncDecOf false true c, c - 1 == 0, dy, false, writeMem8 m p 0⟩).1 := by
  iterate 4
    refine Eq.trans (runX86_step_fst _ _ _ _ rfl rfl) ?_
    simp only [stepX86_store8, stepX86_inc, stepX86_dec, stepX86_jnz, maskGprWidth_true,
      u64_add_neg_one, u64_zero_toUInt8, UInt64.add_zero, b16get_0, b16get_1, b16get_7, b16set_1, b16set_7]

/-- The whole loop, by induction on the remaining count. -/
theorem ctMemzeroX86_loop (k : Nat) : ∀ (c p : UInt64) (o zf : Bool) (m : UInt64 → UInt8) (fuel : Nat),
    c.toNat = k + 1 →
    (runX86 ctMemzeroX86Prog (4 * (k + 1) + fuel)
      ⟨5, ⟨0, c, r2, r3, r4, r5, r6, p, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, m⟩).1 =
    (runX86 ctMemzeroX86Prog fuel
      ⟨15, ⟨0, 0, r2, r3, r4, r5, r6, p + UInt64.ofNat (k + 1), r8, r9, r10, r11, r12, r13, r14, r15⟩,
        y, cf, false, true, dy, false, zeroRange (k + 1) m p⟩).1 := by
  induction k with
  | zero =>
    intro c p o zf m fuel hc
    have hc1 : c = 1 := u64_eq_of_toNat hc
    subst hc1
    rw [show 4 * (0 + 1) + fuel = fuel + 4 from by omega, ctMemzeroX86_body, u64_one_sub_one,
      u64_zero_beq_zero]
    try rfl
  | succ k ih =>
    intro c p o zf m fuel hc
    have hc' := u64_pred_toNat c k hc
    have hne := u64_ne_zero_of_toNat_succ (c - 1) k hc'
    rw [show 4 * (k + 1 + 1) + fuel = (4 * (k + 1) + fuel) + 4 from by omega, ctMemzeroX86_body,
      beq_false_of_ne hne, show jccPc (!false) 5 15 = 5 from rfl,
      ih (c - 1) (p + 1) (evalX86IncDecOf false true c) false (writeMem8 m p 0) fuel hc', addr_succ]
    try rfl

theorem ctMemzeroX86_run {r0 r1 r7 : UInt64} {o zf : Bool} (m : UInt64 → UInt8) (k j : Nat)
    (hn : r6.toNat = k + 1) :
    (runX86 ctMemzeroX86Prog (4 * (k + 1) + 4 + j)
      ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨18, ⟨0, 0, r2, r3, r4, r5, r6, r7 + UInt64.ofNat (k + 1), r8, r9, r10, r11, r12, r13, r14, r15⟩,
        y, false, false, true, dy, true, zeroRange (k + 1) m r7⟩ := by
  rw [show 4 * (k + 1) + 4 + j = (4 * (k + 1) + (j + 2)) + 2 from by omega]
  iterate 2
    refine Eq.trans (runX86_step_fst _ _ _ _ rfl rfl) ?_
    simp only [stepX86_movRR, stepX86_xorRR, maskGprWidth_true, mask32_xor_self, u64_zero_beq_zero,
      b16get_0, b16get_6, b16set_0, b16set_1]
  rw [ctMemzeroX86_loop k r6 r7 false true m (j + 2) hn]
  iterate 2
    refine Eq.trans (runX86_step_fst _ _ _ _ rfl rfl) ?_
    simp only [stepX86_mfence, stepX86_ret]
  exact runX86_halted_fst _ _ _ rfl

end MemzeroX86

/-- **Machine-code refinement of `qsag_asm_ct_memzero_x86_64`.** For a length `n = rsi ≥ 1` (the
Rust wrapper returns early on empty buffers; the loop is bottom-tested), at most `4 n + 4` steps
halt with the `n` bytes at `rdi, rdi + 1, …` (wrapping) zero and every other byte unchanged. -/
theorem ct_memzero_x86_64_mc_refines :
    ∃ slice prog, findSliceByNameBytes x86ExtractedSlices ctMemzeroX86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 0 < (s.gpr.get 6).toNat →
        4 * (s.gpr.get 6).toNat + 4 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        (∀ i : Nat, i < (s.gpr.get 6).toNat →
          (runX86 prog fuel s).1.mem (s.gpr.get 7 + UInt64.ofNat i) = 0) ∧
        (∀ a : UInt64, (∀ i : Nat, i < (s.gpr.get 6).toNat → a ≠ s.gpr.get 7 + UInt64.ofNat i) →
          (runX86 prog fuel s).1.mem a = s.mem a) := by
  obtain ⟨sl, hf, hd⟩ := slice_decode_x86 ctMemzeroX86_decodes
  refine ⟨sl, ctMemzeroX86Prog, hf, hd, ?_⟩
  intro s fuel hpc hh hn hfuel
  obtain ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
    y, cf, o, zf, dy, hlt, m⟩ := s
  have hpc' : pc = 0 := hpc
  have hh' : hlt = false := hh
  subst hpc' hh'
  have hn' : 0 < r6.toNat := hn
  have hfuel' : 4 * r6.toNat + 4 ≤ fuel := hfuel
  obtain ⟨k, hk⟩ : ∃ k, r6.toNat = k + 1 := ⟨r6.toNat - 1, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, fuel = 4 * (k + 1) + 4 + j := ⟨fuel - (4 * (k + 1) + 4), by omega⟩
  subst hj
  rw [ctMemzeroX86_run m k j hk]
  refine ⟨rfl, ?_, ?_⟩
  · intro i hi
    have hi' : i < r6.toNat := hi
    exact zeroRange_inside (k + 1) m r7 i (by omega)
  · intro a ha
    have ha' : ∀ i : Nat, i < r6.toNat → a ≠ r7 + UInt64.ofNat i := ha
    exact zeroRange_outside (k + 1) m r7 a (fun i hi => ha' i (by omega))

/-- The preconditions of `ct_memzero_x86_64_mc_refines` are satisfiable (length 1). -/
theorem ct_memzero_x86_64_pre_inhabited :
    ∃ s : X86State, s.pc = 0 ∧ s.halted = false ∧ 0 < (s.gpr.get 6).toNat :=
  ⟨⟨0, Bank16.const 1, Bank16.const Vec256.zero, false, false, false, false, false, fun _ => 0⟩,
    rfl, rfl, by decide⟩

/-- ASCII bytes of the symbol name `qsag_asm_ct_memzero_aarch64`. -/
@[expose] def ctMemzeroArmName : List UInt8 :=
  [0x71, 0x73, 0x61, 0x67, 0x5f, 0x61, 0x73, 0x6d, 0x5f, 0x63, 0x74, 0x5f, 0x6d, 0x65, 0x6d, 0x7a,
   0x65, 0x72, 0x6f, 0x5f, 0x61, 0x61, 0x72, 0x63, 0x68, 0x36, 0x34]

def ctMemzeroArmProg : List (DecodedInstr Arm64Instr) := [
  ⟨0, 4, .strbPost 31 0 1⟩,
  ⟨4, 4, .aluImm .subs true 1 1 1⟩,
  ⟨8, 4, .bCond 1 0⟩,
  ⟨12, 4, .dmbIsh⟩,
  ⟨16, 4, .ret⟩]

theorem ctMemzeroArm_decodes :
    (findSliceByNameBytes aarch64ExtractedSlices ctMemzeroArmName).bind
      (fun sl => decodeArm64Stream sl.code) = some ctMemzeroArmProg := by
  decide +kernel

section MemzeroArm
variable {r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64} {hi : Bank16 UInt64}
  {v : Bank32 Vec128} {dit : Bool}

/-- One trip round the store loop (three instructions). -/
theorem ctMemzeroArm_body (c p : UInt64) (cf zf : Bool) (m : UInt64 → UInt8) (fuel : Nat) :
    (runArm64 ctMemzeroArmProg (fuel + 3)
      ⟨0, ⟨⟨p, c, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        v, cf, zf, dit, false, m⟩).1 =
    (runArm64 ctMemzeroArmProg fuel
      ⟨jccPc (!(c - 1 == 0)) 0 12,
        ⟨⟨p + 1, c - 1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        v, decide (c.toNat ≥ (1 : UInt64).toNat), c - 1 == 0, dit, false, writeMem8 m p 0⟩).1 := by
  iterate 3
    refine Eq.trans (runArm64_step_fst _ _ _ _ rfl rfl) ?_
    simp only [stepArm64_strbPost, stepArm64_subsImm, stepArm64_bne, uint64_evalSub_eq,
      u64_zero_toUInt8, armGet_31, armGet_0, armGet_1, armSet_0, armSet_1]

theorem ctMemzeroArm_loop (k : Nat) :
    ∀ (c p : UInt64) (cf zf : Bool) (m : UInt64 → UInt8) (fuel : Nat), c.toNat = k + 1 →
    (runArm64 ctMemzeroArmProg (3 * (k + 1) + fuel)
      ⟨0, ⟨⟨p, c, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        v, cf, zf, dit, false, m⟩).1 =
    (runArm64 ctMemzeroArmProg fuel
      ⟨12, ⟨⟨p + UInt64.ofNat (k + 1), 0, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        v, true, true, dit, false, zeroRange (k + 1) m p⟩).1 := by
  induction k with
  | zero =>
    intro c p cf zf m fuel hc
    have hc1 : c = 1 := u64_eq_of_toNat hc
    subst hc1
    rw [show 3 * (0 + 1) + fuel = fuel + 3 from by omega, ctMemzeroArm_body, u64_one_sub_one,
      u64_zero_beq_zero]
    try rfl
  | succ k ih =>
    intro c p cf zf m fuel hc
    have hc' := u64_pred_toNat c k hc
    have hne := u64_ne_zero_of_toNat_succ (c - 1) k hc'
    rw [show 3 * (k + 1 + 1) + fuel = (3 * (k + 1) + fuel) + 3 from by omega, ctMemzeroArm_body,
      beq_false_of_ne hne, show jccPc (!false) 0 12 = 0 from rfl,
      ih (c - 1) (p + 1) _ false (writeMem8 m p 0) fuel hc', addr_succ]
    try rfl

theorem ctMemzeroArm_run {r0 r1 : UInt64} {cf zf : Bool} (m : UInt64 → UInt8) (k j : Nat)
    (hn : r1.toNat = k + 1) :
    (runArm64 ctMemzeroArmProg (3 * (k + 1) + 2 + j)
      ⟨0, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        v, cf, zf, dit, false, m⟩).1 =
      ⟨16, ⟨⟨r0 + UInt64.ofNat (k + 1), 0, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        v, true, true, dit, true, zeroRange (k + 1) m r0⟩ := by
  rw [show 3 * (k + 1) + 2 + j = 3 * (k + 1) + (j + 2) from by omega,
    ctMemzeroArm_loop k r1 r0 cf zf m (j + 2) hn]
  iterate 2
    refine Eq.trans (runArm64_step_fst _ _ _ _ rfl rfl) ?_
    simp only [stepArm64_dmb, stepArm64_ret]
  exact runArm64_halted_fst _ _ _ rfl

end MemzeroArm

/-- **Machine-code refinement of `qsag_asm_ct_memzero_aarch64`.** For a length `n = x1 ≥ 1`, at
most `3 n + 2` steps halt with the `n` bytes at `x0, x0 + 1, …` (wrapping) zero and every other
byte unchanged. -/
theorem ct_memzero_aarch64_mc_refines :
    ∃ slice prog, findSliceByNameBytes aarch64ExtractedSlices ctMemzeroArmName = some slice ∧
      decodeArm64Stream slice.code = some prog ∧
      ∀ (s : Arm64State) (fuel : Nat), s.pc = 0 → s.halted = false → 0 < (s.gpr.get 1).toNat →
        3 * (s.gpr.get 1).toNat + 2 ≤ fuel →
        (runArm64 prog fuel s).1.halted = true ∧
        (∀ i : Nat, i < (s.gpr.get 1).toNat →
          (runArm64 prog fuel s).1.mem (s.gpr.get 0 + UInt64.ofNat i) = 0) ∧
        (∀ a : UInt64, (∀ i : Nat, i < (s.gpr.get 1).toNat → a ≠ s.gpr.get 0 + UInt64.ofNat i) →
          (runArm64 prog fuel s).1.mem a = s.mem a) := by
  obtain ⟨sl, hf, hd⟩ := slice_decode_arm64 ctMemzeroArm_decodes
  refine ⟨sl, ctMemzeroArmProg, hf, hd, ?_⟩
  intro s fuel hpc hh hn hfuel
  obtain ⟨pc, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
    v, cf, zf, dit, hlt, m⟩ := s
  have hpc' : pc = 0 := hpc
  have hh' : hlt = false := hh
  subst hpc' hh'
  have hn' : 0 < r1.toNat := hn
  have hfuel' : 3 * r1.toNat + 2 ≤ fuel := hfuel
  obtain ⟨k, hk⟩ : ∃ k, r1.toNat = k + 1 := ⟨r1.toNat - 1, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, fuel = 3 * (k + 1) + 2 + j := ⟨fuel - (3 * (k + 1) + 2), by omega⟩
  subst hj
  rw [ctMemzeroArm_run m k j hk]
  refine ⟨rfl, ?_, ?_⟩
  · intro i hi
    have hi' : i < r1.toNat := hi
    exact zeroRange_inside (k + 1) m r0 i (by omega)
  · intro a ha
    have ha' : ∀ i : Nat, i < r1.toNat → a ≠ r0 + UInt64.ofNat i := ha
    exact zeroRange_outside (k + 1) m r0 a (fun i hi => ha' i (by omega))

/-- The preconditions of `ct_memzero_aarch64_mc_refines` are satisfiable (length 1). -/
theorem ct_memzero_aarch64_pre_inhabited :
    ∃ s : Arm64State, s.pc = 0 ∧ s.halted = false ∧ 0 < (s.gpr.get 1).toNat :=
  ⟨⟨0, Bank32.const 1, Bank32.const Vec128.zero, false, false, false, false, fun _ => 0⟩,
    rfl, rfl, by decide⟩

/-! ## §9. `qsag_asm_ct_eq_bytes_x86_64`: variable-length equality loop -/

theorem mask32_toNat (v : UInt64) : (maskGprWidth false v).toNat = v.toNat % 4294967296 := by
  show (v &&& 0xFFFFFFFF).toNat = _
  rw [UInt64.toNat_and]
  exact Constructive.and_mask v.toNat 32

theorem mask32_of_lt (v : UInt64) (h : v.toNat < 4294967296) : maskGprWidth false v = v :=
  u64_eq_of_toNat (by rw [mask32_toNat]; exact Nat.mod_eq_of_lt h)

/-- The 32-bit XOR of two zero-extended bytes, as the loop body computes it. -/
def byteDiff (x y : UInt8) : UInt64 :=
  maskGprWidth false (maskGprWidth false x.toUInt64 ^^^ maskGprWidth false y.toUInt64)

theorem byteDiff_eq (x y : UInt8) : byteDiff x y = x.toUInt64 ^^^ y.toUInt64 := by
  have hx : x.toUInt64.toNat < 2 ^ 8 := by rw [UInt8.toNat_toUInt64]; exact x.toNat_lt
  have hy : y.toUInt64.toNat < 2 ^ 8 := by rw [UInt8.toNat_toUInt64]; exact y.toNat_lt
  have hxy : (x.toUInt64 ^^^ y.toUInt64).toNat < 2 ^ 8 := by
    rw [UInt64.toNat_xor]; exact Nat.xor_lt_two_pow hx hy
  unfold byteDiff
  rw [mask32_of_lt x.toUInt64 (by omega), mask32_of_lt y.toUInt64 (by omega), mask32_of_lt _ (by omega)]

/-- One accumulator update keeps the accumulator a byte and records any difference. -/
theorem accStep_spec (acc : UInt64) (x y : UInt8) (hacc : acc.toNat < 256) :
    (maskGprWidth false (acc ||| byteDiff x y)).toNat < 256 ∧
    (maskGprWidth false (acc ||| byteDiff x y) = 0 ↔ acc = 0 ∧ x = y) := by
  have hx : x.toUInt64.toNat < 2 ^ 8 := by rw [UInt8.toNat_toUInt64]; exact x.toNat_lt
  have hy : y.toUInt64.toNat < 2 ^ 8 := by rw [UInt8.toNat_toUInt64]; exact y.toNat_lt
  have hxy : (x.toUInt64 ^^^ y.toUInt64).toNat < 2 ^ 8 := by
    rw [UInt64.toNat_xor]; exact Nat.xor_lt_two_pow hx hy
  have hor : (acc ||| (x.toUInt64 ^^^ y.toUInt64)).toNat < 2 ^ 8 := by
    rw [UInt64.toNat_or]; exact Nat.or_lt_two_pow hacc hxy
  rw [byteDiff_eq, mask32_of_lt _ (by omega)]
  refine ⟨hor, ?_⟩
  rw [UInt64.or_eq_zero_iff, UInt64.xor_eq_zero_iff]
  constructor
  · intro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have := congrArg UInt64.toUInt8 h2
    rw [UInt8.toUInt8_toUInt64, UInt8.toUInt8_toUInt64] at this
    exact this
  · intro ⟨h1, h2⟩
    exact ⟨h1, by rw [h2]⟩

/-- The accumulator after `k` loop iterations starting from `acc`. -/
def eqAcc : Nat → (UInt64 → UInt8) → UInt64 → UInt64 → UInt64 → UInt64
  | 0, _, _, _, acc => acc
  | k + 1, m, p, q, acc => eqAcc k m (p + 1) (q + 1) (maskGprWidth false (acc ||| byteDiff (m p) (m q)))

theorem eqAcc_spec (m : UInt64 → UInt8) (k : Nat) : ∀ (p q acc : UInt64), acc.toNat < 256 →
    (eqAcc k m p q acc).toNat < 256 ∧
    (eqAcc k m p q acc = 0 ↔
      acc = 0 ∧ ∀ i : Nat, i < k → m (p + UInt64.ofNat i) = m (q + UInt64.ofNat i)) := by
  induction k with
  | zero =>
    intro p q acc hacc
    exact ⟨hacc, fun h => ⟨h, fun i hi => absurd hi (Nat.not_lt_zero i)⟩, fun h => h.1⟩
  | succ k ih =>
    intro p q acc hacc
    obtain ⟨hlt', hz'⟩ := accStep_spec acc (m p) (m q) hacc
    obtain ⟨ih1, ih2⟩ := ih (p + 1) (q + 1) _ hlt'
    refine ⟨ih1, ?_⟩
    show eqAcc k m (p + 1) (q + 1) (maskGprWidth false (acc ||| byteDiff (m p) (m q))) = 0 ↔ _
    constructor
    · intro h0
      obtain ⟨ha, hall⟩ := ih2.mp h0
      obtain ⟨hacc0, hpq⟩ := hz'.mp ha
      refine ⟨hacc0, fun i hi => ?_⟩
      cases i with
      | zero => rw [addr_zero, addr_zero]; exact hpq
      | succ j => rw [← addr_succ, ← addr_succ]; exact hall j (by omega)
    · intro ⟨hacc0, hall⟩
      apply ih2.mpr
      refine ⟨hz'.mpr ⟨hacc0, ?_⟩, fun i hi => ?_⟩
      · have := hall 0 (by omega)
        rw [addr_zero, addr_zero] at this
        exact this
      · have := hall (i + 1) (by omega)
        rw [← addr_succ, ← addr_succ] at this
        exact this

/-- `sub eax, 1; shr eax, 31` turns a byte-sized accumulator into its zero test. -/
theorem eqTail_spec (A : UInt64) (hA : A.toNat < 256) :
    maskGprWidth false (maskGprWidth false (maskGprWidth false (UInt64.ofNat
      (((maskGprWidth false A).toNat + 0x100000000 - (maskGprWidth false 1).toNat) % 0x100000000))) >>>
        UInt64.ofNat (31 % 32)) = if A = 0 then 1 else 0 := by
  if h0 : A = 0 then
    subst h0; rw [ite_eq_left rfl]; decide
  else
    rw [ite_eq_right h0]
    have hpos : 0 < A.toNat := Nat.pos_of_ne_zero (fun h => h0 (u64_eq_of_toNat h))
    have hA' : (maskGprWidth false A).toNat = A.toNat := by rw [mask32_toNat]; omega
    have h1 : (maskGprWidth false 1).toNat = 1 := by decide
    apply u64_eq_of_toNat
    have h31 : (UInt64.ofNat (31 % 32)).toNat % 64 = 31 := by decide
    have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
    rw [mask32_toNat, UInt64.toNat_shiftRight, h31, mask32_toNat, mask32_toNat, UInt64.toNat_ofNat', hA', h1,
      Nat.shiftRight_eq_div_pow, h64]
    show _ / 2147483648 % 4294967296 = 0
    omega

/-- ASCII bytes of the symbol name `qsag_asm_ct_eq_bytes_x86_64`. -/
@[expose] def ctEqBytesX86Name : List UInt8 :=
  [0x71, 0x73, 0x61, 0x67, 0x5f, 0x61, 0x73, 0x6d, 0x5f, 0x63, 0x74, 0x5f, 0x65, 0x71, 0x5f, 0x62,
   0x79, 0x74, 0x65, 0x73, 0x5f, 0x78, 0x38, 0x36, 0x5f, 0x36, 0x34]

def ctEqBytesX86Prog : List (DecodedInstr X86Instr) := [
  ⟨0, 2, .aluRegReg .xorOp false 0 0⟩,
  ⟨2, 3, .movRegReg true 1 2⟩,
  ⟨5, 4, .loadGpr 1 false 8 (.baseDisp 7 0)⟩,
  ⟨9, 4, .loadGpr 1 false 9 (.baseDisp 6 0)⟩,
  ⟨13, 3, .aluRegReg .xorOp false 8 9⟩,
  ⟨16, 3, .aluRegReg .orOp false 0 8⟩,
  ⟨19, 3, .incDec true true 7⟩,
  ⟨22, 3, .incDec true true 6⟩,
  ⟨25, 3, .incDec false true 1⟩,
  ⟨28, 2, .jcc 5 5⟩,
  ⟨30, 3, .aluImm .sub false 0 1⟩,
  ⟨33, 3, .shiftImm .shr false 0 31⟩,
  ⟨36, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨39, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨42, 1, .ret⟩]

theorem ctEqBytesX86_decodes :
    (findSliceByNameBytes x86ExtractedSlices ctEqBytesX86Name).bind
      (fun sl => decodeX86Stream sl.code) = some ctEqBytesX86Prog := by
  decide +kernel

section EqBytesX86
variable {r2 r3 r4 r5 r10 r11 r12 r13 r14 r15 : UInt64} {y : Bank16 Vec256} {dy : Bool}
  {m : UInt64 → UInt8}

/-- One trip round the compare loop (eight instructions). -/
theorem ctEqBytesX86_body (c p q acc x8 x9 : UInt64) (cf o zf : Bool) (fuel : Nat) :
    (runX86 ctEqBytesX86Prog (fuel + 8)
      ⟨5, ⟨acc, c, r2, r3, r4, r5, q, p, x8, x9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, m⟩).1 =
    (runX86 ctEqBytesX86Prog fuel
      ⟨jccPc (!(c - 1 == 0)) 5 30,
        ⟨maskGprWidth false (acc ||| byteDiff (m p) (m q)), c - 1, r2, r3, r4, r5, q + 1, p + 1,
          byteDiff (m p) (m q), maskGprWidth false (m q).toUInt64, r10, r11, r12, r13, r14, r15⟩,
        y, false, evalX86IncDecOf false true c, c - 1 == 0, dy, false, m⟩).1 := by
  iterate 8
    refine Eq.trans (runX86_step_fst _ _ _ _ rfl rfl) ?_
    simp only [stepX86_load8, stepX86_xorRR, stepX86_orRR, stepX86_inc, stepX86_dec, stepX86_jnz,
      maskGprWidth_true, u64_add_neg_one, UInt64.add_zero,
      b16get_0, b16get_1, b16get_6, b16get_7, b16get_8, b16get_9,
      b16set_0, b16set_1, b16set_6, b16set_7, b16set_8, b16set_9]
  try rfl

theorem ctEqBytesX86_loop (k : Nat) : ∀ (c p q acc x8 x9 : UInt64) (cf o zf : Bool) (fuel : Nat),
    c.toNat = k + 1 → ∃ x8' x9' : UInt64,
    (runX86 ctEqBytesX86Prog (8 * (k + 1) + fuel)
      ⟨5, ⟨acc, c, r2, r3, r4, r5, q, p, x8, x9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, m⟩).1 =
    (runX86 ctEqBytesX86Prog fuel
      ⟨30, ⟨eqAcc (k + 1) m p q acc, 0, r2, r3, r4, r5, q + UInt64.ofNat (k + 1), p + UInt64.ofNat (k + 1),
          x8', x9', r10, r11, r12, r13, r14, r15⟩,
        y, false, false, true, dy, false, m⟩).1 := by
  induction k with
  | zero =>
    intro c p q acc x8 x9 cf o zf fuel hc
    have hc1 : c = 1 := u64_eq_of_toNat hc
    subst hc1
    refine ⟨byteDiff (m p) (m q), maskGprWidth false (m q).toUInt64, ?_⟩
    rw [show 8 * (0 + 1) + fuel = fuel + 8 from by omega, ctEqBytesX86_body, u64_one_sub_one,
      u64_zero_beq_zero]
    try rfl
  | succ k ih =>
    intro c p q acc x8 x9 cf o zf fuel hc
    have hc' := u64_pred_toNat c k hc
    have hne := u64_ne_zero_of_toNat_succ (c - 1) k hc'
    obtain ⟨x8', x9', h⟩ := ih (c - 1) (p + 1) (q + 1) (maskGprWidth false (acc ||| byteDiff (m p) (m q)))
      (byteDiff (m p) (m q)) (maskGprWidth false (m q).toUInt64) false (evalX86IncDecOf false true c) false fuel hc'
    refine ⟨x8', x9', ?_⟩
    rw [show 8 * (k + 1 + 1) + fuel = (8 * (k + 1) + fuel) + 8 from by omega, ctEqBytesX86_body,
      beq_false_of_ne hne, show jccPc (!false) 5 30 = 5 from rfl, h, addr_succ, addr_succ]
    try rfl

theorem ctEqBytesX86_run {r0 r1 r6 r7 r8 r9 : UInt64} {cf o zf : Bool} (k j : Nat)
    (hn : r2.toNat = k + 1) :
    (runX86 ctEqBytesX86Prog (8 * (k + 1) + 7 + j)
      ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨42, ⟨maskGprWidth false (maskGprWidth false (maskGprWidth false (UInt64.ofNat
            (((maskGprWidth false (eqAcc (k + 1) m r7 r6 0)).toNat + 0x100000000 -
              (maskGprWidth false 1).toNat) % 0x100000000))) >>> UInt64.ofNat (31 % 32)),
          0, r2, r3, r4, r5, r6 + UInt64.ofNat (k + 1), r7 + UInt64.ofNat (k + 1), 0, 0,
          r10, r11, r12, r13, r14, r15⟩,
        y, false, false, true, dy, true, m⟩ := by
  rw [show 8 * (k + 1) + 7 + j = (8 * (k + 1) + (j + 5)) + 2 from by omega]
  iterate 2
    refine Eq.trans (runX86_step_fst _ _ _ _ rfl rfl) ?_
    simp only [stepX86_movRR, stepX86_xorRR, maskGprWidth_true, mask32_xor_self, u64_zero_beq_zero,
      b16get_0, b16get_2, b16set_0, b16set_1]
  obtain ⟨x8', x9', h⟩ := ctEqBytesX86_loop (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5) (r10 := r10)
    (r11 := r11) (r12 := r12) (r13 := r13) (r14 := r14) (r15 := r15) (y := y) (dy := dy) (m := m)
    k r2 r7 r6 0 r8 r9 false false true (j + 5) hn
  rw [h]
  iterate 5
    refine Eq.trans (runX86_step_fst _ _ _ _ rfl rfl) ?_
    simp only [stepX86_subImm32, stepX86_shr32, stepX86_xorRR, stepX86_ret, mask32_xor_self,
      u64_zero_beq_zero, b16get_0, b16get_8, b16get_9, b16set_0, b16set_8, b16set_9]
  exact runX86_halted_fst _ _ _ rfl

end EqBytesX86

/-- **Machine-code refinement of `qsag_asm_ct_eq_bytes_x86_64`.** For a length `n = rdx ≥ 1` (the
Rust wrapper returns early on empty slices; the loop is bottom-tested), at most `8 n + 7` steps
halt with `rax = 1` when the `n` bytes at `rdi` equal the `n` bytes at `rsi` and `rax = 0`
otherwise (addresses wrap modulo `2^64`); memory is untouched and `r8`, `r9` are wiped. -/
theorem ct_eq_bytes_x86_64_mc_refines :
    ∃ slice prog, findSliceByNameBytes x86ExtractedSlices ctEqBytesX86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 0 < (s.gpr.get 2).toNat →
        8 * (s.gpr.get 2).toNat + 7 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        (runX86 prog fuel s).1.gpr.get 0 =
          (if ∀ i : Nat, i < (s.gpr.get 2).toNat →
              s.mem (s.gpr.get 7 + UInt64.ofNat i) = s.mem (s.gpr.get 6 + UInt64.ofNat i)
            then 1 else 0) ∧
        (runX86 prog fuel s).1.mem = s.mem ∧
        (runX86 prog fuel s).1.gpr.get 8 = 0 ∧ (runX86 prog fuel s).1.gpr.get 9 = 0 := by
  obtain ⟨sl, hf, hd⟩ := slice_decode_x86 ctEqBytesX86_decodes
  refine ⟨sl, ctEqBytesX86Prog, hf, hd, ?_⟩
  intro s fuel hpc hh hn hfuel
  obtain ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
    y, cf, o, zf, dy, hlt, m⟩ := s
  have hpc' : pc = 0 := hpc
  have hh' : hlt = false := hh
  subst hpc' hh'
  have hn' : 0 < r2.toNat := hn
  have hfuel' : 8 * r2.toNat + 7 ≤ fuel := hfuel
  obtain ⟨k, hk⟩ : ∃ k, r2.toNat = k + 1 := ⟨r2.toNat - 1, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, fuel = 8 * (k + 1) + 7 + j := ⟨fuel - (8 * (k + 1) + 7), by omega⟩
  subst hj
  rw [ctEqBytesX86_run k j hk]
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  obtain ⟨hlt, hz⟩ := eqAcc_spec m (k + 1) r7 r6 0 (by decide)
  show maskGprWidth false (maskGprWidth false (maskGprWidth false (UInt64.ofNat
      (((maskGprWidth false (eqAcc (k + 1) m r7 r6 0)).toNat + 0x100000000 -
        (maskGprWidth false 1).toNat) % 0x100000000))) >>> UInt64.ofNat (31 % 32)) =
    if ∀ i : Nat, i < r2.toNat → m (r7 + UInt64.ofNat i) = m (r6 + UInt64.ofNat i) then 1 else 0
  rw [eqTail_spec _ hlt]
  if hA : eqAcc (k + 1) m r7 r6 0 = 0 then
    rw [ite_eq_left hA, ite_eq_left (fun i hi => (hz.mp hA).2 i (by omega))]
  else
    rw [ite_eq_right hA, ite_eq_right (fun h => hA (hz.mpr ⟨rfl, fun i hi => h i (by omega)⟩))]

/-- The preconditions of `ct_eq_bytes_x86_64_mc_refines` are satisfiable (length 1). -/
theorem ct_eq_bytes_x86_64_pre_inhabited :
    ∃ s : X86State, s.pc = 0 ∧ s.halted = false ∧ 0 < (s.gpr.get 2).toNat :=
  ⟨⟨0, Bank16.const 1, Bank16.const Vec256.zero, false, false, false, false, false, fun _ => 0⟩,
    rfl, rfl, by decide⟩

/-! ## §10. Mutation refusal: the specifications and the NI checker reject mutated machine code -/

/-- Entry state with the given `rdi`, `rsi`, `rdx`, `rax`, every memory byte `b`, all else zero. -/
@[expose] def x86Init (rdi rsi rdx rax : UInt64) (b : UInt8) : X86State :=
  ⟨0, ⟨rax, 0, rdx, 0, 0, 0, rsi, rdi, 0, 0, 0, 0, 0, 0, 0, 0⟩, Bank16.const Vec256.zero,
    false, false, false, false, false, fun _ => b⟩

/-- Entry state with the given `x0`, `x1`, every memory byte `b`, all else zero. -/
@[expose] def armInit (x0 x1 : UInt64) (b : UInt8) : Arm64State :=
  ⟨0, ⟨⟨x0, x1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Bank16.const 0⟩, Bank32.const Vec128.zero,
    false, false, false, false, fun _ => b⟩

/-- Mutant of `ct_eq_32_x86_64` with the final `xor eax, 1` turned into `xor eax, 0`: it decodes,
halts, and returns `0` on two equal (all-zero) buffers, where the specification demands `1`. -/
theorem ct_eq_32_x86_64_mutant_refuted :
    ((findSliceByNameBytes x86ExtractedSlices ctEq32X86Name).bind
        (fun sl => decodeX86Stream (patchBytesAt sl.code 52 [0x83, 0xF0, 0x00]))).any
      (fun p => (runX86 p 20 (x86Init 0 64 0 0 0)).1.halted &&
        (runX86 p 20 (x86Init 0 64 0 0 0)).1.gpr.get 0 == 0) = true ∧
    (∀ i : Nat, i < 32 →
      (x86Init 0 64 0 0 0).mem ((x86Init 0 64 0 0 0).gpr.get 7 + UInt64.ofNat i) =
      (x86Init 0 64 0 0 0).mem ((x86Init 0 64 0 0 0).gpr.get 6 + UInt64.ofNat i)) :=
  ⟨by decide +kernel, fun _ _ => rfl⟩

/-- NI tooth: the compiled `ct_eq_32_x86_64` passes the 3-way NI checker under its contract, and
the variant whose `or rax, rcx` is replaced by `je +1; nop` (a branch on flags derived from the
secret buffers) is rejected. -/
theorem ct_eq_32_x86_64_secret_branch_rejected :
    (findSliceByNameBytes x86ExtractedSlices ctEq32X86Name).map
        (fun sl => (checkX86ThreeWayNI sl.code
            (mkContract "qsag_asm_ct_eq_32_x86_64" [4, 7, 6] [] [1, 2, 8]),
          checkX86ThreeWayNI (patchBytesAt sl.code 30 [0x74, 0x01, 0x90])
            (mkContract "qsag_asm_ct_eq_32_x86_64" [4, 7, 6] [] [1, 2, 8])))
      = some (true, false) := by
  decide +kernel

/-- Mutant of `ct_eq_32_aarch64` with the final `eor x0, x0, #1` turned into `nop`: it returns `0`
on two equal (all-zero) buffers, where the specification demands `1`. -/
theorem ct_eq_32_aarch64_mutant_refuted :
    ((findSliceByNameBytes aarch64ExtractedSlices ctEq32ArmName).bind
        (fun sl => decodeArm64Stream (patchBytesAt sl.code 56 [0x1F, 0x20, 0x03, 0xD5]))).any
      (fun p => (runArm64 p 22 (armInit 0 64 0)).1.halted &&
        (runArm64 p 22 (armInit 0 64 0)).1.gpr.get 0 == 0) = true ∧
    (∀ i : Nat, i < 32 →
      (armInit 0 64 0).mem ((armInit 0 64 0).gpr.get 0 + UInt64.ofNat i) =
      (armInit 0 64 0).mem ((armInit 0 64 0).gpr.get 1 + UInt64.ofNat i)) :=
  ⟨by decide +kernel, fun _ _ => rfl⟩

/-- NI tooth: the compiled `ct_eq_32_aarch64` passes the 3-way NI checker under its contract, and
the variant whose `lsr x0, x2, #63` is replaced by `cbz w2, +8` (a branch on the secret difference
word) is rejected. -/
theorem ct_eq_32_aarch64_secret_branch_rejected :
    (findSliceByNameBytes aarch64ExtractedSlices ctEq32ArmName).map
        (fun sl => (checkArm64ThreeWayNI sl.code
            (mkContract "qsag_asm_ct_eq_32_aarch64" [0, 1] [] [2, 3, 4, 5, 6, 7]),
          checkArm64ThreeWayNI (patchBytesAt sl.code 52 [0x42, 0x00, 0x00, 0x34])
            (mkContract "qsag_asm_ct_eq_32_aarch64" [0, 1] [] [2, 3, 4, 5, 6, 7])))
      = some (true, false) := by
  decide +kernel

/-- Mutant of `ct_memzero_x86_64` with `xor eax, eax` turned into `mov eax, eax`: with `rax = 0xAA`
and length 1 it halts leaving the byte at `rdi` nonzero. -/
theorem ct_memzero_x86_64_mutant_refuted :
    ((findSliceByNameBytes x86ExtractedSlices ctMemzeroX86Name).bind
        (fun sl => decodeX86Stream (patchBytesAt sl.code 3 [0x89, 0xC0]))).any
      (fun p => (runX86 p 8 (x86Init 16 1 0 0xAA 0x55)).1.halted &&
        (runX86 p 8 (x86Init 16 1 0 0xAA 0x55)).1.mem 16 != 0) = true := by
  decide +kernel

/-- Mutant of `ct_memzero_aarch64` with `strb wzr, [x0], #1` turned into `strb w1, [x0], #1`: with
length 1 it halts leaving the byte at `x0` equal to `1`. -/
theorem ct_memzero_aarch64_mutant_refuted :
    ((findSliceByNameBytes aarch64ExtractedSlices ctMemzeroArmName).bind
        (fun sl => decodeArm64Stream (patchBytesAt sl.code 0 [0x01, 0x14, 0x00, 0x38]))).any
      (fun p => (runArm64 p 5 (armInit 16 1 0x55)).1.halted &&
        (runArm64 p 5 (armInit 16 1 0x55)).1.mem 16 != 0) = true := by
  decide +kernel

/-- Mutant of `ct_eq_bytes_x86_64` with `shr eax, 31` turned into `shr eax, 30`: on two equal
one-byte buffers it returns `3`, where the specification demands `1`. -/
theorem ct_eq_bytes_x86_64_mutant_refuted :
    ((findSliceByNameBytes x86ExtractedSlices ctEqBytesX86Name).bind
        (fun sl => decodeX86Stream (patchBytesAt sl.code 33 [0xC1, 0xE8, 0x1E]))).any
      (fun p => (runX86 p 15 (x86Init 0 64 1 0 0)).1.halted &&
        (runX86 p 15 (x86Init 0 64 1 0 0)).1.gpr.get 0 == 3) = true ∧
    (∀ i : Nat, i < ((x86Init 0 64 1 0 0).gpr.get 2).toNat →
      (x86Init 0 64 1 0 0).mem ((x86Init 0 64 1 0 0).gpr.get 7 + UInt64.ofNat i) =
      (x86Init 0 64 1 0 0).mem ((x86Init 0 64 1 0 0).gpr.get 6 + UInt64.ofNat i)) :=
  ⟨by decide +kernel, fun _ _ => rfl⟩

/-- NI tooth: the compiled `ct_eq_bytes_x86_64` passes the 3-way NI checker under its contract, and
the variant whose `or eax, r8d` is replaced by `je +1; nop` (a branch on the flags of the secret
byte XOR) is rejected. -/
theorem ct_eq_bytes_x86_64_secret_branch_rejected :
    (findSliceByNameBytes x86ExtractedSlices ctEqBytesX86Name).map
        (fun sl => (checkX86ThreeWayNI sl.code
            (mkContract "qsag_asm_ct_eq_bytes_x86_64" [4, 7, 6, 2] [] [8, 9]),
          checkX86ThreeWayNI (patchBytesAt sl.code 16 [0x74, 0x01, 0x90])
            (mkContract "qsag_asm_ct_eq_bytes_x86_64" [4, 7, 6, 2] [] [8, 9])))
      = some (true, false) := by
  decide +kernel

/-! ## §11. Goldilocks field kernels (`p = 2^64 - 2^32 + 1`) -/

theorem sbb32_self (v : UInt64) (cf : Bool) :
    evalX86Alu .sbb false v v cf = (if cf then 0xFFFFFFFF else 0, cf, !cf) := by
  rw [evalX86Alu_sbb_self_congr false v 0 cf]
  cases cf <;> decide

theorem sbb64_self (v : UInt64) (cf : Bool) :
    evalX86Alu .sbb true v v cf = (if cf then 0xFFFFFFFFFFFFFFFF else 0, cf, !cf) := by
  rw [evalX86Alu_sbb_self_congr true v 0 cf]
  cases cf <;> decide

/-- Add `2^32 - 1` (the residue of `2^64`) when a carry is pending; report the new carry. -/
def foldCarry (s : UInt64) (c : Bool) : UInt64 × Bool :=
  (s + (if c then 0xFFFFFFFF else 0),
    decide (s.toNat + (if c then (0xFFFFFFFF : UInt64) else 0).toNat ≥ 0x10000000000000000))

/-- Branch-free conditional subtraction of `p`, as `add r8, r9; sbb rcx, rcx; and rcx, r9; add`. -/
def goldCanon (s : UInt64) : UInt64 :=
  s + ((if decide (s.toNat + (maskGprWidth false 4294967295).toNat ≥ 0x10000000000000000)
        then 0xFFFFFFFFFFFFFFFF else 0) &&& maskGprWidth false 4294967295)

theorem goldCanon_toNat (s : UInt64) : (goldCanon s).toNat = s.toNat % goldilocksPrime := by
  have hs : s.toNat < 18446744073709551616 := s.toNat_lt
  have hm : maskGprWidth false 4294967295 = 4294967295 := by decide
  have hE : (4294967295 : UInt64).toNat = 4294967295 := rfl
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  unfold goldCanon
  rw [hm, hE]
  show _ = s.toNat % 18446744069414584321
  if h : s.toNat + 4294967295 ≥ 18446744073709551616 then
    have hand : (0xFFFFFFFFFFFFFFFF : UInt64) &&& 4294967295 = 4294967295 := by decide
    rw [decide_eq_true h, ite_eq_left rfl, hand, UInt64.toNat_add, hE, h64]
    omega
  else
    have hand : (0 : UInt64) &&& 4294967295 = 0 := by decide
    have h0 : (0 : UInt64).toNat = 0 := rfl
    rw [decide_eq_false h, ite_eq_right (by decide), hand, UInt64.toNat_add, h0, h64]
    omega

/-- Two carry folds leave a word congruent to the full sum `s + 2^64·c` modulo `p`. -/
theorem foldCarry2_mod (s : UInt64) (c : Bool) :
    (foldCarry (foldCarry s c).1 (foldCarry s c).2).1.toNat % goldilocksPrime =
      (s.toNat + (if c then 18446744073709551616 else 0)) % goldilocksPrime := by
  have hs : s.toNat < 18446744073709551616 := s.toNat_lt
  have hE : (0xFFFFFFFF : UInt64).toNat = 4294967295 := rfl
  have h0 : (0 : UInt64).toNat = 0 := rfl
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  have hz : ∀ x : UInt64, foldCarry x false = (x, false) := by
    intro x
    have hx : x.toNat < 18446744073709551616 := x.toNat_lt
    unfold foldCarry
    rw [ite_eq_right (by decide), UInt64.add_zero, h0, decide_eq_false (by omega)]
  show _ % 18446744069414584321 = _ % 18446744069414584321
  cases c with
  | false => rw [hz s, hz s, ite_eq_right (by decide)]; rfl
  | true =>
    rw [ite_eq_left rfl]
    have hf : foldCarry s true = (s + 0xFFFFFFFF,
        decide (s.toNat + 4294967295 ≥ 18446744073709551616)) := by
      unfold foldCarry
      rw [ite_eq_left rfl, hE]
    rw [hf]
    if h : s.toNat + 4294967295 ≥ 18446744073709551616 then
      rw [decide_eq_true h]
      show (foldCarry (s + 0xFFFFFFFF) true).1.toNat % _ = _
      show ((s + 0xFFFFFFFF) + (if true then 0xFFFFFFFF else 0)).toNat % _ = _
      rw [ite_eq_left rfl, UInt64.toNat_add, UInt64.toNat_add, hE, h64]
      omega
    else
      rw [decide_eq_false h]
      show (foldCarry (s + 0xFFFFFFFF) false).1.toNat % _ = _
      rw [hz, UInt64.toNat_add, hE, h64]
      omega

/-- The value `goldilocks_add_ct` leaves in `rax`. -/
def goldAddMc (a b : UInt64) : UInt64 :=
  goldCanon (foldCarry (foldCarry (a + b) (decide (a.toNat + b.toNat ≥ 0x10000000000000000))).1
    (foldCarry (a + b) (decide (a.toNat + b.toNat ≥ 0x10000000000000000))).2).1

theorem goldAddMc_toNat (a b : UInt64) :
    (goldAddMc a b).toNat = (a.toNat + b.toNat) % goldilocksPrime := by
  have ha : a.toNat < 18446744073709551616 := a.toNat_lt
  have hb : b.toNat < 18446744073709551616 := b.toNat_lt
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  unfold goldAddMc
  rw [goldCanon_toNat, foldCarry2_mod]
  show _ % 18446744069414584321 = _ % 18446744069414584321
  if h : a.toNat + b.toNat ≥ 18446744073709551616 then
    rw [decide_eq_true h, ite_eq_left rfl, UInt64.toNat_add, h64]
    omega
  else
    rw [decide_eq_false h, ite_eq_right (by decide), UInt64.toNat_add, h64]
    omega

/-- The value `goldilocks_sub_ct` leaves in `rax`. -/
def goldSubMc (a b : UInt64) : UInt64 :=
  (goldCanon a - goldCanon b) +
    ((if decide ((goldCanon a).toNat < (goldCanon b).toNat) then 0xFFFFFFFFFFFFFFFF else 0) &&&
      18446744069414584321)

theorem goldSubMc_toNat (a b : UInt64) :
    (goldSubMc a b).toNat =
      (a.toNat + goldilocksPrime - b.toNat % goldilocksPrime) % goldilocksPrime := by
  have hx := goldCanon_toNat a
  have hy := goldCanon_toNat b
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  have hP : (18446744069414584321 : UInt64).toNat = 18446744069414584321 := rfl
  have h0 : (0 : UInt64).toNat = 0 := rfl
  unfold goldSubMc
  have hx' : (goldCanon a).toNat = a.toNat % 18446744069414584321 := hx
  have hy' : (goldCanon b).toNat = b.toNat % 18446744069414584321 := hy
  show _ = (a.toNat + 18446744069414584321 - b.toNat % 18446744069414584321) % 18446744069414584321
  if h : (goldCanon a).toNat < (goldCanon b).toNat then
    have hand : (0xFFFFFFFFFFFFFFFF : UInt64) &&& 18446744069414584321 = 18446744069414584321 := by
      decide
    rw [decide_eq_true h, ite_eq_left rfl, hand, UInt64.toNat_add, UInt64.toNat_sub, hP, h64]
    omega
  else
    have hand : (0 : UInt64) &&& 18446744069414584321 = 0 := by decide
    rw [decide_eq_false h, ite_eq_right (by decide), hand, UInt64.toNat_add, UInt64.toNat_sub, h0, h64]
    omega

/-- ASCII bytes of the symbol name `qsag_asm_goldilocks_add_ct_x86_64`. -/
@[expose] def goldAddX86Name : List UInt8 :=
  [0x71, 0x73, 0x61, 0x67, 0x5f, 0x61, 0x73, 0x6d, 0x5f, 0x67, 0x6f, 0x6c, 0x64, 0x69, 0x6c, 0x6f,
   0x63, 0x6b, 0x73, 0x5f, 0x61, 0x64, 0x64, 0x5f, 0x63, 0x74, 0x5f, 0x78, 0x38, 0x36, 0x5f, 0x36, 0x34]

def goldAddX86Prog : List (DecodedInstr X86Instr) := [
  ⟨0, 3, .movRegReg true 0 7⟩,
  ⟨3, 3, .aluRegReg .add true 0 6⟩,
  ⟨6, 3, .aluRegReg .sbb false 8 8⟩,
  ⟨9, 3, .aluRegReg .add true 0 8⟩,
  ⟨12, 3, .aluRegReg .sbb false 10 10⟩,
  ⟨15, 3, .aluRegReg .add true 0 10⟩,
  ⟨18, 6, .movImm false 9 4294967295⟩,
  ⟨24, 3, .movRegReg true 8 0⟩,
  ⟨27, 3, .aluRegReg .add true 8 9⟩,
  ⟨30, 3, .aluRegReg .sbb true 1 1⟩,
  ⟨33, 3, .aluRegReg .andOp true 1 9⟩,
  ⟨36, 3, .aluRegReg .add true 0 1⟩,
  ⟨39, 2, .aluRegReg .xorOp false 1 1⟩,
  ⟨41, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨44, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨47, 3, .aluRegReg .xorOp false 10 10⟩,
  ⟨50, 1, .ret⟩]

theorem goldAddX86_decodes :
    (findSliceByNameBytes x86ExtractedSlices goldAddX86Name).bind
      (fun sl => decodeX86Stream sl.code) = some goldAddX86Prog := by
  decide +kernel

theorem goldAddX86_run (k : Nat) (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    (runX86 goldAddX86Prog (k + 17)
      ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨50, ⟨goldAddMc r7 r6, 0, r2, r3, r4, r5, r6, r7, 0, 0, 0, r11, r12, r13, r14, r15⟩,
        y, false, false, true, dy, true, m⟩ := by
  iterate 17
    refine Eq.trans (runX86_step_fst _ _ _ _ rfl rfl) ?_
    simp only [stepX86_movRR, stepX86_addRR64, stepX86_sbbRR, stepX86_andRR, stepX86_movImm,
      stepX86_xorRR, stepX86_ret, maskGprWidth_true, mask32_xor_self, u64_zero_beq_zero,
      sbb32_self, sbb64_self, uint64_evalAdd_eq,
      b16get_0, b16get_1, b16get_6, b16get_7, b16get_8, b16get_9, b16get_10,
      b16set_0, b16set_1, b16set_8, b16set_9, b16set_10]
  exact runX86_halted_fst _ _ _ rfl

/-- **Machine-code refinement of `qsag_asm_goldilocks_add_ct_x86_64`.** For every pair of 64-bit
inputs (canonical or not), at most 17 steps halt with `rax` the canonical residue of `rdi + rsi`
modulo `p = 2^64 - 2^32 + 1`; memory is untouched and `rcx`, `r8`, `r9`, `r10` are wiped. -/
theorem goldilocks_add_ct_x86_64_mc_refines :
    ∃ slice prog, findSliceByNameBytes x86ExtractedSlices goldAddX86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 17 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        ((runX86 prog fuel s).1.gpr.get 0).toNat =
          ((s.gpr.get 7).toNat + (s.gpr.get 6).toNat) % goldilocksPrime ∧
        (runX86 prog fuel s).1.mem = s.mem ∧
        (runX86 prog fuel s).1.gpr.get 1 = 0 ∧ (runX86 prog fuel s).1.gpr.get 8 = 0 ∧
        (runX86 prog fuel s).1.gpr.get 9 = 0 ∧ (runX86 prog fuel s).1.gpr.get 10 = 0 := by
  obtain ⟨sl, hf, hd⟩ := slice_decode_x86 goldAddX86_decodes
  refine ⟨sl, goldAddX86Prog, hf, hd, ?_⟩
  intro s fuel hpc hh hfuel
  obtain ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
    y, cf, o, zf, dy, hlt, m⟩ := s
  have hpc' : pc = 0 := hpc
  have hh' : hlt = false := hh
  subst hpc' hh'
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hfuel
  rw [Nat.add_comm 17 k, goldAddX86_run]
  exact ⟨rfl, goldAddMc_toNat r7 r6, rfl, rfl, rfl, rfl, rfl⟩

/-- ASCII bytes of the symbol name `qsag_asm_goldilocks_sub_ct_x86_64`. -/
@[expose] def goldSubX86Name : List UInt8 :=
  [0x71, 0x73, 0x61, 0x67, 0x5f, 0x61, 0x73, 0x6d, 0x5f, 0x67, 0x6f, 0x6c, 0x64, 0x69, 0x6c, 0x6f,
   0x63, 0x6b, 0x73, 0x5f, 0x73, 0x75, 0x62, 0x5f, 0x63, 0x74, 0x5f, 0x78, 0x38, 0x36, 0x5f, 0x36, 0x34]

def goldSubX86Prog : List (DecodedInstr X86Instr) := [
  ⟨0, 6, .movImm false 9 4294967295⟩,
  ⟨6, 3, .movRegReg true 0 7⟩,
  ⟨9, 3, .movRegReg true 8 0⟩,
  ⟨12, 3, .aluRegReg .add true 8 9⟩,
  ⟨15, 3, .aluRegReg .sbb true 1 1⟩,
  ⟨18, 3, .aluRegReg .andOp true 1 9⟩,
  ⟨21, 3, .aluRegReg .add true 0 1⟩,
  ⟨24, 3, .movRegReg true 8 6⟩,
  ⟨27, 3, .aluRegReg .add true 8 9⟩,
  ⟨30, 3, .aluRegReg .sbb true 1 1⟩,
  ⟨33, 3, .aluRegReg .andOp true 1 9⟩,
  ⟨36, 3, .aluRegReg .add true 6 1⟩,
  ⟨39, 3, .aluRegReg .sub true 0 6⟩,
  ⟨42, 3, .aluRegReg .sbb true 8 8⟩,
  ⟨45, 10, .movImm true 10 18446744069414584321⟩,
  ⟨55, 3, .aluRegReg .andOp true 8 10⟩,
  ⟨58, 3, .aluRegReg .add true 0 8⟩,
  ⟨61, 2, .aluRegReg .xorOp false 1 1⟩,
  ⟨63, 2, .aluRegReg .xorOp false 6 6⟩,
  ⟨65, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨68, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨71, 3, .aluRegReg .xorOp false 10 10⟩,
  ⟨74, 1, .ret⟩]

theorem goldSubX86_decodes :
    (findSliceByNameBytes x86ExtractedSlices goldSubX86Name).bind
      (fun sl => decodeX86Stream sl.code) = some goldSubX86Prog := by
  decide +kernel

theorem goldSubX86_run (k : Nat) (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    (runX86 goldSubX86Prog (k + 23)
      ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨74, ⟨goldSubMc r7 r6, 0, r2, r3, r4, r5, 0, r7, 0, 0, 0, r11, r12, r13, r14, r15⟩,
        y, false, false, true, dy, true, m⟩ := by
  iterate 23
    refine Eq.trans (runX86_step_fst _ _ _ _ rfl rfl) ?_
    simp only [stepX86_movRR, stepX86_addRR64, stepX86_subRR64, stepX86_sbbRR, stepX86_andRR,
      stepX86_movImm, stepX86_xorRR, stepX86_ret, maskGprWidth_true, mask32_xor_self,
      u64_zero_beq_zero, sbb64_self, uint64_evalAdd_eq, uint64_evalSub_eq,
      b16get_0, b16get_1, b16get_6, b16get_7, b16get_8, b16get_9, b16get_10,
      b16set_0, b16set_1, b16set_6, b16set_8, b16set_9, b16set_10]
  exact runX86_halted_fst _ _ _ rfl

/-- **Machine-code refinement of `qsag_asm_goldilocks_sub_ct_x86_64`.** For every pair of 64-bit
inputs (canonical or not), at most 23 steps halt with `rax` the canonical residue of `rdi - rsi`
modulo `p`; memory is untouched and `rcx`, `rsi`, `r8`, `r9`, `r10` are wiped. -/
theorem goldilocks_sub_ct_x86_64_mc_refines :
    ∃ slice prog, findSliceByNameBytes x86ExtractedSlices goldSubX86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 23 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        ((runX86 prog fuel s).1.gpr.get 0).toNat =
          ((s.gpr.get 7).toNat + goldilocksPrime - (s.gpr.get 6).toNat % goldilocksPrime) %
            goldilocksPrime ∧
        (runX86 prog fuel s).1.mem = s.mem ∧
        (runX86 prog fuel s).1.gpr.get 1 = 0 ∧ (runX86 prog fuel s).1.gpr.get 6 = 0 ∧
        (runX86 prog fuel s).1.gpr.get 8 = 0 ∧ (runX86 prog fuel s).1.gpr.get 9 = 0 ∧
        (runX86 prog fuel s).1.gpr.get 10 = 0 := by
  obtain ⟨sl, hf, hd⟩ := slice_decode_x86 goldSubX86_decodes
  refine ⟨sl, goldSubX86Prog, hf, hd, ?_⟩
  intro s fuel hpc hh hfuel
  obtain ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
    y, cf, o, zf, dy, hlt, m⟩ := s
  have hpc' : pc = 0 := hpc
  have hh' : hlt = false := hh
  subst hpc' hh'
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hfuel
  rw [Nat.add_comm 23 k, goldSubX86_run]
  exact ⟨rfl, goldSubMc_toNat r7 r6, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Goldilocks multiplication: `2^64 ≡ 2^32 - 1` and `2^96 ≡ -1` reduction of a 128-bit product -/

/-- `x - y`, then subtract `2^32 - 1` when the subtraction borrowed. -/
def subBorrow (x y : UInt64) : UInt64 :=
  (x - y) - (if decide (x.toNat < y.toNat) then 0xFFFFFFFF else 0)

theorem subBorrow_mod (x y : UInt64) (hy : y.toNat < 4294967296) :
    (subBorrow x y).toNat % 18446744069414584321 =
      (x.toNat + 18446744069414584321 - y.toNat) % 18446744069414584321 := by
  have hx : x.toNat < 18446744073709551616 := x.toNat_lt
  have hE : (0xFFFFFFFF : UInt64).toNat = 4294967295 := rfl
  have h0 : (0 : UInt64).toNat = 0 := rfl
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  unfold subBorrow
  if h : x.toNat < y.toNat then
    rw [decide_eq_true h, ite_eq_left rfl, UInt64.toNat_sub, UInt64.toNat_sub, hE, h64]
    omega
  else
    rw [decide_eq_false h, ite_eq_right (by decide), UInt64.toNat_sub, UInt64.toNat_sub, h0, h64]
    omega

/-- `(hi mod 2^32) · (2^32 - 1)` as `shl 32; sub`. -/
