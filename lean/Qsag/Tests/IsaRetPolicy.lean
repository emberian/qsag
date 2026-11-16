module
public import Qsag.Machine.IsaCt
import Qsag.Tactic.AssuranceKit
public section
namespace Qsag.Tests.IsaRetPolicy
open Qsag

def contract : FuncContract := ⟨"ret-policy", [4], [], [], false, 0, 0, true⟩

theorem public_stack_ret_accepted : checkX86ThreeWayNI [0xC3] contract = true := by decide +kernel

theorem tooth_store_return_slot_rejected :
    checkX86ThreeWayNI [0x48, 0x89, 0x04, 0x24, 0xC3] contract ≠ true := by decide +kernel

theorem tooth_secret_stack_ret_rejected :
    checkX86ThreeWayNI [0xC3] { contract with pubGprs := [] } ≠ true := by decide +kernel

theorem tooth_x86_mul_and_mulx_rejected_without_doit :
    ¬ ((transferX86Instr { contract with doitEnabled := false }
        ⟨0, 3, .mulOneOp false true 0⟩ (initX86AbsState contract)).isSome = true ∨
      (transferX86Instr { contract with doitEnabled := false }
        ⟨0, 5, .mulx 0 1 2⟩ (initX86AbsState contract)).isSome = true ∨
      (transferX86Instr { contract with doitEnabled := false }
        ⟨0, 4, .cmovcc 4 true 0 1⟩ (initX86AbsState contract)).isSome = true) := by
  decide +kernel

theorem ret_pops_stack_and_observes_read (s : X86State) (off len : Nat) :
    (stepX86 ⟨off, len, .ret⟩ s).1.pc = (readMem64 s.mem (s.gpr.get 4)).toNat ∧
    (stepX86 ⟨off, len, .ret⟩ s).1.gpr.get 4 = s.gpr.get 4 + 8 ∧
    (stepX86 ⟨off, len, .ret⟩ s).2 = ⟨off, [(s.gpr.get 4, 8)], true⟩ := by
  constructor
  · rfl
  constructor
  · change (s.gpr.set 4 (s.gpr.get 4 + 8)).get 4 = _
    exact Bank16.get_set_eq _ _ _
  · rfl

#verify_constructive public_stack_ret_accepted tooth_store_return_slot_rejected
  tooth_secret_stack_ret_rejected tooth_x86_mul_and_mulx_rejected_without_doit
  ret_pops_stack_and_observes_read
#tooth_pair public_stack_ret_accepted vs tooth_store_return_slot_rejected
#tooth_pair public_stack_ret_accepted vs tooth_secret_stack_ret_rejected
end Qsag.Tests.IsaRetPolicy
