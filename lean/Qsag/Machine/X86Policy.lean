module
public import Qsag.Machine.X86AbsDomain
public section
namespace Qsag

/-- Instructions whose operand-dependent timing requires the caller's DOIT assumption. -/
@[expose] def x86RequiresDoit : X86Instr → Bool
  | .mulOneOp _ _ _ | .mulx _ _ _ | .cmovcc _ _ _ _ => true
  | _ => false

/-- Raw entry-stack aliases cannot be used as ordinary writable data or laundered by LEA. -/
@[expose] def x86AddrTouchesRawStack (st : X86AbsState) : X86MemAddr → Bool :=
  let raw := fun r => match st.gpr.get r with
    | .initSame 4 | .spMinus8 | .spAligned32 => true
    | _ => false
  fun addr => match addr with
  | .baseDisp r _ => raw r
  | .indexedSib base idx _ _ => base.any raw || raw idx
  | _ => false

/-- One fail-closed policy gate shared by every x86 transfer. -/
@[expose] def x86ViolatesPolicy (c : FuncContract) (i : X86Instr) (st : X86AbsState) : Bool :=
  (x86RequiresDoit i && !c.doitEnabled) ||
    match i with
    | .storeGpr _ _ a | .storeImm8 a _ | .vstore _ _ a | .lea _ _ a =>
      x86AddrTouchesRawStack st a
    | _ => false

end Qsag
