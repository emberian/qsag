module
public import Lean
public import Qsag.ElfBinaryVerify
import all Qsag.ElfBinaryVerify
public section
open Lean Qsag

/-! Streaming JSON execution of the binary decoder and operational semantics.
Hex integers are most-significant digit first; memory and instruction strings
are bytes in address order. Only CF, OF and ZF are represented by X86State;
`modeled_rflags_mask` reports this boundary explicitly. Other input flag bits
are preserved in the response and are not claimed as modeled arithmetic flags.
-/
namespace IsaCosim

def requireSome {α : Type} (message : String) : Option α → Except String α
  | some x => .ok x
  | none => .error message

def hexNat (width n : Nat) : String :=
  String.ofList ((List.range width).reverse.map fun i =>
    "0123456789abcdef".toList[(n >>> (4*i)) % 16]!)

def parseHex (s : String) : Except String Nat := do
  if s.isEmpty then throw "empty hexadecimal integer"
  s.toList.foldlM (fun n c => do
    let v ← if '0' ≤ c && c ≤ '9' then pure (c.toNat - 48)
      else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 87)
      else if 'A' ≤ c && c ≤ 'F' then pure (c.toNat - 55)
      else throw "invalid hexadecimal digit"
    pure (16*n + v)) 0

def bytes (s : String) : Except String (List UInt8) := do
  let cs := s.toList
  if cs.length % 2 != 0 then throw "odd hexadecimal byte string"
  (List.range (cs.length / 2)).mapM fun i => do
    return UInt8.ofNat (← parseHex (String.ofList ((cs.drop (2*i)).take 2)))

def fieldHex (j : Json) (key : String) : Except String Nat := do
  parseHex (← (← j.getObjVal? key).getStr?)

def bank (j : Json) (key : String) (digits : Nat) : Except String (Array Nat) := do
  let a ← (← j.getObjVal? key).getArr?
  if a.size != 16 then throw s!"{key}: expected 16 registers"
  a.mapM fun v => do
    let s ← v.getStr?
    if s.length != digits then throw s!"{key}: wrong register width"
    parseHex s

def run (fuel : Nat) (prog : List (DecodedInstr X86Instr)) (endPc : Nat)
    (st : X86State) : Except String (X86State × Nat) :=
  if st.halted || st.pc == endPc then pure (st, 0)
  else match fuel with
  | 0 => .error "instruction fuel exhausted"
  | n+1 => do
    let d ← requireSome "PC outside decoded instructions" (findInstrAtPc st.pc prog)
    match d.instr with
    | .ret => throw "RET is a function boundary in this model; exact return state is not modeled"
    | .divRem _ | .indirectBr _ | .varShiftCl _ _ | .vpgather _ _ =>
      throw "instruction is classified but lacks executable semantics"
    | _ => pure ()
    let (out, count) ← run n prog endPc (stepX86 d st).1
    pure (out, count + 1)

def evaluate (j : Json) : Except String Json := do
  let code ← bytes (← (← j.getObjVal? "insn_bytes_or_kernel").getStr?)
  let prog ← requireSome "unsupported or invalid instruction bytes" (decodeX86Stream code)
  let gs ← bank j "initial_gprs" 16
  let ys ← bank j "initial_ymms" 64
  let flags ← fieldHex j "initial_rflags"
  let base ← fieldHex j "stack_base"
  let mem ← bytes (← (← j.getObjVal? "stack_mem").getStr?)
  let st : X86State := {
    pc := 0, gpr := Bank16.ofFn (fun i => UInt64.ofNat gs[i]!)
    ymm := Bank16.ofFn (fun i =>
      let n := ys[i]!
      ⟨UInt64.ofNat n, UInt64.ofNat (n >>> 64), UInt64.ofNat (n >>> 128), UInt64.ofNat (n >>> 192)⟩)
    cf := flags &&& 1 != 0, ofFlag := flags &&& 2048 != 0, zf := flags &&& 64 != 0
    ymmDirty := false, halted := false
    mem := fun a => if base ≤ a.toNat && a.toNat < base + mem.length then
      mem.getD (a.toNat - base) 0 else 0 }
  let (out, steps) ← run 100000 prog code.length st
  let f := (flags &&& (0xffffffffffffffff - 0x841)) |||
    (if out.cf then 1 else 0) ||| (if out.zf then 64 else 0) ||| (if out.ofFlag then 2048 else 0)
  return Json.mkObj [
    ("steps", toJson steps),
    ("gprs", toJson ((List.range 16).map fun i => hexNat 16 (out.gpr.get i).toNat)),
    ("ymms", toJson ((List.range 16).map fun i =>
      let v := out.ymm.get i
      hexNat 16 v.w3.toNat ++ hexNat 16 v.w2.toNat ++ hexNat 16 v.w1.toNat ++ hexNat 16 v.w0.toNat)),
    ("rflags", toJson (hexNat 16 f)),
    ("modeled_rflags_mask", toJson (hexNat 16 0x841)),
    ("stack_mem", toJson (String.join ((List.range mem.length).map fun i =>
      hexNat 2 (out.mem (UInt64.ofNat (base+i))).toNat)))]

end IsaCosim

def main (args : List String) : IO UInt32 := do
  if let ["--elf", path] := args then
    let data ← IO.FS.readBinFile path
    let source : Bytes := ⟨data.size, fun i => data[i]!⟩
    match extractExecutableElfFuncs source with
    | none => throw (IO.userError "invalid or unsupported ELF image")
    | some fs =>
      for f in fs do
        let decoded := if f.machine == elfMachineX86_64 then (decodeX86Stream f.code).isSome
          else if f.machine == elfMachineAArch64 then (decodeArm64Stream f.code).isSome else false
        IO.println ((Json.mkObj [("symbol", toJson f.name), ("bytes", toJson f.symSize),
          ("decoded", toJson decoded)]).compress)
      return 0
  let input ← match args with
    | [] => IO.getStdin
    | [path] => do pure (IO.FS.Stream.ofHandle (← IO.FS.Handle.mk path .read))
    | _ => throw (IO.userError "usage: isa-cosim [json-lines-file]")
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let result := Json.parse line >>= IsaCosim.evaluate
    let reply := match result with
      | .ok j => j
      | .error e => Json.mkObj [("error", toJson e)]
    output.putStrLn reply.compress
    output.flush
  return 0
