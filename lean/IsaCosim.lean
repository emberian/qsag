module
public import Lean
public import Qsag.Machine.IsaCosim
public section
open Lean Qsag

/-! JSON transport for the pure, audited `Qsag.IsaCosim` execution layer. -/
namespace IsaCosim

def fieldHex (j : Json) (key : String) : Except String Nat := do
  parseHex (← (← j.getObjVal? key).getStr?)

def bank (j : Json) (key : String) (digits : Nat) : Except String (Array Nat) := do
  let a ← (← j.getObjVal? key).getArr?
  if a.size != 16 then throw s!"{key}: expected 16 registers"
  a.mapM fun v => do
    let s ← v.getStr?
    if s.length != digits then throw s!"{key}: wrong register width"
    parseHex s

def evaluate (j : Json) : Except String Json := do
  let code ← bytes (← (← j.getObjVal? "insn_bytes_or_kernel").getStr?)
  let gs ← bank j "initial_gprs" 16
  let ys ← bank j "initial_ymms" 64
  let flags ← fieldHex j "initial_rflags"
  let base ← fieldHex j "stack_base"
  let mem := (← bytes (← (← j.getObjVal? "stack_mem").getStr?)).toArray
  let st : X86State := {
    pc := 0, gpr := Bank16.ofFn (fun i => UInt64.ofNat gs[i]!)
    ymm := Bank16.ofFn (fun i =>
      let n := ys[i]!
      ⟨UInt64.ofNat n, UInt64.ofNat (n >>> 64), UInt64.ofNat (n >>> 128), UInt64.ofNat (n >>> 192)⟩)
    cf := flags &&& 1 != 0, ofFlag := flags &&& 2048 != 0, zf := flags &&& 64 != 0
    ymmDirty := false, halted := false
    mem := fun a => if base ≤ a.toNat && a.toNat < base + mem.size then
      mem.getD (a.toNat - base) 0 else 0 }
  let (out, finalFlags, pcs) ← run 100000 code st { value := flags }
  let f := finalFlags.value
  return Json.mkObj [
    ("steps", toJson pcs.length),
    ("final_pc", toJson (hexNat 16 out.pc)),
    ("pc_trace", toJson (pcs.map (hexNat 16))),
    ("gprs", toJson ((List.range 16).map fun i => hexNat 16 (out.gpr.get i).toNat)),
    ("ymms", toJson ((List.range 16).map fun i =>
      let v := out.ymm.get i
      hexNat 16 v.w3.toNat ++ hexNat 16 v.w2.toNat ++ hexNat 16 v.w1.toNat ++ hexNat 16 v.w0.toNat)),
    ("rflags", toJson (hexNat 16 f)),
    ("modeled_rflags_mask", toJson (hexNat 16 finalFlags.valid)),
    ("stack_mem", toJson (String.join ((List.range mem.size).map fun i =>
      hexNat 2 (out.mem (UInt64.ofNat (base+i))).toNat)))]

end IsaCosim

def main (args : List String) : IO UInt32 := do
  if args == ["--self-test"] then
    for v in IsaCosim.edgeCaseVectors do
      if !IsaCosim.checkEdgeVector v then
        throw (IO.userError s!"edge-case vector failed: {v.name}")
    IO.println s!"isa-cosim self-test ok ({IsaCosim.edgeCaseVectors.length} RFLAGS edge vectors)"
    return 0
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
