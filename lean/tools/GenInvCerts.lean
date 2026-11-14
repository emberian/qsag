/- Untrusted invariant-certificate proposer. Runs the fixpoint inference outside the kernel and
prints one line per compiled symbol; `generate_inv_certs.py` turns the output into
`Qsag/ElfInvCerts.lean`. The kernel only ever checks the printed invariants. -/
import Qsag.ElfBinaryVerify
open Qsag
set_option maxRecDepth 100000

def x86CertLine (s : ElfFuncSlice) (c : FuncContract) : String :=
  match decodeX86Stream s.code with
  | some p =>
    match inferX86Invariant p c with
    | some inv => (repr inv.root).pretty 1000000000
    | none => "FAIL"
  | none => "FAIL"

def armCertLine (s : ElfFuncSlice) (c : FuncContract) : String :=
  match decodeArm64Stream s.code with
  | some p =>
    match inferArm64Invariant p c with
    | some inv => (repr inv.root).pretty 1000000000
    | none => "FAIL"
  | none => "FAIL"

#eval do
  for (s, c) in x86ExtractedSlices.zip x86SymbolContracts do
    IO.println s!"CERT x86 {s.name} {x86CertLine s c}"
  for (s, c) in aarch64ExtractedSlices.zip aarch64SymbolContracts do
    IO.println s!"CERT aarch64 {s.name} {armCertLine s c}"
