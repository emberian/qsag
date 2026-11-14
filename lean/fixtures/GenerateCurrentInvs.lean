module
import all Qsag.ElfBinaryVerify
import all Qsag.ElfFixtureSlices
open Qsag
set_option maxRecDepth 65536
def bank16Lit {α : Type} (f : α → String) (b : Bank16 α) : String :=
  "⟨" ++ String.intercalate ", " ((List.range 16).map fun i => f (b.get i)) ++ "⟩"
def bank32Lit {α : Type} (f : α → String) (b : Bank32 α) : String :=
  "⟨" ++ bank16Lit f b.lo ++ ", " ++ bank16Lit f b.hi ++ "⟩"
def optLit {α : Type} (f : α → String) : Option α → String
  | none => "none"
  | some x => "some (" ++ f x ++ ")"
def mapLit {α : Type} [Repr α] (m : PcMap α) : String :=
  "⟨" ++ bank32Lit (optLit (bank16Lit (optLit (bank16Lit (optLit (fun x => (reprStr x).replace "\n" " ")))))) m.root ++ "⟩"
public def main (args : List String) : IO Unit := do
  let mut result := ""
  for (sl, c) in currentX86ExtractedSlices.zip currentX86SymbolContracts do
    let some prog := decodeX86Stream sl.code | throw (IO.userError s!"decode {sl.name}")
    let some inv := inferX86Invariant prog c | throw (IO.userError s!"infer {sl.name}")
    unless verifyX86Invariant prog c inv do throw (IO.userError s!"verify {sl.name}")
    IO.println s!"x86 {sl.name}: {prog.length} instructions: accepted"
    result := result ++ s!"def {sl.name}_currentInv : PcMap X86AbsState :=\n{mapLit inv}\n\n"
  for (sl, c) in currentAarch64ExtractedSlices.zip currentAarch64SymbolContracts do
    let some prog := decodeArm64Stream sl.code | throw (IO.userError s!"decode {sl.name}")
    let some inv := inferArm64Invariant prog c | throw (IO.userError s!"infer {sl.name}")
    unless verifyArm64Invariant prog c inv do throw (IO.userError s!"verify {sl.name}")
    IO.println s!"arm {sl.name}: {prog.length} instructions: accepted"
    result := result ++ s!"def {sl.name}_currentInv : PcMap Arm64AbsState :=\n{mapLit inv}\n\n"
  IO.FS.writeFile (args.headD "fixtures/current-invariants.inc") result

