module
public import Qsag.Machine.Elf64Headers
import Qsag.Tactic.AssuranceKit
public section
namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
  UInt64.instLawfulOrderOrd Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe
set_option autoImplicit false
set_option maxRecDepth 65536
@[expose] def findTextSection (elf : Bytes) (shstrSh : Elf64Shdr) : Nat → List Elf64Shdr → Option (Nat × Elf64Shdr)
  | _, [] => none
  | idx, sh :: rest =>
    if sh.shType == 1 &&
        readCStrBytes elf shstrSh.shOffset shstrSh.shSize sh.shName == dotTextBytes then
      some (idx, sh)
    else
      findTextSection elf shstrSh (idx + 1) rest

@[expose] def findSymtabSection : List Elf64Shdr → Option Elf64Shdr
  | [] => none
  | sh :: rest => if sh.shType == 2 then some sh else findSymtabSection rest

@[expose] def stripLeadingUnderscoreBytes : List UInt8 → List UInt8
  | 0x5f :: rest => rest
  | bs => bs

@[expose] def buildFuncSlice (elf : Bytes) (strSh : Elf64Shdr)
    (machine textIdx : Nat) (textSh : Elf64Shdr) (sym : Elf64Sym) : Option ElfFuncSlice :=
  if (sym.stInfo >>> 4) ≥ 1 && (sym.stInfo &&& 0x0f) == 2 && sym.stShndx == textIdx then
    if 0 < sym.stSize ∧ sym.stValue + sym.stSize ≤ textSh.shSize ∧
        textSh.shOffset + textSh.shSize ≤ elf.len then
      let rawNm := stripLeadingUnderscoreBytes
        (readCStrBytes elf strSh.shOffset strSh.shSize sym.stName)
      some {
        name := bytesToAsciiString rawNm
        nameBytes := rawNm
        machine := machine
        textFileOffset := textSh.shOffset
        textSize := textSh.shSize
        symValue := sym.stValue
        symSize := sym.stSize
        code := elf.slice (textSh.shOffset + sym.stValue) sym.stSize
      }
    else none
  else none

/-- Parse all global `STT_FUNC` `.text` symbols from an `ELF64` relocatable object. -/
@[expose] def extractAllElfFuncs (elf : Bytes) : Option (List ElfFuncSlice) :=
  match parseElf64Ehdr elf with
  | none => none
  | some eh =>
    let shdrs := parseShdrLoop elf eh.shnum eh.shoff
    match shdrs[eh.shstrndx]? with
    | none => none
    | some shstrSh =>
      if elf.len < shstrSh.shOffset + shstrSh.shSize then none
      else
        match findTextSection elf shstrSh 0 shdrs, findSymtabSection shdrs with
        | some (textIdx, textSh), some symSh =>
          if textSh.shOffset + textSh.shSize ≤ elf.len then
            match shdrs[symSh.shLink]? with
            | none => none
            | some strSh =>
              if symSh.shOffset + symSh.shSize ≤ elf.len ∧
                  strSh.shOffset + strSh.shSize ≤ elf.len then
                let syms := parseSymLoop elf (symSh.shSize / 24) symSh.shOffset
                some (List.filterMap (buildFuncSlice elf strSh eh.machine textIdx textSh) syms)
              else none
          else none
        | _, _ => none

/-- Extract a named `STT_FUNC` symbol's `.text` machine-code slice from an `ELF64` object. -/
@[expose] def extractElfFuncBytes (elf : Bytes) (symName : String) : Option ElfFuncSlice :=
  match extractAllElfFuncs elf with
  | none => none
  | some slices => slices.find? (fun s => s.name == symName)

/-- Locate all `ELF64` members inside a `GNU ar` `.rlib` archive and extract their `STT_FUNC` slices. -/
@[expose] def extractAllRlibFuncs (rlib : Bytes) : List ElfFuncSlice :=
  (parseArArchive rlib).foldl (fun acc m =>
    if m.payload.slice 0 4 == elfMagicBytes then
      match extractAllElfFuncs m.payload with
      | some fs => acc ++ fs
      | none => acc
    else acc) []

/-- Extract a named symbol's `ElfFuncSlice` directly from a compiled `.rlib`. -/
@[expose] def extractRlibFuncBytes (rlib : Bytes) (symName : String) : Option ElfFuncSlice :=
  (extractAllRlibFuncs rlib).find? (fun s => s.name == symName)


end Qsag
