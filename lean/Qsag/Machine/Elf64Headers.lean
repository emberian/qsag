module
public import Qsag.Machine.ArParse
import Qsag.Tactic.AssuranceKit
public section
namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
  UInt64.instLawfulOrderOrd Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe
set_option autoImplicit false
set_option maxRecDepth 65536
/-! ## §3. `ELF64` header, section & symbol parser + subslice soundness -/

/-- Parsed 64-byte `Elf64_Ehdr` for little-endian relocatable `.o` objects. -/
structure Elf64Ehdr where
  machine : Nat
  shoff : Nat
  ehsize : Nat
  shentsize : Nat
  shnum : Nat
  shstrndx : Nat
  deriving DecidableEq, Repr

/-- Parsed 64-byte `Elf64_Shdr` section table entry. -/
structure Elf64Shdr where
  shName : Nat
  shType : Nat
  shFlags : Nat
  shOffset : Nat
  shSize : Nat
  shLink : Nat
  shEntsize : Nat
  deriving DecidableEq, Repr

/-- Parsed 24-byte `Elf64_Sym` symbol table entry. -/
structure Elf64Sym where
  stName : Nat
  stInfo : UInt8
  stShndx : Nat
  stValue : Nat
  stSize : Nat
  deriving DecidableEq, Repr

@[expose] def elfMachineX86_64 : Nat := 62
@[expose] def elfMachineAArch64 : Nat := 183

/-- Bounds-checked byte read; out-of-range reads return `0`. -/
@[expose] def readByteD (bs : Bytes) (off : Nat) : UInt8 :=
  if off < bs.len then bs.get off else 0

@[expose] def readU16LE (bs : Bytes) (off : Nat) : Nat :=
  (readByteD bs off).toNat + 256 * (readByteD bs (off + 1)).toNat

@[expose] def readU32LE (bs : Bytes) (off : Nat) : Nat :=
  (readByteD bs off).toNat +
  256 * (readByteD bs (off + 1)).toNat +
  65536 * (readByteD bs (off + 2)).toNat +
  16777216 * (readByteD bs (off + 3)).toNat

@[expose] def readU64LE (bs : Bytes) (off : Nat) : Nat :=
  readU32LE bs off + 4294967296 * readU32LE bs (off + 4)

/-- NUL-terminated name at offset `off` of the string table `[tabOff, tabOff + tabSize)`. -/
@[expose] def readCStrBytes (elf : Bytes) (tabOff tabSize off : Nat) : List UInt8 :=
  takeUntilByte 0x00 (elf.slice (tabOff + off) (tabSize - off))

/-- Parse and validate a 64-byte `Elf64_Ehdr` (`\x7fELF`, `ELFCLASS64`, `ELFDATA2LSB`, `ET_REL`). -/
@[expose] def parseElf64Ehdr (elf : Bytes) : Option Elf64Ehdr :=
  let total := elf.len
  if total < 64 then none
  else if elf.slice 0 4 != elfMagicBytes then none
  else if readByteD elf 4 != 2 || readByteD elf 5 != 1 then none
  else
    let eType := readU16LE elf 16
    let eMachine := readU16LE elf 18
    let eShoff := readU64LE elf 40
    let eEhsize := readU16LE elf 52
    let eShentsize := readU16LE elf 58
    let eShnum := readU16LE elf 60
    let eShstrndx := readU16LE elf 62
    if eType == 1 && eEhsize == 64 && eShentsize == 64 && eShnum > 0 &&
       eShstrndx < eShnum && eShoff + eShnum * 64 ≤ total then
      some {
        machine := eMachine
        shoff := eShoff
        ehsize := eEhsize
        shentsize := eShentsize
        shnum := eShnum
        shstrndx := eShstrndx
      }
    else none

@[expose] def parseShdrLoop (elf : Bytes) : Nat → Nat → List Elf64Shdr
  | 0, _ => []
  | n + 1, off =>
    let sh : Elf64Shdr := {
      shName := readU32LE elf off
      shType := readU32LE elf (off + 4)
      shFlags := readU64LE elf (off + 8)
      shOffset := readU64LE elf (off + 24)
      shSize := readU64LE elf (off + 32)
      shLink := readU32LE elf (off + 40)
      shEntsize := readU64LE elf (off + 56)
    }
    sh :: parseShdrLoop elf n (off + 64)

@[expose] def parseSymLoop (elf : Bytes) : Nat → Nat → List Elf64Sym
  | 0, _ => []
  | n + 1, off =>
    let sym : Elf64Sym := {
      stName := readU32LE elf off
      stInfo := readByteD elf (off + 4)
      stShndx := readU16LE elf (off + 6)
      stValue := readU64LE elf (off + 8)
      stSize := readU64LE elf (off + 16)
    }
    sym :: parseSymLoop elf n (off + 24)

/-- ASCII `.text`. -/
@[expose] def dotTextBytes : List UInt8 := [0x2e, 0x74, 0x65, 0x78, 0x74]


end Qsag
