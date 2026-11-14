module
/-
# Qsag.ElfParse — indexed-reader `GNU ar` + `ELF64` parser and fixture extraction certificates

The parser reads its input through `Bytes`, a length plus an index function, so that a parse touches
only the header, section-table, symbol-table, name and code bytes it needs. The compiled archives in
`Qsag.CompiledRlibFixtures` are single natural-number literals; reading byte `i` is one shift.

Contents:
1. `Bytes` and its list views (`toList`, `slice`), with `ofList` round-trip lemmas.
2. `GNU ar` envelope validation and member parsing (`parseArArchive`, `parseArMember_subslice`).
3. `ELF64` header, section and symbol parsing (`extractAllElfFuncs`,
   `extractElfFuncBytes_in_text_section`), and archive-level provenance
   (`extractAllRlibFuncs_provenance`).
4. Extraction certificates: the parser applied to both compiled archives returns exactly the
   normalized slices of `Qsag.ElfFixtureSlices`.
-/

public import Qsag.CompiledRlibFixtures
public import Qsag.ElfFixtureSlices

public section
namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd

set_option autoImplicit false
set_option maxRecDepth 65536

/-! ## §0. Tail-recursive list helpers (shared with the instruction decoders) -/

/-- Tail-recursive list length (`O(1)` WHNF stack depth on multi-kilobyte binary streams). -/
def lenTRLoop : List UInt8 → Nat → Nat
  | [], acc => acc
  | _ :: xs, acc => lenTRLoop xs (acc + 1)

def lenTR (xs : List UInt8) : Nat :=
  lenTRLoop xs 0

private theorem lenTRLoop_eq : ∀ (xs : List UInt8) (acc : Nat),
    lenTRLoop xs acc = acc + xs.length
  | [], acc => by simp [lenTRLoop]
  | _ :: xs, acc => by
    simp only [lenTRLoop, lenTRLoop_eq xs (acc + 1), List.length_cons]
    omega

theorem lenTR_eq (xs : List UInt8) : lenTR xs = xs.length := by
  simpa [lenTR] using lenTRLoop_eq xs 0

/-- Tail-recursive prefix slice (`O(1)` WHNF stack depth on multi-kilobyte `.text` sections). -/
def takeTRLoop : Nat → List UInt8 → List UInt8 → List UInt8
  | 0, _, acc => acc.reverse
  | _ + 1, [], acc => acc.reverse
  | n + 1, x :: xs, acc => takeTRLoop n xs (x :: acc)

def takeTR (n : Nat) (xs : List UInt8) : List UInt8 :=
  takeTRLoop n xs []

private theorem takeTRLoop_eq : ∀ (n : Nat) (xs acc : List UInt8),
    takeTRLoop n xs acc = acc.reverse ++ xs.take n
  | 0, _, acc => by simp [takeTRLoop]
  | _ + 1, [], acc => by simp [takeTRLoop]
  | n + 1, x :: xs, acc => by
    simp [takeTRLoop, takeTRLoop_eq n xs (x :: acc), List.append_assoc]

theorem takeTR_eq (n : Nat) (xs : List UInt8) : takeTR n xs = xs.take n := by
  simpa [takeTR] using takeTRLoop_eq n xs []

/-! ## §1. Indexed byte source -/

/-- A byte string presented as its length and an index function. Reads at `i ≥ len` are
    unspecified; every parser read below is bounds-checked first. -/
structure Bytes where
  len : Nat
  get : Nat → UInt8

namespace Bytes

/-- Little-endian natural number as bytes: byte `i` is `(n >>> (8 * i)) % 256`. -/
def ofNat (len n : Nat) : Bytes :=
  ⟨len, fun i => UInt8.ofNat (n >>> (8 * i))⟩

def ofList (l : List UInt8) : Bytes :=
  ⟨l.length, fun i => l.getD i 0⟩

def drop (k : Nat) (b : Bytes) : Bytes :=
  ⟨b.len - k, fun i => b.get (k + i)⟩

def take (n : Nat) (b : Bytes) : Bytes :=
  ⟨if n ≤ b.len then n else b.len, b.get⟩

/-- `n` consecutive bytes starting at index `i`, produced front to back. -/
def listFrom (get : Nat → UInt8) : Nat → Nat → List UInt8
  | 0, _ => []
  | n + 1, i => get i :: listFrom get n (i + 1)

def toList (b : Bytes) : List UInt8 :=
  listFrom b.get b.len 0

/-- The `n` bytes at `[off, off + n)`. -/
def slice (b : Bytes) (off n : Nat) : List UInt8 :=
  listFrom b.get n off

theorem listFrom_length (get : Nat → UInt8) : ∀ (n i : Nat), (listFrom get n i).length = n
  | 0, _ => rfl
  | n + 1, i => by simp only [listFrom, List.length_cons, listFrom_length get n (i + 1)]

theorem listFrom_congr {g h : Nat → UInt8} : ∀ (n i : Nat),
    (∀ j, i ≤ j → j < i + n → g j = h j) → listFrom g n i = listFrom h n i
  | 0, _, _ => rfl
  | n + 1, i, hEq => by
    simp only [listFrom]
    rw [hEq i (Nat.le_refl i) (by omega),
      listFrom_congr n (i + 1) (fun j h1 h2 => hEq j (by omega) (by omega))]

theorem slice_length (b : Bytes) (off n : Nat) : (b.slice off n).length = n :=
  listFrom_length b.get n off

private theorem listFrom_ofList : ∀ (l : List UInt8) (n i : Nat), i + n ≤ l.length →
    listFrom (fun j => l.getD j 0) n i = (l.drop i).take n
  | _, 0, _, _ => by simp [listFrom]
  | l, n + 1, i, h => by
    have hi : i < l.length := by omega
    have hd : l.drop i = l[i] :: l.drop (i + 1) := List.drop_eq_getElem_cons hi
    simp only [listFrom]
    rw [hd, List.take_succ_cons, listFrom_ofList l n (i + 1) (by omega)]
    congr 1
    simp [List.getD, List.getElem?_eq_getElem hi]

/-- The list view of `ofList` is the original list. -/
theorem toList_ofList (l : List UInt8) : (ofList l).toList = l := by
  have h := listFrom_ofList l l.length 0 (by omega)
  simpa [toList, ofList] using h

/-- On a list-backed source, `slice` is `drop` then `take`. -/
theorem slice_ofList (l : List UInt8) (off n : Nat) (h : off + n ≤ l.length) :
    (ofList l).slice off n = (l.drop off).take n :=
  listFrom_ofList l n off h

end Bytes

/-! ## §2. `GNU ar` (`.rlib`) parser & subslice soundness -/

/-- Parsed member of a `GNU ar` (`.rlib`) archive with exact byte-offset provenance. -/
structure ArMember where
  name : String
  payloadOffset : Nat
  payloadSize : Nat
  payload : Bytes

def arMagicBytes : List UInt8 :=
  [0x21, 0x3c, 0x61, 0x72, 0x63, 0x68, 0x3e, 0x0a]

def elfMagicBytes : List UInt8 :=
  [0x7f, 0x45, 0x4c, 0x46]

def parseAsciiDecLoop : List UInt8 → Nat → Bool → Option Nat
  | [], acc, seen => if seen then some acc else none
  | b :: bs, acc, seen =>
    if b == 0x20 then
      if seen then
        if bs.all (· == 0x20) then some acc else none
      else
        parseAsciiDecLoop bs acc false
    else if 0x30 ≤ b && b ≤ 0x39 then
      parseAsciiDecLoop bs (acc * 10 + (b.toNat - 48)) true
    else
      none

def parseAsciiDec (bs : List UInt8) : Option Nat :=
  parseAsciiDecLoop bs 0 false

def bytesToAsciiString (bs : List UInt8) : String :=
  String.ofList (bs.map (fun b => Char.ofNat b.toNat))

def takeUntilByte (stop : UInt8) : List UInt8 → List UInt8
  | [] => []
  | b :: bs => if b == stop then [] else b :: takeUntilByte stop bs

def rstripSpaces (bs : List UInt8) : List UInt8 :=
  (bs.reverse.dropWhile (· == 0x20)).reverse

def rstripSlash (bs : List UInt8) : List UInt8 :=
  match bs.reverse with
  | 0x2f :: rest => rest.reverse
  | _ => bs

def resolveArMemberName (rawField : List UInt8) (extNames : List UInt8) : String :=
  let trimmed := rstripSpaces rawField
  match trimmed with
  | 0x2f :: rest =>
    match rest with
    | [] => "/"
    | 0x2f :: _ => "//"
    | _ =>
      match parseAsciiDec rest with
      | some off =>
        let slice := takeUntilByte 0x0a (extNames.drop off)
        bytesToAsciiString (rstripSlash slice)
      | none => bytesToAsciiString (rstripSlash trimmed)
  | _ => bytesToAsciiString (rstripSlash trimmed)

/-- Walk member headers from byte offset `pos`. The GNU `//` extended-name member is consumed as
    the name table for later members; every other member is recorded with its payload window. -/
def parseArLoop (bytes : Bytes) : Nat → Nat → List UInt8 → List ArMember → List ArMember
  | 0, _, _, acc => acc.reverse
  | fuel + 1, pos, extNames, acc =>
    if pos + 60 ≤ bytes.len then
      let hdr := bytes.slice pos 60
      if hdr.drop 58 == [0x60, 0x0a] then
        match parseAsciiDec (takeTR 10 (hdr.drop 48)) with
        | none => acc.reverse
        | some sz =>
          if pos + 60 + sz ≤ bytes.len then
            let payload : Bytes := (bytes.drop (pos + 60)).take sz
            let rawName := takeTR 16 hdr
            let nextPos := pos + (60 + sz + (sz % 2))
            if rstripSpaces rawName == [0x2f, 0x2f] then
              parseArLoop bytes fuel nextPos payload.toList acc
            else
              let m : ArMember := {
                name := resolveArMemberName rawName extNames
                payloadOffset := pos + 60
                payloadSize := sz
                payload := payload
              }
              parseArLoop bytes fuel nextPos extNames (m :: acc)
          else acc.reverse
      else acc.reverse
    else acc.reverse

/-- Validate the entire archive envelope before exposing any parsed prefix.
Odd payloads require their alignment byte; truncated headers and trailing junk fail closed. -/
def validArEnvelope (bytes : Bytes) : Nat → Nat → Bool
  | 0, pos => decide (bytes.len ≤ pos)
  | fuel + 1, pos =>
    if bytes.len ≤ pos then true
    else if bytes.len < pos + 60 then false
    else
      let hdr := bytes.slice pos 60
      if hdr.drop 58 != [0x60, 0x0a] then false
      else match parseAsciiDec (takeTR 10 (hdr.drop 48)) with
      | none => false
      | some sz =>
        let step := 60 + sz + sz % 2
        if sz % 2 == 1 && !(decide (pos + 60 + sz < bytes.len) && bytes.get (pos + 60 + sz) == 0x0a) then false
        else if pos + step ≤ bytes.len then validArEnvelope bytes fuel (pos + step) else false

/-- Parse a `GNU ar` (`.rlib`) archive into its non-`//` member windows. -/
def parseArArchive (rlib : Bytes) : List ArMember :=
  if decide (8 ≤ rlib.len) && rlib.slice 0 8 == arMagicBytes && validArEnvelope rlib rlib.len 8 then
    parseArLoop rlib rlib.len 8 [] []
  else
    []

/-- A member's payload is exactly the window `[payloadOffset, payloadOffset + payloadSize)` of
    the archive. -/
def ArPayloadOk (bytes : Bytes) (m : ArMember) : Prop :=
  m.payload.len = m.payloadSize ∧
  m.payloadOffset + m.payloadSize ≤ bytes.len ∧
  ∀ i, m.payload.get i = bytes.get (m.payloadOffset + i)

private theorem parseArLoop_subslice (bytes : Bytes) :
    ∀ (fuel pos : Nat) (extNames : List UInt8) (acc : List ArMember),
      (∀ m ∈ acc, ArPayloadOk bytes m) →
      ∀ m ∈ parseArLoop bytes fuel pos extNames acc, ArPayloadOk bytes m
  | 0, _, _, acc, hAcc, m, hm => by
    simp only [parseArLoop, List.mem_reverse] at hm
    exact hAcc m hm
  | fuel + 1, pos, extNames, acc, hAcc, m, hm => by
    unfold parseArLoop at hm
    dsimp only at hm
    split at hm
    · split at hm
      · split at hm
        · simp only [List.mem_reverse] at hm
          exact hAcc m hm
        · rename_i sz _
          split at hm
          · rename_i hFit
            split at hm
            · exact parseArLoop_subslice bytes fuel _ _ acc hAcc m hm
            · refine parseArLoop_subslice bytes fuel _ _ _ ?_ m hm
              intro x hx
              simp only [List.mem_cons] at hx
              rcases hx with rfl | hxAcc
              · refine ⟨?_, hFit, fun _ => rfl⟩
                show (if sz ≤ bytes.len - (pos + 60) then sz else bytes.len - (pos + 60)) = sz
                have hle : sz ≤ bytes.len - (pos + 60) := by omega
                exact ite_eq_left hle
              · exact hAcc x hxAcc
          · simp only [List.mem_reverse] at hm
            exact hAcc m hm
      · simp only [List.mem_reverse] at hm
        exact hAcc m hm
    · simp only [List.mem_reverse] at hm
      exact hAcc m hm

/-- **`parseArMember_subslice`**: every member returned by `parseArArchive` is an in-bounds,
    exact-length window of the archive. -/
theorem parseArMember_subslice (rlib : Bytes) (m : ArMember)
    (hm : m ∈ parseArArchive rlib) : ArPayloadOk rlib m := by
  unfold parseArArchive at hm
  split at hm
  · exact parseArLoop_subslice rlib rlib.len 8 [] [] (fun _ h => nomatch h) m hm
  · exact nomatch hm

def oneByteArHeader : List UInt8 :=
  [0x61] ++ List.replicate 47 0x20 ++ [0x31] ++ List.replicate 9 0x20 ++ [0x60, 0x0a]

/-- A well-formed member remains accepted. -/
theorem ar_one_member_supported :
    (parseArArchive (Bytes.ofList (arMagicBytes ++ oneByteArHeader ++ [0x42, 0x0a]))).length = 1 := by
  decide +kernel

/-- A valid prefix never masks trailing malformed data. -/
theorem ar_trailing_junk_rejected :
    (parseArArchive (Bytes.ofList (arMagicBytes ++ oneByteArHeader ++ [0x42, 0x0a, 0]))).length = 0 := by
  decide +kernel

theorem ar_missing_alignment_rejected :
    (parseArArchive (Bytes.ofList (arMagicBytes ++ oneByteArHeader ++ [0x42]))).length = 0 := by
  decide +kernel

theorem ar_invalid_alignment_rejected :
    (parseArArchive (Bytes.ofList (arMagicBytes ++ oneByteArHeader ++ [0x42, 0]))).length = 0 := by
  decide +kernel

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

def elfMachineX86_64 : Nat := 62
def elfMachineAArch64 : Nat := 183

/-- Bounds-checked byte read; out-of-range reads return `0`. -/
def readByteD (bs : Bytes) (off : Nat) : UInt8 :=
  if off < bs.len then bs.get off else 0

def readU16LE (bs : Bytes) (off : Nat) : Nat :=
  (readByteD bs off).toNat + 256 * (readByteD bs (off + 1)).toNat

def readU32LE (bs : Bytes) (off : Nat) : Nat :=
  (readByteD bs off).toNat +
  256 * (readByteD bs (off + 1)).toNat +
  65536 * (readByteD bs (off + 2)).toNat +
  16777216 * (readByteD bs (off + 3)).toNat

def readU64LE (bs : Bytes) (off : Nat) : Nat :=
  readU32LE bs off + 4294967296 * readU32LE bs (off + 4)

/-- NUL-terminated name at offset `off` of the string table `[tabOff, tabOff + tabSize)`. -/
def readCStrBytes (elf : Bytes) (tabOff tabSize off : Nat) : List UInt8 :=
  takeUntilByte 0x00 (elf.slice (tabOff + off) (tabSize - off))

/-- Parse and validate a 64-byte `Elf64_Ehdr` (`\x7fELF`, `ELFCLASS64`, `ELFDATA2LSB`, `ET_REL`). -/
def parseElf64Ehdr (elf : Bytes) : Option Elf64Ehdr :=
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

def parseShdrLoop (elf : Bytes) : Nat → Nat → List Elf64Shdr
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

def parseSymLoop (elf : Bytes) : Nat → Nat → List Elf64Sym
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
def dotTextBytes : List UInt8 := [0x2e, 0x74, 0x65, 0x78, 0x74]

def findTextSection (elf : Bytes) (shstrSh : Elf64Shdr) : Nat → List Elf64Shdr → Option (Nat × Elf64Shdr)
  | _, [] => none
  | idx, sh :: rest =>
    if sh.shType == 1 &&
        readCStrBytes elf shstrSh.shOffset shstrSh.shSize sh.shName == dotTextBytes then
      some (idx, sh)
    else
      findTextSection elf shstrSh (idx + 1) rest

def findSymtabSection : List Elf64Shdr → Option Elf64Shdr
  | [] => none
  | sh :: rest => if sh.shType == 2 then some sh else findSymtabSection rest

def stripLeadingUnderscoreBytes : List UInt8 → List UInt8
  | 0x5f :: rest => rest
  | bs => bs

def buildFuncSlice (elf : Bytes) (strSh : Elf64Shdr)
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
def extractAllElfFuncs (elf : Bytes) : Option (List ElfFuncSlice) :=
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
def extractElfFuncBytes (elf : Bytes) (symName : String) : Option ElfFuncSlice :=
  match extractAllElfFuncs elf with
  | none => none
  | some slices => slices.find? (fun s => s.name == symName)

/-- Locate all `ELF64` members inside a `GNU ar` `.rlib` archive and extract their `STT_FUNC` slices. -/
def extractAllRlibFuncs (rlib : Bytes) : List ElfFuncSlice :=
  (parseArArchive rlib).foldl (fun acc m =>
    if m.payload.slice 0 4 == elfMagicBytes then
      match extractAllElfFuncs m.payload with
      | some fs => acc ++ fs
      | none => acc
    else acc) []

/-- Extract a named symbol's `ElfFuncSlice` directly from a compiled `.rlib`. -/
def extractRlibFuncBytes (rlib : Bytes) (symName : String) : Option ElfFuncSlice :=
  (extractAllRlibFuncs rlib).find? (fun s => s.name == symName)

/-- A slice has positive size, lies inside `.text`, `.text` lies inside the object, and its code
    is exactly the object's bytes at `[textFileOffset + symValue, … + symSize)`. -/
def ElfSliceOk (elf : Bytes) (slice : ElfFuncSlice) : Prop :=
  slice.symSize > 0 ∧
  slice.code.length = slice.symSize ∧
  slice.symValue + slice.symSize ≤ slice.textSize ∧
  slice.textFileOffset + slice.textSize ≤ elf.len ∧
  slice.code = elf.slice (slice.textFileOffset + slice.symValue) slice.symSize

private theorem buildFuncSlice_sound (elf : Bytes) (strSh : Elf64Shdr)
    (machine textIdx : Nat) (textSh : Elf64Shdr) (sym : Elf64Sym) (slice : ElfFuncSlice)
    (hBuild : buildFuncSlice elf strSh machine textIdx textSh sym = some slice) :
    ElfSliceOk elf slice := by
  unfold buildFuncSlice at hBuild
  split at hBuild
  · split at hBuild
    · rename_i hBounds
      injection hBuild with hEq
      subst hEq
      exact ⟨hBounds.1, Bytes.slice_length _ _ _, hBounds.2.1, hBounds.2.2, rfl⟩
    · cases hBuild
  · cases hBuild

theorem extractAllElfFuncs_sound (elf : Bytes) (slices : List ElfFuncSlice)
    (hAll : extractAllElfFuncs elf = some slices) (slice : ElfFuncSlice) (hMem : slice ∈ slices) :
    ElfSliceOk elf slice := by
  unfold extractAllElfFuncs at hAll
  split at hAll
  · cases hAll
  · rename_i eh _
    dsimp only at hAll
    split at hAll
    · cases hAll
    · rename_i shstrSh _
      split at hAll
      · cases hAll
      · split at hAll
        · rename_i textIdx textSh symSh _ _
          split at hAll
          · split at hAll
            · cases hAll
            · rename_i strSh _
              split at hAll
              · injection hAll with hSlices
                subst hSlices
                rcases List.mem_filterMap.mp hMem with ⟨sym, _, hBuild⟩
                exact buildFuncSlice_sound elf strSh eh.machine textIdx textSh sym slice hBuild
              · cases hAll
          · cases hAll
        · cases hAll

/-- **`extractElfFuncBytes_in_text_section`**: any function slice extracted from an `ELF64` object
    has positive size, lies within `.text`, and equals the object's bytes at
    `[textFileOffset + symValue, … + symSize)`. -/
theorem extractElfFuncBytes_in_text_section (elf : Bytes) (symName : String)
    (slice : ElfFuncSlice) (hExt : extractElfFuncBytes elf symName = some slice) :
    ElfSliceOk elf slice := by
  unfold extractElfFuncBytes at hExt
  cases hAll : extractAllElfFuncs elf with
  | none => rw [hAll] at hExt; cases hExt
  | some slices =>
    rw [hAll] at hExt
    exact extractAllElfFuncs_sound elf slices hAll slice (List.mem_of_find?_eq_some hExt)

private theorem foldl_extract_mem (step : List ElfFuncSlice → ArMember → List ElfFuncSlice)
    (P : ElfFuncSlice → Prop) :
    ∀ (ms : List ArMember) (acc : List ElfFuncSlice),
      (∀ s ∈ acc, P s) →
      (∀ m ∈ ms, ∀ a : List ElfFuncSlice, (∀ s ∈ a, P s) → ∀ s ∈ step a m, P s) →
      ∀ s ∈ ms.foldl step acc, P s
  | [], _, hAcc, _, s, hs => hAcc s hs
  | m :: ms, acc, hAcc, hStep, s, hs =>
    foldl_extract_mem step P ms (step acc m)
      (hStep m (List.mem_cons_self) acc hAcc)
      (fun m' hm' => hStep m' (List.mem_cons_of_mem _ hm')) s hs

/-- **Archive-level provenance.** Every slice returned for an archive lies in some member whose
    payload window is in bounds, and the slice's code is exactly the archive's bytes at
    `[payloadOffset + textFileOffset + symValue, … + symSize)`. -/
theorem extractAllRlibFuncs_provenance (rlib : Bytes) (slice : ElfFuncSlice)
    (hMem : slice ∈ extractAllRlibFuncs rlib) :
    ∃ m ∈ parseArArchive rlib,
      m.payloadOffset + m.payloadSize ≤ rlib.len ∧
      slice.symSize > 0 ∧
      slice.symValue + slice.symSize ≤ slice.textSize ∧
      slice.textFileOffset + slice.textSize ≤ m.payloadSize ∧
      slice.code =
        rlib.slice (m.payloadOffset + (slice.textFileOffset + slice.symValue)) slice.symSize := by
  unfold extractAllRlibFuncs at hMem
  refine foldl_extract_mem _ (fun slice => ∃ m ∈ parseArArchive rlib,
      m.payloadOffset + m.payloadSize ≤ rlib.len ∧
      slice.symSize > 0 ∧
      slice.symValue + slice.symSize ≤ slice.textSize ∧
      slice.textFileOffset + slice.textSize ≤ m.payloadSize ∧
      slice.code =
        rlib.slice (m.payloadOffset + (slice.textFileOffset + slice.symValue)) slice.symSize)
    (parseArArchive rlib) [] (fun _ h => nomatch h) ?_ slice hMem
  intro m hm a hA s hs
  split at hs
  · split at hs
    · rename_i fs hFs
      rcases List.mem_append.mp hs with h | h
      · exact hA s h
      · have hOk := extractAllElfFuncs_sound m.payload fs hFs s h
        have hPay := parseArMember_subslice rlib m hm
        refine ⟨m, hm, hPay.2.1, hOk.1, hOk.2.2.1, hPay.1 ▸ hOk.2.2.2.1, ?_⟩
        rw [hOk.2.2.2.2]
        unfold Bytes.slice
        have hShift : ∀ (n i : Nat),
            Bytes.listFrom m.payload.get n i = Bytes.listFrom rlib.get n (m.payloadOffset + i) := by
          intro n
          induction n with
          | zero => intro i; rfl
          | succ n ih =>
            intro i
            simp only [Bytes.listFrom]
            rw [hPay.2.2 i, ih (i + 1), Nat.add_assoc]
        exact hShift _ _
    · exact hA s hs
  · exact hA s hs

/-! ## §4. Extraction certificates for the compiled archives -/

/-- The compiled `x86_64` archive fixture as an indexed byte source. -/
@[expose] def x86RlibArchiveBytes : Bytes :=
  Bytes.ofNat x86RlibArchiveLen x86RlibArchiveNat

/-- The compiled `aarch64` archive fixture as an indexed byte source. -/
@[expose] def aarch64RlibArchiveBytes : Bytes :=
  Bytes.ofNat aarch64RlibArchiveLen aarch64RlibArchiveNat

/-- The archive literal has no bits beyond its stated byte length. -/
theorem x86_rlib_archive_nat_fits :
    x86RlibArchiveNat < 2 ^ (8 * x86RlibArchiveLen) := by decide +kernel

theorem aarch64_rlib_archive_nat_fits :
    aarch64RlibArchiveNat < 2 ^ (8 * aarch64RlibArchiveLen) := by decide +kernel

/-- Certified extraction boundary: the parser applied to the compiled `x86_64` archive returns
    exactly the normalized slices consumed by downstream proofs. -/
theorem x86_rlib_extracted_slices :
    extractAllRlibFuncs x86RlibArchiveBytes = x86ExtractedSlices := by
  rfl

theorem aarch64_rlib_extracted_slices :
    extractAllRlibFuncs aarch64RlibArchiveBytes = aarch64ExtractedSlices := by
  rfl

/-- `parseArArchive` + `extractAllElfFuncs` discover exactly the 16 exported `x86_64` symbols. -/
theorem x86_rlib_symbol_names_exact :
    (extractAllRlibFuncs x86RlibArchiveBytes).map ElfFuncSlice.name =
      x86ExportedSymbolNames := by
  rw [x86_rlib_extracted_slices]
  decide +kernel

/-- `parseArArchive` + `extractAllElfFuncs` discover exactly the 7 exported `aarch64` symbols. -/
theorem aarch64_rlib_symbol_names_exact :
    (extractAllRlibFuncs aarch64RlibArchiveBytes).map ElfFuncSlice.name =
      aarch64ExportedSymbolNames := by
  rw [aarch64_rlib_extracted_slices]
  decide +kernel

/-- Corrupting one byte of the archive literal inside a symbol body changes the extracted code:
    the certificate is sensitive to the code bytes, not only to the layout. -/
theorem x86_rlib_extraction_detects_code_flip :
    (extractAllRlibFuncs
        (Bytes.ofNat x86RlibArchiveLen (x86RlibArchiveNat ^^^ (1 <<< (8 * 400))))).map
        ElfFuncSlice.code ≠
      x86ExtractedSlices.map ElfFuncSlice.code := by
  decide +kernel

/-! ## Linked-image extraction

The ELF64 field layout and PT_LOAD terminology follow ELFSage's
`ELFSage/Types/ProgramHeaderTable.lean` (Draper Laboratory, MIT license,
https://github.com/shigoel/ELFSage). This independent indexed-reader
implementation checks file-backed executable ranges; it never treats BSS
or a virtual address as an offset into the file. The original fixture
extractor above intentionally retains its exact legacy symbol selection.
-/
structure Elf64ProgramHeader where
  kind : Nat
  flags : Nat
  offset : Nat
  vaddr : Nat
  filesz : Nat
  memsz : Nat
  deriving DecidableEq, Repr

def parseProgramHeaders (elf : Bytes) : Option (List Elf64ProgramHeader) := do
  if elf.len < 64 then none else do
    let off := readU64LE elf 32
    let size := readU16LE elf 54
    let count := readU16LE elf 56
    if count == 0 then pure [] else do
      if size != 56 || off + count * size > elf.len then none else
        pure ((List.range count).map fun i =>
          let p := off + i * size
          ⟨readU32LE elf p, readU32LE elf (p+4), readU64LE elf (p+8),
           readU64LE elf (p+16), readU64LE elf (p+32), readU64LE elf (p+40)⟩)

/-- Translate only file-backed bytes in an executable PT_LOAD segment. -/
def executableFileOffset (elf : Bytes) (ph : Elf64ProgramHeader)
    (va size : Nat) : Option Nat :=
  if ph.kind == 1 && (ph.flags &&& 1) == 1 && ph.filesz ≤ ph.memsz &&
      ph.offset + ph.filesz ≤ elf.len && ph.vaddr ≤ va &&
      va - ph.vaddr + size ≤ ph.filesz then
    some (ph.offset + (va - ph.vaddr))
  else none

def buildImageFuncSlice (elf : Bytes) (eh : Elf64Ehdr) (strSh : Elf64Shdr)
    (shdrs : List Elf64Shdr) (phdrs : List Elf64ProgramHeader)
    (sym : Elf64Sym) : Option ElfFuncSlice := do
  if sym.stShndx == 0 || sym.stShndx ≥ 0xff00 then none else do
    let sh ← shdrs[sym.stShndx]?
    if sh.shType != 1 || (sh.shFlags &&& 4) == 0 then none else do
      let linked := readU16LE elf 16 != 1
      let addr := readU64LE elf (eh.shoff + sym.stShndx * 64 + 16)
      if linked && sym.stValue < addr then none else do
        let relative := if linked then sym.stValue - addr else sym.stValue
        if linked && !(phdrs.any fun ph =>
            executableFileOffset elf ph sym.stValue sym.stSize == some (sh.shOffset + relative)) then
          none
        else buildFuncSlice elf strSh eh.machine sym.stShndx sh { sym with stValue := relative }

/-- All executable sections of ET_REL, ET_EXEC and ET_DYN images. Linked
symbols must agree with both section and executable PT_LOAD translations.
Unlike the legacy fixture API, this includes `.text.*` sections. -/
def extractExecutableElfFuncs (elf : Bytes) : Option (List ElfFuncSlice) := do
  let kind := readU16LE elf 16
  if kind != 1 && kind != 2 && kind != 3 then none else do
    -- Reuse the fully bounds-checked section header parser without weakening
    -- the legacy ET_REL entry point or its exact extraction certificates.
    let normalized : Bytes := ⟨elf.len, fun i => if i == 16 then 1 else if i == 17 then 0 else elf.get i⟩
    let eh ← parseElf64Ehdr normalized
    let ph ← parseProgramHeaders elf
    let sh := parseShdrLoop elf eh.shnum eh.shoff
    let tab ← findSymtabSection sh
    let strings ← sh[tab.shLink]?
    if tab.shEntsize != 24 || tab.shSize % 24 != 0 ||
        tab.shOffset + tab.shSize > elf.len || strings.shOffset + strings.shSize > elf.len then none
    else pure ((parseSymLoop elf (tab.shSize / 24) tab.shOffset).filterMap
      (buildImageFuncSlice elf eh strings sh ph))

/-- The linked extraction path preserves the same byte provenance guarantee. -/
theorem buildImageFuncSlice_sound (elf : Bytes) (eh : Elf64Ehdr) (strSh : Elf64Shdr)
    (shdrs : List Elf64Shdr) (phdrs : List Elf64ProgramHeader)
    (sym : Elf64Sym) (slice : ElfFuncSlice)
    (h : buildImageFuncSlice elf eh strSh shdrs phdrs sym = some slice) :
    ElfSliceOk elf slice := by
  simp only [buildImageFuncSlice, bind, Option.bind] at h
  try dsimp only at h
  repeat' first | contradiction | (split at h <;> try dsimp only at h)
  all_goals exact buildFuncSlice_sound _ _ _ _ _ _ _ h

end Qsag
