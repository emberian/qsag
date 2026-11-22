module
/-
# Qsag.Machine.ElfParse — indexed-reader `GNU ar` + `ELF64` parser and fixture extraction certificates

The parser reads its input through `Bytes`, a length plus an index function, so that a parse touches
only the header, section-table, symbol-table, name and code bytes it needs. The compiled archives in
`Qsag.Machine.ElfFixtures` are single natural-number literals; reading byte `i` is one shift.

Contents:
1. `Bytes` and its list views (`toList`, `slice`), with `ofList` round-trip lemmas.
2. `GNU ar` envelope validation and member parsing (`parseArArchive`, `parseArMember_subslice`).
3. `ELF64` header, section and symbol parsing (`extractAllElfFuncs`,
   `extractElfFuncBytes_in_text_section`), and archive-level provenance
   (`extractAllRlibFuncs_provenance`).
4. Extraction certificates: the parser applied to both compiled archives returns exactly the
   slices of `Qsag.Machine.ElfFixtures`.
-/

public import Qsag.Machine.Elf64Parse

import Qsag.Tactic.AssuranceKit
public section
namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd

set_option autoImplicit false
set_option maxRecDepth 65536

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
@[expose] noncomputable def currentX86RlibArchiveBytes : Bytes :=
  Bytes.ofNat currentX86RlibLiteral.1 currentX86RlibLiteral.2

/-- The compiled `aarch64` archive fixture as an indexed byte source. -/
@[expose] noncomputable def currentAarch64RlibArchiveBytes : Bytes :=
  Bytes.ofNat currentAarch64RlibLiteral.1 currentAarch64RlibLiteral.2

/-- The archive literal has no bits beyond its stated byte length. -/
theorem currentX86_rlib_archive_nat_fits :
    currentX86RlibLiteral.2 < 2 ^ (8 * currentX86RlibLiteral.1) := by decide +kernel

theorem currentAarch64_rlib_archive_nat_fits :
    currentAarch64RlibLiteral.2 < 2 ^ (8 * currentAarch64RlibLiteral.1) := by decide +kernel

/-- Certified extraction boundary: the parser applied to the compiled `x86_64` archive returns
    exactly the slices consumed by downstream proofs. -/
theorem currentX86_rlib_extracted_slices :
    extractAllRlibFuncs currentX86RlibArchiveBytes = currentX86ExtractedSlices := by decide +kernel

theorem currentAarch64_rlib_extracted_slices :
    extractAllRlibFuncs currentAarch64RlibArchiveBytes = currentAarch64ExtractedSlices := by decide +kernel

/-- `parseArArchive` + `extractAllElfFuncs` discover exactly the 19 exported `x86_64` symbols. -/
theorem currentX86_symbol_names_exact :
    (extractAllRlibFuncs currentX86RlibArchiveBytes).map ElfFuncSlice.name =
      currentX86ExportedSymbolNames := by
  rw [currentX86_rlib_extracted_slices]
  decide +kernel

/-- `parseArArchive` + `extractAllElfFuncs` discover exactly the 9 exported `aarch64` symbols. -/
theorem currentAarch64_symbol_names_exact :
    (extractAllRlibFuncs currentAarch64RlibArchiveBytes).map ElfFuncSlice.name =
      currentAarch64ExportedSymbolNames := by
  rw [currentAarch64_rlib_extracted_slices]
  decide +kernel

/-- Corrupting one byte of the archive literal inside a symbol body changes the extracted code:
    the certificate is sensitive to the code bytes, not only to the layout. -/
theorem currentX86_rlib_extraction_detects_code_flip :
    (extractAllRlibFuncs
        (Bytes.ofNat currentX86RlibLiteral.1 (currentX86RlibLiteral.2 ^^^ (1 <<< (8 * 400))))).map
        ElfFuncSlice.code ≠
      currentX86ExtractedSlices.map ElfFuncSlice.code := by
  decide +kernel

/-! ## Linked-image extraction

The ELF64 field layout and PT_LOAD terminology follow ELFSage's
`ELFSage/Types/ProgramHeaderTable.lean` (Draper Laboratory, MIT license,
https://github.com/shigoel/ELFSage). This independent indexed-reader
implementation checks file-backed executable ranges; it never treats BSS
or a virtual address as an offset into the file. The relocatable-object
extractor above keeps its own symbol selection.
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


/-- Every fresh symbol is an in-bounds slice of an actual archive member. -/
theorem currentX86_all_symbols_provenance (slice : ElfFuncSlice)
    (h : slice ∈ currentX86ExtractedSlices) :
    ∃ m ∈ parseArArchive currentX86RlibArchiveBytes,
      m.payloadOffset + m.payloadSize ≤ currentX86RlibArchiveBytes.len ∧
      slice.symSize > 0 ∧
      slice.symValue + slice.symSize ≤ slice.textSize ∧
      slice.textFileOffset + slice.textSize ≤ m.payloadSize ∧
      slice.code = currentX86RlibArchiveBytes.slice
        (m.payloadOffset + (slice.textFileOffset + slice.symValue)) slice.symSize := by
  apply extractAllRlibFuncs_provenance
  rw [currentX86_rlib_extracted_slices]
  exact h


/-- Every fresh symbol is an in-bounds slice of an actual archive member. -/
theorem currentAarch64_all_symbols_provenance (slice : ElfFuncSlice)
    (h : slice ∈ currentAarch64ExtractedSlices) :
    ∃ m ∈ parseArArchive currentAarch64RlibArchiveBytes,
      m.payloadOffset + m.payloadSize ≤ currentAarch64RlibArchiveBytes.len ∧
      slice.symSize > 0 ∧
      slice.symValue + slice.symSize ≤ slice.textSize ∧
      slice.textFileOffset + slice.textSize ≤ m.payloadSize ∧
      slice.code = currentAarch64RlibArchiveBytes.slice
        (m.payloadOffset + (slice.textFileOffset + slice.symValue)) slice.symSize := by
  apply extractAllRlibFuncs_provenance
  rw [currentAarch64_rlib_extracted_slices]
  exact h


theorem truncated_archive_provenance_tooth :
    (parseArArchive (Bytes.ofList [0x21, 0x3c])).length ≠ 1 := by decide +kernel

theorem currentX86_provenance_inhabited :
    ∃ slice : ElfFuncSlice, slice ∈ currentX86ExtractedSlices ∧ slice.symSize > 0 :=
  ⟨currentX86ExtractedSlices[0], List.mem_cons_self, by decide +kernel⟩

#tooth_pair currentX86_all_symbols_provenance vs truncated_archive_provenance_tooth
#verify_inhabited currentX86_all_symbols_provenance currentX86_provenance_inhabited

end Qsag
