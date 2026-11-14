module
/-
# Qsag.ElfFixtureVerify — certificates for the compiled `qsag-asm` archives

Fixture-specific half of the binary verification: everything here is about the two compiled
archives in `Qsag.CompiledRlibFixtures`.
1. Decode counts for all 23 extracted symbols.
2. One kernel-checked invariant certificate per symbol (`Qsag.ElfInvCerts`), checked by
   `certSliceAt`: decode the symbol's bytes and verify the supplied invariant is inductive.
3. The end-to-end corollaries: every symbol the parser extracts from each archive satisfies
   `ElfSliceThreeWayNISafe` under its contract.
4. Mutation teeth on the real compiled bytes.
-/

public import Qsag.ElfBinaryVerify
public import Qsag.ElfInvCerts
import all Qsag.ElfParse
import all Qsag.ElfBinaryVerify
import all Qsag.ElfInvCerts

public section
namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd

set_option autoImplicit false
set_option maxRecDepth 65536

/-! ## Decode counts -/

def listLenGenTRLoop {α : Type} : List α → Nat → Nat
  | [], acc => acc
  | _ :: xs, acc => listLenGenTRLoop xs (acc + 1)

def sumDecodedX86Loop : List ElfFuncSlice → Nat → Option Nat
  | [], acc => some acc
  | s :: ss, acc =>
    match decodeX86Stream s.code with
    | none => none
    | some ins => sumDecodedX86Loop ss (acc + listLenGenTRLoop ins 0)

def sumDecodedArm64Loop : List ElfFuncSlice → Nat → Option Nat
  | [], acc => some acc
  | s :: ss, acc =>
    match decodeArm64Stream s.code with
    | none => none
    | some ins => sumDecodedArm64Loop ss (acc + listLenGenTRLoop ins 0)

def totalDecodedX86Instrs (archiveBytes : Bytes) : Option Nat :=
  sumDecodedX86Loop (extractAllRlibFuncs archiveBytes) 0

def totalDecodedArm64Instrs (archiveBytes : Bytes) : Option Nat :=
  sumDecodedArm64Loop (extractAllRlibFuncs archiveBytes) 0

/-- Kernel-checked verification (`0 native_decide`) that all 16 `x86_64` `.rlib` functions decode
    cleanly to **999** exact `X86Instr` machine instructions. -/
theorem x86_rlib_all_16_decode_999_instrs :
    totalDecodedX86Instrs x86RlibArchiveBytes = some 999 := by
  unfold totalDecodedX86Instrs
  rw [x86_rlib_extracted_slices]
  decide +kernel

/-- Kernel-checked verification (`0 native_decide`) that all 7 `aarch64` `.rlib` functions decode
    cleanly to **299** exact `Arm64Instr` machine instructions. -/
theorem aarch64_rlib_all_7_decode_299_instrs :
    totalDecodedArm64Instrs aarch64RlibArchiveBytes = some 299 := by
  unfold totalDecodedArm64Instrs
  rw [aarch64_rlib_extracted_slices]
  decide +kernel



/-! ## Per-symbol invariant certificates -/

theorem x86_symbol_00_certificate :
    certSliceAt x86ExtractedSlices x86SymbolContracts x86InvCerts 0 = true := by decide +kernel
theorem x86_symbol_01_certificate :
    certSliceAt x86ExtractedSlices x86SymbolContracts x86InvCerts 1 = true := by decide +kernel
theorem x86_symbol_02_certificate :
    certSliceAt x86ExtractedSlices x86SymbolContracts x86InvCerts 2 = true := by decide +kernel
theorem x86_symbol_03_certificate :
    certSliceAt x86ExtractedSlices x86SymbolContracts x86InvCerts 3 = true := by decide +kernel
theorem x86_symbol_04_certificate :
    certSliceAt x86ExtractedSlices x86SymbolContracts x86InvCerts 4 = true := by decide +kernel
theorem x86_symbol_05_certificate :
    certSliceAt x86ExtractedSlices x86SymbolContracts x86InvCerts 5 = true := by decide +kernel
theorem x86_symbol_06_certificate :
    certSliceAt x86ExtractedSlices x86SymbolContracts x86InvCerts 6 = true := by decide +kernel
theorem x86_symbol_07_certificate :
    certSliceAt x86ExtractedSlices x86SymbolContracts x86InvCerts 7 = true := by decide +kernel
theorem x86_symbol_08_certificate :
    certSliceAt x86ExtractedSlices x86SymbolContracts x86InvCerts 8 = true := by decide +kernel
theorem x86_symbol_09_certificate :
    certSliceAt x86ExtractedSlices x86SymbolContracts x86InvCerts 9 = true := by decide +kernel
theorem x86_symbol_10_certificate :
    certSliceAt x86ExtractedSlices x86SymbolContracts x86InvCerts 10 = true := by decide +kernel
theorem x86_symbol_11_certificate :
    certSliceAt x86ExtractedSlices x86SymbolContracts x86InvCerts 11 = true := by decide +kernel
theorem x86_symbol_12_certificate :
    certSliceAt x86ExtractedSlices x86SymbolContracts x86InvCerts 12 = true := by decide +kernel
theorem x86_symbol_13_certificate :
    certSliceAt x86ExtractedSlices x86SymbolContracts x86InvCerts 13 = true := by decide +kernel
theorem x86_symbol_14_certificate :
    certSliceAt x86ExtractedSlices x86SymbolContracts x86InvCerts 14 = true := by decide +kernel
theorem x86_symbol_15_certificate :
    certSliceAt x86ExtractedSlices x86SymbolContracts x86InvCerts 15 = true := by decide +kernel

theorem aarch64_symbol_00_certificate :
    certSliceAt aarch64ExtractedSlices aarch64SymbolContracts aarch64InvCerts 0 = true := by decide +kernel
theorem aarch64_symbol_01_certificate :
    certSliceAt aarch64ExtractedSlices aarch64SymbolContracts aarch64InvCerts 1 = true := by decide +kernel
theorem aarch64_symbol_02_certificate :
    certSliceAt aarch64ExtractedSlices aarch64SymbolContracts aarch64InvCerts 2 = true := by decide +kernel
theorem aarch64_symbol_03_certificate :
    certSliceAt aarch64ExtractedSlices aarch64SymbolContracts aarch64InvCerts 3 = true := by decide +kernel
theorem aarch64_symbol_04_certificate :
    certSliceAt aarch64ExtractedSlices aarch64SymbolContracts aarch64InvCerts 4 = true := by decide +kernel
theorem aarch64_symbol_05_certificate :
    certSliceAt aarch64ExtractedSlices aarch64SymbolContracts aarch64InvCerts 5 = true := by decide +kernel
theorem aarch64_symbol_06_certificate :
    certSliceAt aarch64ExtractedSlices aarch64SymbolContracts aarch64InvCerts 6 = true := by decide +kernel

theorem x86_all_symbol_certificates (i : Nat) (hi : i < x86ExtractedSlices.length) :
    certSliceAt x86ExtractedSlices x86SymbolContracts x86InvCerts i = true := by
  have h16 : i < 16 := hi
  match i, h16 with
  | 0, _ => exact x86_symbol_00_certificate
  | 1, _ => exact x86_symbol_01_certificate
  | 2, _ => exact x86_symbol_02_certificate
  | 3, _ => exact x86_symbol_03_certificate
  | 4, _ => exact x86_symbol_04_certificate
  | 5, _ => exact x86_symbol_05_certificate
  | 6, _ => exact x86_symbol_06_certificate
  | 7, _ => exact x86_symbol_07_certificate
  | 8, _ => exact x86_symbol_08_certificate
  | 9, _ => exact x86_symbol_09_certificate
  | 10, _ => exact x86_symbol_10_certificate
  | 11, _ => exact x86_symbol_11_certificate
  | 12, _ => exact x86_symbol_12_certificate
  | 13, _ => exact x86_symbol_13_certificate
  | 14, _ => exact x86_symbol_14_certificate
  | 15, _ => exact x86_symbol_15_certificate
  | n + 16, h => exact absurd h (Nat.not_lt_of_ge (Nat.le_add_left 16 n))

theorem aarch64_all_symbol_certificates (i : Nat) (hi : i < aarch64ExtractedSlices.length) :
    certSliceAt aarch64ExtractedSlices aarch64SymbolContracts aarch64InvCerts i = true := by
  have h7 : i < 7 := hi
  match i, h7 with
  | 0, _ => exact aarch64_symbol_00_certificate
  | 1, _ => exact aarch64_symbol_01_certificate
  | 2, _ => exact aarch64_symbol_02_certificate
  | 3, _ => exact aarch64_symbol_03_certificate
  | 4, _ => exact aarch64_symbol_04_certificate
  | 5, _ => exact aarch64_symbol_05_certificate
  | 6, _ => exact aarch64_symbol_06_certificate
  | n + 7, h => exact absurd h (Nat.not_lt_of_ge (Nat.le_add_left 7 n))

/-! ## End-to-end corollaries -/

/-- **All 16 compiled `x86_64` kernels.** Every `STT_FUNC` symbol the parser extracts from
    `x86RlibArchiveBytes` carries its contract's name and satisfies 3-way constant-time
    noninterference with System V ABI hygiene. -/
theorem rlib_x86_every_symbol_three_way_ni_sound :
    (extractAllRlibFuncs x86RlibArchiveBytes).length = x86SymbolContracts.length ∧
    ∀ i : Nat, (hs : i < (extractAllRlibFuncs x86RlibArchiveBytes).length) →
      (hc : i < x86SymbolContracts.length) →
      ((extractAllRlibFuncs x86RlibArchiveBytes)[i]'hs).name =
        (x86SymbolContracts[i]'hc).symName ∧
      ElfSliceThreeWayNISafe ((extractAllRlibFuncs x86RlibArchiveBytes)[i]'hs)
        (x86SymbolContracts[i]'hc) := by
  have key : ∀ sl : List ElfFuncSlice, sl = x86ExtractedSlices →
      (sl.length = x86SymbolContracts.length ∧
       ∀ i : Nat, (hs : i < sl.length) → (hc : i < x86SymbolContracts.length) →
        sl[i].name = x86SymbolContracts[i].symName ∧
        ElfSliceThreeWayNISafe sl[i] x86SymbolContracts[i]) := by
    intro sl h
    subst h
    exact ⟨by decide, fun i hs hc => certSliceAt_sound x86_all_symbol_certificates i hs hc⟩
  exact key _ x86_rlib_extracted_slices

/-- **All 7 compiled `aarch64` kernels.** Every `STT_FUNC` symbol the parser extracts from
    `aarch64RlibArchiveBytes` carries its contract's name and satisfies 3-way constant-time
    noninterference with AAPCS64 hygiene. -/
theorem rlib_aarch64_every_symbol_three_way_ni_sound :
    (extractAllRlibFuncs aarch64RlibArchiveBytes).length = aarch64SymbolContracts.length ∧
    ∀ i : Nat, (hs : i < (extractAllRlibFuncs aarch64RlibArchiveBytes).length) →
      (hc : i < aarch64SymbolContracts.length) →
      ((extractAllRlibFuncs aarch64RlibArchiveBytes)[i]'hs).name =
        (aarch64SymbolContracts[i]'hc).symName ∧
      ElfSliceThreeWayNISafe ((extractAllRlibFuncs aarch64RlibArchiveBytes)[i]'hs)
        (aarch64SymbolContracts[i]'hc) := by
  have key : ∀ sl : List ElfFuncSlice, sl = aarch64ExtractedSlices →
      (sl.length = aarch64SymbolContracts.length ∧
       ∀ i : Nat, (hs : i < sl.length) → (hc : i < aarch64SymbolContracts.length) →
        sl[i].name = aarch64SymbolContracts[i].symName ∧
        ElfSliceThreeWayNISafe sl[i] aarch64SymbolContracts[i]) := by
    intro sl h
    subst h
    exact ⟨by decide, fun i hs hc => certSliceAt_sound aarch64_all_symbol_certificates i hs hc⟩
  exact key _ aarch64_rlib_extracted_slices

/-! ## Mutation teeth on the compiled bytes -/

/-- **Negative Tooth 5 (`mutant_unwiped_neon_reg_rejected`):**
    Surgically patching the real compiled `qsag_asm_tower128_bdoz_mac_pmull` `.text` slice from
    `aarch64RlibArchiveBytes` to replace `eor v16.16b, v16.16b, v16.16b` at byte offset `+0x104`
    with `nop` (`0xD503201F`) leaves `v16` tainted at `ret` and is immediately rejected (`false`)! -/
theorem mutant_unwiped_neon_reg_rejected :
    (match findSliceByNameBytes (extractAllRlibFuncs aarch64RlibArchiveBytes)
             [0x71, 0x73, 0x61, 0x67, 0x5f, 0x61, 0x73, 0x6d, 0x5f, 0x74, 0x6f, 0x77, 0x65, 0x72,
              0x31, 0x32, 0x38, 0x5f, 0x62, 0x64, 0x6f, 0x7a, 0x5f, 0x6d, 0x61, 0x63, 0x5f, 0x70,
              0x6d, 0x75, 0x6c, 0x6c] with
     | none => true
     | some slice =>
       let mutated := patchBytesAt slice.code 0x104 [0x1F, 0x20, 0x03, 0xD5]
       checkArm64ThreeWayNI mutated (mkContract "qsag_asm_tower128_bdoz_mac_pmull" [0, 1, 2, 3])) =
    false := by
  rw [aarch64_rlib_extracted_slices]
  decide +kernel

/-- **Negative Tooth 6 (`mutant_missing_vzeroupper_rejected`):**
    Surgically patching the real compiled `qsag_asm_gf256_shamir_mul_gfni` `.text` slice from
    `x86RlibArchiveBytes` to replace `vzeroupper` (`C5 F8 77` at byte offset `+0x72`) with three
    `nop`s (`90 90 90`) leaves dirty upper `YMM` state at `ret` and is immediately rejected (`false`)! -/
theorem mutant_missing_vzeroupper_rejected :
    (match findSliceByNameBytes (extractAllRlibFuncs x86RlibArchiveBytes)
             [0x71, 0x73, 0x61, 0x67, 0x5f, 0x61, 0x73, 0x6d, 0x5f, 0x67, 0x66, 0x32, 0x35, 0x36,
              0x5f, 0x73, 0x68, 0x61, 0x6d, 0x69, 0x72, 0x5f, 0x6d, 0x75, 0x6c, 0x5f, 0x67, 0x66,
              0x6e, 0x69] with
     | none => true
     | some slice =>
       let mutated := patchBytesAt slice.code 0x72 [0x90, 0x90, 0x90]
       checkX86ThreeWayNI mutated (mkContract "qsag_asm_gf256_shamir_mul_gfni" [4, 7, 6, 2, 1])) =
    false := by
  rw [x86_rlib_extracted_slices]
  decide +kernel



/-- The genuine certificate for `qsag_asm_tower128_bdoz_mac_pmull` does not accept the body with
    its `eor v16.16b, v16.16b, v16.16b` wipe replaced by `nop`. -/
theorem genuine_certificate_rejects_unwiped_neon_mutant :
    (match aarch64ExtractedSlices[3]? with
     | none => true
     | some slice =>
       checkArm64WithInv (patchBytesAt slice.code 0x104 [0x1F, 0x20, 0x03, 0xD5])
         (mkContract "qsag_asm_tower128_bdoz_mac_pmull" [0, 1, 2, 3]) aarch64InvCert03) = false := by
  decide +kernel

/-- A certificate for one symbol is not a certificate for another. -/
theorem certificate_not_transferable :
    certSliceAt x86ExtractedSlices x86SymbolContracts (x86InvCerts.drop 1) 0 = false := by
  decide +kernel

end Qsag
