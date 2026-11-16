module
/-
# Qsag.Machine.ElfFixtureVerify — certificates for the compiled `qsag-asm` archives

Fixture-specific half of the binary verification: everything here is about the two compiled
archives in `Qsag.Machine.ElfFixtures`.
1. Decode counts for the 28 extracted symbols.
2. One kernel-checked invariant certificate per symbol (`Qsag.Machine.ElfInvCerts`), checked by
   `certSliceAt`: decode the symbol's bytes and verify the supplied invariant is inductive.
3. The end-to-end corollaries: every symbol the parser extracts from each archive satisfies
   `ElfSliceThreeWayNISafe` under its contract.
4. Mutation teeth on the real compiled bytes.
-/

public import Qsag.Machine.ElfVerify
public import Qsag.Machine.ElfInvCerts
public import Qsag.Machine.ElfParse
public import Qsag.Machine.IsaCt

import Qsag.Tactic.AssuranceKit
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

/-! ## Per-symbol invariant certificates -/

/-- All five bitslice symbols are pinned as exact, nonempty parser-produced slices. -/
theorem current_bitslice_exports_pinned :
    ((extractAllRlibFuncs currentX86RlibArchiveBytes).drop 16).map
      (fun s => (s.name, s.code.length)) =
      [("qsag_asm_transpose64x256_avx2", 3809),
       ("qsag_asm_gf2_128_mul_acc_pclmul", 212),
       ("qsag_asm_gf2_128_mul_acc_vpclmul", 242)] ∧
    ((extractAllRlibFuncs currentAarch64RlibArchiveBytes).drop 7).map
      (fun s => (s.name, s.code.length)) =
      [("qsag_asm_transpose64x256_neon", 4264),
       ("qsag_asm_gf2_128_mul_acc_pmull", 216)] := by
  rw [currentX86_rlib_extracted_slices, currentAarch64_rlib_extracted_slices]
  decide +kernel

theorem currentX86_symbol_00_certificate :
    certSliceAt currentX86ExtractedSlices currentX86SymbolContracts currentX86InvCerts 0 = true := by decide +kernel

theorem currentX86_symbol_01_certificate :
    certSliceAt currentX86ExtractedSlices currentX86SymbolContracts currentX86InvCerts 1 = true := by decide +kernel

theorem currentX86_symbol_02_certificate :
    certSliceAt currentX86ExtractedSlices currentX86SymbolContracts currentX86InvCerts 2 = true := by decide +kernel

theorem currentX86_symbol_03_certificate :
    certSliceAt currentX86ExtractedSlices currentX86SymbolContracts currentX86InvCerts 3 = true := by decide +kernel

theorem currentX86_symbol_04_certificate :
    certSliceAt currentX86ExtractedSlices currentX86SymbolContracts currentX86InvCerts 4 = true := by decide +kernel

theorem currentX86_symbol_05_certificate :
    certSliceAt currentX86ExtractedSlices currentX86SymbolContracts currentX86InvCerts 5 = true := by decide +kernel

theorem currentX86_symbol_06_certificate :
    certSliceAt currentX86ExtractedSlices currentX86SymbolContracts currentX86InvCerts 6 = true := by decide +kernel

theorem currentX86_symbol_07_certificate :
    certSliceAt currentX86ExtractedSlices currentX86SymbolContracts currentX86InvCerts 7 = true := by decide +kernel

theorem currentX86_symbol_08_certificate :
    certSliceAt currentX86ExtractedSlices currentX86SymbolContracts currentX86InvCerts 8 = true := by decide +kernel

theorem currentX86_symbol_09_certificate :
    certSliceAt currentX86ExtractedSlices currentX86SymbolContracts currentX86InvCerts 9 = true := by decide +kernel

theorem currentX86_symbol_10_certificate :
    certSliceAt currentX86ExtractedSlices currentX86SymbolContracts currentX86InvCerts 10 = true := by decide +kernel

theorem currentX86_symbol_11_certificate :
    certSliceAt currentX86ExtractedSlices currentX86SymbolContracts currentX86InvCerts 11 = true := by decide +kernel

theorem currentX86_symbol_12_certificate :
    certSliceAt currentX86ExtractedSlices currentX86SymbolContracts currentX86InvCerts 12 = true := by decide +kernel

theorem currentX86_symbol_13_certificate :
    certSliceAt currentX86ExtractedSlices currentX86SymbolContracts currentX86InvCerts 13 = true := by decide +kernel

theorem currentX86_symbol_14_certificate :
    certSliceAt currentX86ExtractedSlices currentX86SymbolContracts currentX86InvCerts 14 = true := by decide +kernel

theorem currentX86_symbol_15_certificate :
    certSliceAt currentX86ExtractedSlices currentX86SymbolContracts currentX86InvCerts 15 = true := by decide +kernel

theorem currentX86_symbol_16_certificate :
    certSliceAt currentX86ExtractedSlices currentX86SymbolContracts currentX86InvCerts 16 = true := by decide +kernel

theorem currentX86_symbol_17_certificate :
    certSliceAt currentX86ExtractedSlices currentX86SymbolContracts currentX86InvCerts 17 = true := by decide +kernel

theorem currentX86_symbol_18_certificate :
    certSliceAt currentX86ExtractedSlices currentX86SymbolContracts currentX86InvCerts 18 = true := by decide +kernel

theorem currentX86_all_symbol_certificates (i : Nat) (hi : i < currentX86ExtractedSlices.length) :
    certSliceAt currentX86ExtractedSlices currentX86SymbolContracts currentX86InvCerts i = true := by
  have hn : i < 19 := hi
  match i, hn with
  | 0, _ => exact currentX86_symbol_00_certificate
  | 1, _ => exact currentX86_symbol_01_certificate
  | 2, _ => exact currentX86_symbol_02_certificate
  | 3, _ => exact currentX86_symbol_03_certificate
  | 4, _ => exact currentX86_symbol_04_certificate
  | 5, _ => exact currentX86_symbol_05_certificate
  | 6, _ => exact currentX86_symbol_06_certificate
  | 7, _ => exact currentX86_symbol_07_certificate
  | 8, _ => exact currentX86_symbol_08_certificate
  | 9, _ => exact currentX86_symbol_09_certificate
  | 10, _ => exact currentX86_symbol_10_certificate
  | 11, _ => exact currentX86_symbol_11_certificate
  | 12, _ => exact currentX86_symbol_12_certificate
  | 13, _ => exact currentX86_symbol_13_certificate
  | 14, _ => exact currentX86_symbol_14_certificate
  | 15, _ => exact currentX86_symbol_15_certificate
  | 16, _ => exact currentX86_symbol_16_certificate
  | 17, _ => exact currentX86_symbol_17_certificate
  | 18, _ => exact currentX86_symbol_18_certificate
  | k + 19, h => exact absurd h (Nat.not_lt_of_ge (Nat.le_add_left 19 k))

theorem currentX86_rlib_every_symbol_three_way_ni_sound :
    (extractAllRlibFuncs currentX86RlibArchiveBytes).length = currentX86SymbolContracts.length ∧
    ∀ i : Nat, (hs : i < (extractAllRlibFuncs currentX86RlibArchiveBytes).length) →
      (hc : i < currentX86SymbolContracts.length) →
      ((extractAllRlibFuncs currentX86RlibArchiveBytes)[i]'hs).name =
        (currentX86SymbolContracts[i]'hc).symName ∧
      ElfSliceThreeWayNISafe ((extractAllRlibFuncs currentX86RlibArchiveBytes)[i]'hs)
        (currentX86SymbolContracts[i]'hc) := by
  have key : ∀ sl : List ElfFuncSlice, sl = currentX86ExtractedSlices →
      (sl.length = currentX86SymbolContracts.length ∧
       ∀ i : Nat, (hs : i < sl.length) → (hc : i < currentX86SymbolContracts.length) →
        sl[i].name = currentX86SymbolContracts[i].symName ∧
        ElfSliceThreeWayNISafe sl[i] currentX86SymbolContracts[i]) := by
    intro sl h
    subst h
    exact ⟨by decide, fun i hs hc => certSliceAt_sound currentX86_all_symbol_certificates i hs hc⟩
  exact key _ currentX86_rlib_extracted_slices


theorem currentAarch64_symbol_00_certificate :
    certSliceAt currentAarch64ExtractedSlices currentAarch64SymbolContracts currentAarch64InvCerts 0 = true := by decide +kernel

theorem currentAarch64_symbol_01_certificate :
    certSliceAt currentAarch64ExtractedSlices currentAarch64SymbolContracts currentAarch64InvCerts 1 = true := by decide +kernel

theorem currentAarch64_symbol_02_certificate :
    certSliceAt currentAarch64ExtractedSlices currentAarch64SymbolContracts currentAarch64InvCerts 2 = true := by decide +kernel

theorem currentAarch64_symbol_03_certificate :
    certSliceAt currentAarch64ExtractedSlices currentAarch64SymbolContracts currentAarch64InvCerts 3 = true := by decide +kernel

theorem currentAarch64_symbol_04_certificate :
    certSliceAt currentAarch64ExtractedSlices currentAarch64SymbolContracts currentAarch64InvCerts 4 = true := by decide +kernel

theorem currentAarch64_symbol_05_certificate :
    certSliceAt currentAarch64ExtractedSlices currentAarch64SymbolContracts currentAarch64InvCerts 5 = true := by decide +kernel

theorem currentAarch64_symbol_06_certificate :
    certSliceAt currentAarch64ExtractedSlices currentAarch64SymbolContracts currentAarch64InvCerts 6 = true := by decide +kernel

theorem currentAarch64_symbol_07_certificate :
    certSliceAt currentAarch64ExtractedSlices currentAarch64SymbolContracts currentAarch64InvCerts 7 = true := by decide +kernel

theorem currentAarch64_symbol_08_certificate :
    certSliceAt currentAarch64ExtractedSlices currentAarch64SymbolContracts currentAarch64InvCerts 8 = true := by decide +kernel

theorem currentAarch64_all_symbol_certificates (i : Nat) (hi : i < currentAarch64ExtractedSlices.length) :
    certSliceAt currentAarch64ExtractedSlices currentAarch64SymbolContracts currentAarch64InvCerts i = true := by
  have hn : i < 9 := hi
  match i, hn with
  | 0, _ => exact currentAarch64_symbol_00_certificate
  | 1, _ => exact currentAarch64_symbol_01_certificate
  | 2, _ => exact currentAarch64_symbol_02_certificate
  | 3, _ => exact currentAarch64_symbol_03_certificate
  | 4, _ => exact currentAarch64_symbol_04_certificate
  | 5, _ => exact currentAarch64_symbol_05_certificate
  | 6, _ => exact currentAarch64_symbol_06_certificate
  | 7, _ => exact currentAarch64_symbol_07_certificate
  | 8, _ => exact currentAarch64_symbol_08_certificate
  | k + 9, h => exact absurd h (Nat.not_lt_of_ge (Nat.le_add_left 9 k))

theorem currentAarch64_rlib_every_symbol_three_way_ni_sound :
    (extractAllRlibFuncs currentAarch64RlibArchiveBytes).length = currentAarch64SymbolContracts.length ∧
    ∀ i : Nat, (hs : i < (extractAllRlibFuncs currentAarch64RlibArchiveBytes).length) →
      (hc : i < currentAarch64SymbolContracts.length) →
      ((extractAllRlibFuncs currentAarch64RlibArchiveBytes)[i]'hs).name =
        (currentAarch64SymbolContracts[i]'hc).symName ∧
      ElfSliceThreeWayNISafe ((extractAllRlibFuncs currentAarch64RlibArchiveBytes)[i]'hs)
        (currentAarch64SymbolContracts[i]'hc) := by
  have key : ∀ sl : List ElfFuncSlice, sl = currentAarch64ExtractedSlices →
      (sl.length = currentAarch64SymbolContracts.length ∧
       ∀ i : Nat, (hs : i < sl.length) → (hc : i < currentAarch64SymbolContracts.length) →
        sl[i].name = currentAarch64SymbolContracts[i].symName ∧
        ElfSliceThreeWayNISafe sl[i] currentAarch64SymbolContracts[i]) := by
    intro sl h
    subst h
    exact ⟨by decide, fun i hs hc => certSliceAt_sound currentAarch64_all_symbol_certificates i hs hc⟩
  exact key _ currentAarch64_rlib_extracted_slices

/-- All 19 `x86_64` symbols decode, to 1935 instructions in total. -/
theorem currentX86_all_symbols_decode :
    totalDecodedX86Instrs currentX86RlibArchiveBytes = some 1935 := by
  unfold totalDecodedX86Instrs
  rw [currentX86_rlib_extracted_slices]
  decide +kernel

/-- All 9 `aarch64` symbols decode, to 1420 instructions in total. -/
theorem currentAarch64_all_symbols_decode :
    totalDecodedArm64Instrs currentAarch64RlibArchiveBytes = some 1420 := by
  unfold totalDecodedArm64Instrs
  rw [currentAarch64_rlib_extracted_slices]
  decide +kernel


/-- Removing both architectural vector-clear instructions is detected in the fresh GFNI body. -/
theorem current_gfni_missing_vector_cleanup_rejected :
    checkX86WithInv (patchBytesAt currentX86ExtractedSlices[2].code 0x72
      [0x90, 0x90, 0x90, 0x90, 0x90])
      currentX86SymbolContracts[2] qsag_asm_gf256_shamir_mul_gfni_currentInv = false := by
  decide +kernel

theorem current_pmull_missing_wipe_rejected :
    checkArm64WithInv (patchBytesAt currentAarch64ExtractedSlices[3].code 0x104
      [0x1F, 0x20, 0x03, 0xD5])
      currentAarch64SymbolContracts[3] qsag_asm_tower128_bdoz_mac_pmull_currentInv = false := by
  decide +kernel


/-! ## Mutation teeth on the compiled bytes -/

/-- Patching the compiled `qsag_asm_tower128_bdoz_mac_pmull` slice of
    `currentAarch64RlibArchiveBytes` to replace `eor v16.16b, v16.16b, v16.16b` at byte offset
    `+0x104` with `nop` (`0xD503201F`) leaves `v16` tainted at `ret`; the invariant-inferring
    checker rejects it. -/
theorem mutant_unwiped_neon_reg_rejected :
    (match findSliceByNameBytes (extractAllRlibFuncs currentAarch64RlibArchiveBytes)
             [0x71, 0x73, 0x61, 0x67, 0x5f, 0x61, 0x73, 0x6d, 0x5f, 0x74, 0x6f, 0x77, 0x65, 0x72,
              0x31, 0x32, 0x38, 0x5f, 0x62, 0x64, 0x6f, 0x7a, 0x5f, 0x6d, 0x61, 0x63, 0x5f, 0x70,
              0x6d, 0x75, 0x6c, 0x6c] with
     | none => true
     | some slice =>
       let mutated := patchBytesAt slice.code 0x104 [0x1F, 0x20, 0x03, 0xD5]
       checkArm64ThreeWayNI mutated (mkContract "qsag_asm_tower128_bdoz_mac_pmull" [0, 1, 2, 3])) =
    false := by
  rw [currentAarch64_rlib_extracted_slices]
  decide +kernel

/-- Patching the compiled `qsag_asm_gf256_shamir_mul_gfni` slice of `currentX86RlibArchiveBytes`
    to replace its vector-clear instructions at byte offset `+0x72` with `nop`s leaves dirty upper
    `YMM` state at `ret`; the invariant-inferring checker rejects it. -/
theorem mutant_missing_vector_cleanup_rejected :
    (match findSliceByNameBytes (extractAllRlibFuncs currentX86RlibArchiveBytes)
             [0x71, 0x73, 0x61, 0x67, 0x5f, 0x61, 0x73, 0x6d, 0x5f, 0x67, 0x66, 0x32, 0x35, 0x36,
              0x5f, 0x73, 0x68, 0x61, 0x6d, 0x69, 0x72, 0x5f, 0x6d, 0x75, 0x6c, 0x5f, 0x67, 0x66,
              0x6e, 0x69] with
     | none => true
     | some slice =>
       let mutated := patchBytesAt slice.code 0x72 [0x90, 0x90, 0x90, 0x90, 0x90]
       checkX86ThreeWayNI mutated (mkContract "qsag_asm_gf256_shamir_mul_gfni" [4, 7, 6, 2, 1])) =
    false := by
  rw [currentX86_rlib_extracted_slices]
  decide +kernel



/-- A certificate for one symbol is not a certificate for another. -/
theorem certificate_not_transferable :
    certSliceAt currentX86ExtractedSlices currentX86SymbolContracts (currentX86InvCerts.drop 1) 0 = false := by
  decide +kernel

/-- The per-symbol check depends on the certificate: shifting the certificate list by one makes
    symbol 0 fail. -/
theorem current_certificate_mutation_tooth :
    ∃ i : Nat,
      certSliceAt currentX86ExtractedSlices currentX86SymbolContracts currentX86InvCerts i = true ∧
      certSliceAt currentX86ExtractedSlices currentX86SymbolContracts (currentX86InvCerts.drop 1) i = false :=
  ⟨0, currentX86_symbol_00_certificate, certificate_not_transferable⟩

theorem current_certificate_index_inhabited :
    ∃ i : Nat, i < currentX86ExtractedSlices.length ∧
      certSliceAt currentX86ExtractedSlices currentX86SymbolContracts currentX86InvCerts i = true :=
  ⟨13, by decide +kernel, currentX86_symbol_13_certificate⟩

#tooth_pair currentX86_all_symbol_certificates vs current_certificate_mutation_tooth
#verify_inhabited currentX86_all_symbol_certificates current_certificate_index_inhabited

end Qsag
