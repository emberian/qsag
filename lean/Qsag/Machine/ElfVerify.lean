module
/-
# ELF certificate composition

Consumes normalized ELF slices and the canonical decoded ISA/checker soundness API in
`Machine.IsaCt`. This module owns architecture dispatch, symbol contracts, per-slice
certificates, and the theorem connecting accepted ELF certificates to machine traces.
Concrete decoder regressions and negative tests are in `Tests.MachineAndSimt`.
-/

public import Qsag.Machine.IsaCt
public import Qsag.Math.Goldilocks
public import Qsag.Oracle.Keccak
public import Qsag.Math.Gf2Pow128
public import Qsag.Machine.ElfFixtures
public import Qsag.Machine.ElfParse
import Qsag.Machine.ElfParse

import Qsag.Tactic.AssuranceKit
public section
namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
  UInt64.instLawfulOrderOrd Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe

set_option autoImplicit false
set_option maxRecDepth 65536

@[expose] def checkElfSliceThreeWayNI (slice : ElfFuncSlice) (c : FuncContract) : Bool :=
  if slice.machine == elfMachineX86_64 then
    checkX86ThreeWayNI slice.code c
  else if slice.machine == elfMachineAArch64 then
    checkArm64ThreeWayNI slice.code c
  else
    false

@[expose] def checkElfFuncThreeWayNI (elfBytes : Bytes) (symName : String) (c : FuncContract) : Bool :=
  match extractElfFuncBytes elfBytes symName with
  | none => false
  | some slice => checkElfSliceThreeWayNI slice c

/-! ### Exact contracts for all 28 compiled `.rlib` symbols -/

@[expose] def mkContract (name : String) (pubGprs : List Nat)
    (pubMem : List (Nat × Nat) := []) (wipedGprs : List Nat := [])
    (usesRbp : Bool := false) (outPtr : Nat := 0) (outBytes : Nat := 0)
    (doitEnabled : Bool := true) : FuncContract :=
  ⟨name, pubGprs, pubMem, wipedGprs, usesRbp, outPtr, outBytes, doitEnabled⟩

/-- Contracts of the 19 `x86_64` symbols, in fixture order. Pointer/count inputs are public; loaded
data remain secret. -/
@[expose] def currentX86SymbolContracts : List FuncContract := [
  mkContract "qsag_asm_keccak_f1600_avx2_4x"        [4, 7, 6]       []           []        true 7 0x320,
  mkContract "qsag_asm_keccak_chi_mpc_avx2"         [4, 7, 6, 2, 1] []           [],
  mkContract "qsag_asm_gf256_shamir_mul_gfni"       [4, 7, 6, 2, 1] []           [],
  mkContract "qsag_asm_gf256_shamir_mac_gfni"       [4, 7, 6, 1]    []           [],
  mkContract "qsag_asm_gf256_shamir_mul_avx2"       [4, 7, 6, 2, 1, 8] [(8, 0x80)] [],
  mkContract "qsag_asm_gf256_shamir_mac_avx2"       [4, 7, 6, 1, 8] [(8, 0xA0)]  [],
  mkContract "qsag_asm_tower128_bdoz_mac_vpclmul"   [4, 7, 6, 2, 1] []           [],
  mkContract "qsag_asm_tower128_bdoz_mac_pclmul"    [4, 7, 6, 2, 1] []           [],
  mkContract "qsag_asm_goldilocks_mul_ct_x86_64"    [4]             []           [],
  mkContract "qsag_asm_goldilocks_add_ct_x86_64"    [4]             []           [],
  mkContract "qsag_asm_goldilocks_sub_ct_x86_64"    [4]             []           [],
  mkContract "qsag_asm_goldilocks_pow7_ct_x86_64"   [4]             []           [11],
  mkContract "qsag_asm_goldilocks_dot2_adx_x86_64"  [4]             []           [],
  mkContract "qsag_asm_ct_eq_32_x86_64"             [4, 7, 6]       []           [1, 2, 8],
  mkContract "qsag_asm_ct_eq_bytes_x86_64"          [4, 7, 6, 2]    []           [8, 9],
  mkContract "qsag_asm_ct_memzero_x86_64"           [4, 7, 6]       []           [],
  mkContract "qsag_asm_transpose64x256_avx2"        [4, 7],
  mkContract "qsag_asm_gf2_128_mul_acc_pclmul"      [4, 7, 6, 2, 1],
  mkContract "qsag_asm_gf2_128_mul_acc_vpclmul"     [4, 7, 6, 2, 1]
]

/-- Contracts of the 9 `aarch64` symbols, in fixture order. -/
@[expose] def currentAarch64SymbolContracts : List FuncContract := [
  mkContract "qsag_asm_enable_dit_aarch64"          [],
  mkContract "qsag_asm_keccak_sha3_neon"            [0, 1, 2],
  mkContract "qsag_asm_keccak_theta_rho_sha3_neon"  [0, 1],
  mkContract "qsag_asm_tower128_bdoz_mac_pmull"     [0, 1, 2, 3],
  mkContract "qsag_asm_goldilocks_mul_ct_aarch64"   [],
  mkContract "qsag_asm_ct_eq_32_aarch64"            [0, 1]          []           [2, 3, 4, 5, 6, 7],
  mkContract "qsag_asm_ct_memzero_aarch64"          [0, 1],
  mkContract "qsag_asm_transpose64x256_neon"        [0],
  mkContract "qsag_asm_gf2_128_mul_acc_pmull"       [0, 1, 2, 3]
]

@[expose] def verifySliceContractList : List ElfFuncSlice → List FuncContract → Bool
  | [], [] => true
  | s :: ss, c :: cs =>
    (s.name == c.symName) && checkElfSliceThreeWayNI s c && verifySliceContractList ss cs
  | _, _ => false

@[expose] def verifyAllRlibContracts (rlib : Bytes) (contracts : List FuncContract) : Bool :=
  verifySliceContractList (extractAllRlibFuncs rlib) contracts

/-! ### Mutation / Negative Teeth (`#tooth` Equivalents on Real & Mutated Machine-Code Streams) -/

@[expose] def patchBytesAt (bs : List UInt8) (off : Nat) (patch : List UInt8) : List UInt8 :=
  takeTR off bs ++ patch ++ bs.drop (off + patch.length)

@[expose] def findSliceByNameBytes (slices : List ElfFuncSlice) (target : List UInt8) : Option ElfFuncSlice :=
  slices.find? (fun s => s.nameBytes == target)

/-- Unified 3-Way Constant-Time NI + ABI Hygiene semantic postcondition for an `ELF64` `.text` slice. -/
def ElfSliceThreeWayNISafe (slice : ElfFuncSlice) (c : FuncContract) : Prop :=
  (slice.machine = elfMachineX86_64 ∧
   ∀ (s₁ s₂ : X86State), X86ContractInit c s₁ s₂ → ∀ (fuel : Nat),
     ∃ prog : List (DecodedInstr X86Instr),
       decodeX86Stream slice.code = some prog ∧
       let (s₁f, tr₁) := runX86 prog fuel s₁
       let (s₂f, tr₂) := runX86 prog fuel s₂
       tr₁ = tr₂ ∧
       (∀ obs ∈ tr₁, obs.isDoitSafe = true) ∧
       ((s₁f.halted = true ∧ s₂f.halted = true ∧ X86ExitHygiene c s₁ s₂ s₁f s₂f) ∨
        (s₁f.halted = false ∧ s₂f.halted = false))) ∨
  (slice.machine = elfMachineAArch64 ∧
   ∀ (s₁ s₂ : Arm64State), Arm64ContractInit c s₁ s₂ → ∀ (fuel : Nat),
     ∃ prog : List (DecodedInstr Arm64Instr),
       decodeArm64Stream slice.code = some prog ∧
       let (s₁f, tr₁) := runArm64 prog fuel s₁
       let (s₂f, tr₂) := runArm64 prog fuel s₂
       tr₁ = tr₂ ∧
       (∀ obs ∈ tr₁, obs.isDoitSafe = true) ∧
       ((s₁f.halted = true ∧ s₂f.halted = true ∧ Arm64ExitHygiene c s₁ s₂ s₁f s₂f) ∨
        (s₁f.halted = false ∧ s₂f.halted = false)))

theorem checkElfSliceThreeWayNI_sound {slice : ElfFuncSlice} {c : FuncContract}
    (hCheck : checkElfSliceThreeWayNI slice c = true) :
    ElfSliceThreeWayNISafe slice c := by
  unfold checkElfSliceThreeWayNI at hCheck
  by_cases hx : slice.machine == elfMachineX86_64
  · simp only [hx, ↓reduceIte] at hCheck
    exact Or.inl ⟨beq_iff_eq.mp hx, fun _ _ hInit fuel => checkX86ThreeWayNI_sound hCheck hInit fuel⟩
  · simp only [hx, Bool.false_eq_true, ↓reduceIte] at hCheck
    by_cases ha : slice.machine == elfMachineAArch64
    · simp only [ha, ↓reduceIte] at hCheck
      exact Or.inr ⟨beq_iff_eq.mp ha, fun _ _ hInit fuel => checkArm64ThreeWayNI_sound hCheck hInit fuel⟩
    · simp [ha] at hCheck

/-- **Master `ELF64` Binary 3-Way Constant-Time NI + ABI Hygiene Soundness Theorem (`§5`):**
    If `checkElfFuncThreeWayNI elfBytes symName c = true`, then `symName` resolves inside `elfBytes`
    to a valid `.text` subslice `slice` (`extractElfFuncBytes_in_text_section`) whose decoded
    machine-code semantics satisfies `PC-NI`, `Mem-NI`, `DOIT-NI`, callee-saved preservation, and
    epilogue scratch register zeroization (`ElfSliceThreeWayNISafe slice c`)! -/
theorem checkElfFuncThreeWayNI_sound {elfBytes : Bytes} {symName : String} {c : FuncContract}
    (hCheck : checkElfFuncThreeWayNI elfBytes symName c = true) :
    ∃ slice : ElfFuncSlice,
      extractElfFuncBytes elfBytes symName = some slice ∧
      ElfSliceOk elfBytes slice ∧
      ElfSliceThreeWayNISafe slice c := by
  unfold checkElfFuncThreeWayNI at hCheck
  cases hExt : extractElfFuncBytes elfBytes symName with
  | none => simp [hExt] at hCheck
  | some slice =>
    simp only [hExt] at hCheck
    exact ⟨slice, rfl, extractElfFuncBytes_in_text_section elfBytes symName slice hExt,
      checkElfSliceThreeWayNI_sound hCheck⟩

/-- An invariant certificate for one symbol. -/
inductive InvCert where
  | x86 (inv : PcMap X86AbsState)
  | arm (inv : PcMap Arm64AbsState)

/-- Architecture-dispatching certificate check for one slice. -/
@[expose] def checkElfSliceWithCert (slice : ElfFuncSlice) (c : FuncContract) : InvCert → Bool
  | .x86 inv => slice.machine == elfMachineX86_64 && checkX86WithInv slice.code c inv
  | .arm inv => slice.machine == elfMachineAArch64 && checkArm64WithInv slice.code c inv

theorem checkElfSliceWithCert_sound {slice : ElfFuncSlice} {c : FuncContract} {cert : InvCert}
    (hCheck : checkElfSliceWithCert slice c cert = true) :
    ElfSliceThreeWayNISafe slice c := by
  cases cert with
  | x86 inv =>
    simp only [checkElfSliceWithCert, Bool.and_eq_true, beq_iff_eq] at hCheck
    exact Or.inl ⟨hCheck.1, fun _ _ hInit fuel => checkX86WithInv_sound hCheck.2 hInit fuel⟩
  | arm inv =>
    simp only [checkElfSliceWithCert, Bool.and_eq_true, beq_iff_eq] at hCheck
    exact Or.inr ⟨hCheck.1, fun _ _ hInit fuel => checkArm64WithInv_sound hCheck.2 hInit fuel⟩

/-- The check for the `i`-th slice against the `i`-th contract and the `i`-th certificate. -/
@[expose] def certSliceAt (slices : List ElfFuncSlice) (contracts : List FuncContract)
    (certs : List InvCert) (i : Nat) : Bool :=
  match slices[i]?, contracts[i]?, certs[i]? with
  | some s, some c, some k => (s.name == c.symName) && checkElfSliceWithCert s c k
  | _, _, _ => false

/-- Per-index certificate checks give the name match and the semantic postcondition at every index. -/
theorem certSliceAt_sound {slices : List ElfFuncSlice} {contracts : List FuncContract}
    {certs : List InvCert}
    (hAt : ∀ i, i < slices.length → certSliceAt slices contracts certs i = true)
    (i : Nat) (hs : i < slices.length) (hc : i < contracts.length) :
    slices[i].name = contracts[i].symName ∧ ElfSliceThreeWayNISafe slices[i] contracts[i] := by
  have h := hAt i hs
  unfold certSliceAt at h
  rw [List.getElem?_eq_getElem hs, List.getElem?_eq_getElem hc] at h
  cases hk : certs[i]? with
  | none => rw [hk] at h; cases h
  | some k =>
    rw [hk] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h.1, checkElfSliceWithCert_sound h.2⟩

end Qsag
