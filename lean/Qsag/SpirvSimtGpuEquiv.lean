module
/-
# Qsag.SpirvSimtGpuEquiv — Binary SPIR-V 1.5/1.6 Compute, Multi-Wave Wave32 SIMT, Faial DRF & SIMT-CT

Machine-checked Lean 4.35 GPU verification foundation (constructive proofs, axioms strictly within `{propext, Quot.sound}`):

1. **§1 Structured `SPIR-V 1.5/1.6` Compute Module AST & Binary `Array UInt32` Word Codec:**
   Khronos 5-word binary headers (`magic = 0x07230203`), with explicit 1.5 (`0x00010500`)
   and 1.6 (`0x00010600`) version tags,
   capabilities (`Shader`, `Int64`, `SubgroupDispatch`, `GroupNonUniform`, `VulkanMemoryModel`),
   execution modes (`LocalSize`, `SubgroupSize 32`), decorations, SSA type/global declarations,
   64-bit & 32-bit `OpUMulExtended` / `OpSelect` / `OpAccessChain` / `OpLoad` / `OpStore` /
   `OpControlBarrier` (`Workgroup`, `AcquireRelease | WorkgroupMemory = 0x108`), and verified
   roundtrip `decodeSpirvModule (encodeSpirvModule m) = .ok m` (`encodeSpirvModule_injective`).
2. **§2 Genuine Multi-Wave Wave32 Workgroup Operational Semantics (`64 KiB` Shared LDS):**
   Models `numWaves * 32` threads (e.g. `8` Wave32 subgroups = `256` threads) sharing persistent
   `64 KiB` (`16,384`-dword) `Workgroup` LDS and global `StorageBuffer` memory under arbitrary
   cross-wave instruction interleavings with lockstep workgroup-wide `OpControlBarrier` release.
3. **§3 Compositional `Faial` MAP Data-Race Freedom & `SIMT-CT` Side-Channel Immunity:**
   Proves deterministic confluence across all valid wave interleavings (`multiWave_schedule_confluence`)
   from per-epoch pairwise write/read disjointness, paired with `#tooth` witnesses for missing
   barriers (`tooth_missing_barrier_causes_cross_wave_lds_race`) and single-wave LDS-wipe models
   (`tooth_single_wave_lds_wipe_corrupts_multiwave_reduction`). Establishes `SIMT-CT` hardware
   leakage-trace noninterference (`simt_ct_noninterference`) covering zero `EXEC`-mask divergence,
   public-affine coalesced global addressing, and 32-bank conflict-free LDS addressing
   (`odd_stride_lds_bank_conflict_free`, `merkle_skewed_lds_bank_conflict_free_both_epochs`, and
   `tooth_stride32_lds_causes_32way_bank_conflict`).
Scope: this module proves codec, scheduling, race-freedom and leakage-model results.
It does not yet prove functional equivalence of the runtime field-arithmetic,
Poseidon2, Merkle-tree or WHIR shaders. Such a theorem must connect the actual
shader words, their decoded program and execution to the independent field or
protocol specification. Importing those specifications does not supply that link.
The codec supports both 1.5 and 1.6; version tags describe encoded words, not the
runtime backend's architecture-enum name.
-/

import Qsag.Tactic.AssuranceKit
public import Qsag.Constructive
import all Qsag.Constructive
public import Qsag.Goldilocks
import all Qsag.Goldilocks
public import Qsag.Poseidon2
import all Qsag.Poseidon2
public import Qsag.Aggregation
import all Qsag.Aggregation

public section
namespace Qsag

open Aggregation

attribute [-instance] UInt8.instLawfulEqOrd UInt32.instLawfulEqOrd UInt32.instLawfulOrderOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd

instance (priority := 1200) : LawfulBEq UInt32 where
  eq_of_beq {a b} h := UInt32.eq_of_toBitVec_eq (eq_of_beq h)
  rfl {a} := by
    change (a.toBitVec == a.toBitVec) = true
    exact BEq.rfl

set_option autoImplicit false

/-! ## §1. Binary `SPIR-V 1.5/1.6` Compute Module AST & Verified `Array UInt32` Encoder/Decoder -/

/-- Khronos SPIR-V magic number (`0x07230203`). -/
def spirvMagic : UInt32 := 0x07230203

/-- Khronos SPIR-V 1.5 version word (`major = 1, minor = 5 -> 0x00010500`, Vulkan 1.2). -/
def spirvVersion15 : UInt32 := 0x00010500

/-- Khronos SPIR-V 1.6 version word (`major = 1, minor = 6 -> 0x00010600`, Vulkan 1.3+). -/
def spirvVersion16 : UInt32 := 0x00010600

/-- Supported Khronos SPIR-V binary versions (`1.5` for Vulkan 1.2, `1.6` for Vulkan 1.3+). -/
inductive SpirvVersion where
  | v1_5
  | v1_6
  deriving DecidableEq, Repr

def SpirvVersion.toWord : SpirvVersion → UInt32
  | .v1_5 => spirvVersion15
  | .v1_6 => spirvVersion16

def SpirvVersion.ofWord? (w : UInt32) : Option SpirvVersion :=
  if w == spirvVersion15 then some .v1_5
  else if w == spirvVersion16 then some .v1_6
  else none

theorem SpirvVersion.ofWord?_toWord (v : SpirvVersion) :
    SpirvVersion.ofWord? v.toWord = some v := by
  cases v <;> decide

/-- Little-endian UTF-8 word 0 of entry-point literal `"main\0"`. -/
def spirvMainWord0 : UInt32 := 0x6E69616D

/-- Little-endian UTF-8 word 1 (null padding) of entry-point literal `"main\0"`. -/
def spirvMainWord1 : UInt32 := 0x00000000

/-- SPIR-V `ExecutionModel.GLCompute = 5`. -/
def spirvExecModelGLCompute : UInt32 := 5

/-- SPIR-V `MemorySemantics` bitmasks (`AcquireRelease = 0x8`, `WorkgroupMemory = 0x100`). -/
def spirvSemAcquireRelease : UInt32 := 0x00000008
def spirvSemUniformMemory : UInt32 := 0x00000040
def spirvSemWorkgroupMemory : UInt32 := 0x00000100
def spirvSemWorkgroupAcqRel : UInt32 := 0x00000108

theorem spirvSemWorkgroupAcqRel_eq_or :
    spirvSemWorkgroupAcqRel = (spirvSemWorkgroupMemory ||| spirvSemAcquireRelease) := by
  decide

/-- Pack a SPIR-V instruction header word `(wordCount <<< 16) ||| opcode`. -/
def packSpirvWord0 (wordCount opcode : Nat) : UInt32 :=
  (UInt32.ofNat wordCount <<< 16) ||| UInt32.ofNat opcode

/-- Extract the 16-bit `wordCount` field from a SPIR-V instruction header word. -/
def unpackSpirvWordCount (w0 : UInt32) : Nat :=
  (w0 >>> 16).toNat

/-- Extract the 16-bit `opcode` field from a SPIR-V instruction header word. -/
def unpackSpirvOpcode (w0 : UInt32) : Nat :=
  (w0 &&& 0xFFFF).toNat

private theorem nat_shiftLeft_16_lt {wc : Nat} (hwc : wc < 65536) :
    wc <<< 16 < 4294967296 := by
  rw [Nat.shiftLeft_eq]
  have h16 : (2 : Nat) ^ 16 = 65536 := rfl
  rw [h16]
  omega

private theorem toNat_packSpirvWord0 {wc op : Nat} (hwc : wc < 65536) (hop : op < 65536) :
    (packSpirvWord0 wc op).toNat = (wc <<< 16) ||| op := by
  unfold packSpirvWord0
  have hwc32 : wc < 4294967296 := by omega
  have hop32 : op < 4294967296 := by omega
  have hsh32 : wc <<< 16 < 4294967296 := nat_shiftLeft_16_lt hwc
  have h1 : (UInt32.ofNat wc <<< 16).toNat = wc <<< 16 := by
    rw [UInt32.toNat_shiftLeft]
    have h16 : (16 : UInt32).toNat % 32 = 16 := rfl
    rw [h16]
    simp only [UInt32.toNat_ofNat', show (2 : Nat) ^ 32 = 4294967296 from rfl,
      Nat.mod_eq_of_lt hwc32, Nat.mod_eq_of_lt hsh32]
  have h2 : (UInt32.ofNat op).toNat = op := by
    rw [UInt32.toNat_ofNat', show (2 : Nat) ^ 32 = 4294967296 from rfl, Nat.mod_eq_of_lt hop32]
  rw [UInt32.toNat_or, h1, h2]

theorem unpack_packSpirvWord0 {wc op : Nat} (hwc : wc < 65536) (hop : op < 65536) :
    unpackSpirvWordCount (packSpirvWord0 wc op) = wc ∧
    unpackSpirvOpcode (packSpirvWord0 wc op) = op := by
  have hPack := toNat_packSpirvWord0 hwc hop
  have hopPow : op < 2 ^ 16 := by
    simpa [show (2 : Nat) ^ 16 = 65536 from rfl] using hop
  refine ⟨?_, ?_⟩
  · unfold unpackSpirvWordCount
    rw [UInt32.toNat_shiftRight, hPack]
    have h16 : (16 : UInt32).toNat % 32 = 16 := rfl
    rw [h16]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_shiftRight, Nat.testBit_or]
    have hOpZero : op.testBit (16 + i) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hopPow (Nat.pow_le_pow_right (by decide) (by omega)))
    have hSh : (wc <<< 16).testBit (16 + i) = wc.testBit i := by
      rw [Nat.testBit_shiftLeft]
      simp [show 16 ≤ 16 + i by omega, show 16 + i - 16 = i by omega]
    rw [hOpZero, hSh, Bool.or_false]
  · unfold unpackSpirvOpcode
    rw [UInt32.toNat_and, hPack]
    have hMask : (0xFFFF : UInt32).toNat = 2 ^ 16 - 1 := rfl
    rw [hMask]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_or, Constructive.testBit_mask]
    by_cases hi : i < 16
    · have hShZero : (wc <<< 16).testBit i = false := by
        rw [Nat.testBit_shiftLeft]
        simp [show ¬ (16 ≤ i) by omega]
      simp [hi, hShZero]
    · have hOpZero : op.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hopPow (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hi, hOpZero]

/-- Split a `UInt64` into its low and high 32-bit `UInt32` words (little-endian SPIR-V literal order). -/
def u64Lo32 (v : UInt64) : UInt32 := UInt32.ofNat (v.toNat % 4294967296)
def u64Hi32 (v : UInt64) : UInt32 := UInt32.ofNat (v.toNat / 4294967296)
def u64OfLoHi32 (lo hi : UInt32) : UInt64 := UInt64.ofNat (lo.toNat + 4294967296 * hi.toNat)

theorem u64OfLoHi32_lo_hi (v : UInt64) : u64OfLoHi32 (u64Lo32 v) (u64Hi32 v) = v := by
  unfold u64OfLoHi32 u64Lo32 u64Hi32
  have hv : v.toNat < 18446744073709551616 := v.toNat_lt
  have hlo : v.toNat % 4294967296 < 4294967296 := Nat.mod_lt _ (by decide)
  have hhi : v.toNat / 4294967296 < 4294967296 := by omega
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  change (UInt64.ofNat _).toNat = v.toNat
  rw [UInt64.toNat_ofNat']
  simp only [UInt32.toNat_ofNat', show (2 : Nat) ^ 32 = 4294967296 from rfl,
    show (2 : Nat) ^ 64 = 18446744073709551616 from rfl,
    Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hhi]
  rw [Nat.mod_add_div, Nat.mod_eq_of_lt hv]

theorem u64Lo32_u64OfLoHi32 (lo hi : UInt32) : u64Lo32 (u64OfLoHi32 lo hi) = lo := by
  unfold u64Lo32 u64OfLoHi32
  have hlo : lo.toNat < 4294967296 := lo.toNat_lt
  have hhi : hi.toNat < 4294967296 := hi.toNat_lt
  have hsum : lo.toNat + 4294967296 * hi.toNat < 18446744073709551616 := by omega
  apply UInt32.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  change (UInt32.ofNat _).toNat = lo.toNat
  rw [UInt32.toNat_ofNat', UInt64.toNat_ofNat']
  simp only [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl,
    show (2 : Nat) ^ 32 = 4294967296 from rfl, Nat.mod_eq_of_lt hsum]
  omega

theorem u64Hi32_u64OfLoHi32 (lo hi : UInt32) : u64Hi32 (u64OfLoHi32 lo hi) = hi := by
  unfold u64Hi32 u64OfLoHi32
  have hlo : lo.toNat < 4294967296 := lo.toNat_lt
  have hhi : hi.toNat < 4294967296 := hi.toNat_lt
  have hsum : lo.toNat + 4294967296 * hi.toNat < 18446744073709551616 := by omega
  apply UInt32.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  change (UInt32.ofNat _).toNat = hi.toNat
  rw [UInt32.toNat_ofNat', UInt64.toNat_ofNat']
  simp only [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl,
    show (2 : Nat) ^ 32 = 4294967296 from rfl, Nat.mod_eq_of_lt hsum]
  omega

/-- Capabilities in the compute `SPIR-V 1.6` profile (`OpCapability = 17`). -/
inductive SpirvCapability where
  | shader
  | int64
  | subgroupDispatch
  | groupNonUniform
  | vulkanMemoryModel
  deriving DecidableEq, Repr

def SpirvCapability.toWord : SpirvCapability → UInt32
  | .shader => 1
  | .int64 => 11
  | .subgroupDispatch => 58
  | .groupNonUniform => 61
  | .vulkanMemoryModel => 5345

def SpirvCapability.ofWord? (w : UInt32) : Option SpirvCapability :=
  if w == 1 then some .shader
  else if w == 11 then some .int64
  else if w == 58 then some .subgroupDispatch
  else if w == 61 then some .groupNonUniform
  else if w == 5345 then some .vulkanMemoryModel
  else none

theorem SpirvCapability.ofWord?_toWord (c : SpirvCapability) :
    SpirvCapability.ofWord? c.toWord = some c := by
  cases c <;> decide

/-- Addressing model (`OpMemoryModel` operand 0). -/
inductive SpirvAddressingModel where
  | logical
  | physicalStorageBuffer64
  deriving DecidableEq, Repr

def SpirvAddressingModel.toWord : SpirvAddressingModel → UInt32
  | .logical => 0
  | .physicalStorageBuffer64 => 5348

def SpirvAddressingModel.ofWord? (w : UInt32) : Option SpirvAddressingModel :=
  if w == 0 then some .logical
  else if w == 5348 then some .physicalStorageBuffer64
  else none

theorem SpirvAddressingModel.ofWord?_toWord (a : SpirvAddressingModel) :
    SpirvAddressingModel.ofWord? a.toWord = some a := by
  cases a <;> decide

/-- Memory consistency model (`OpMemoryModel` operand 1). -/
inductive SpirvMemoryModelKind where
  | glsl450
  | vulkan
  deriving DecidableEq, Repr

def SpirvMemoryModelKind.toWord : SpirvMemoryModelKind → UInt32
  | .glsl450 => 1
  | .vulkan => 3

def SpirvMemoryModelKind.ofWord? (w : UInt32) : Option SpirvMemoryModelKind :=
  if w == 1 then some .glsl450
  else if w == 3 then some .vulkan
  else none

theorem SpirvMemoryModelKind.ofWord?_toWord (m : SpirvMemoryModelKind) :
    SpirvMemoryModelKind.ofWord? m.toWord = some m := by
  cases m <;> decide

/-- Compute execution modes (`LocalSize = 17`, `SubgroupSize = 35`). -/
inductive SpirvExecutionMode where
  | localSize (x y z : UInt32)
  | subgroupSize (sz : UInt32)
  deriving DecidableEq, Repr

/-- SPIR-V storage classes (`Input = 1`, `Workgroup = 4`, `Function = 7`, `PushConstant = 9`, `StorageBuffer = 12`). -/
inductive SpirvStorageClass where
  | input
  | workgroup
  | function
  | pushConstant
  | storageBuffer
  deriving DecidableEq, Repr

def SpirvStorageClass.toWord : SpirvStorageClass → UInt32
  | .input => 1
  | .workgroup => 4
  | .function => 7
  | .pushConstant => 9
  | .storageBuffer => 12

def SpirvStorageClass.ofWord? (w : UInt32) : Option SpirvStorageClass :=
  if w == 1 then some .input
  else if w == 4 then some .workgroup
  else if w == 7 then some .function
  else if w == 9 then some .pushConstant
  else if w == 12 then some .storageBuffer
  else none

theorem SpirvStorageClass.ofWord?_toWord (sc : SpirvStorageClass) :
    SpirvStorageClass.ofWord? sc.toWord = some sc := by
  cases sc <;> decide

/-- Built-in compute invocation identifiers (`OpDecorate BuiltIn`). -/
inductive SpirvBuiltIn where
  | numWorkgroups
  | workgroupSize
  | workgroupId
  | localInvocationId
  | globalInvocationId
  | localInvocationIndex
  | subgroupSize
  | subgroupId
  | subgroupLocalInvocationId
  deriving DecidableEq, Repr

def SpirvBuiltIn.toWord : SpirvBuiltIn → UInt32
  | .numWorkgroups => 24
  | .workgroupSize => 25
  | .workgroupId => 26
  | .localInvocationId => 27
  | .globalInvocationId => 28
  | .localInvocationIndex => 29
  | .subgroupSize => 36
  | .subgroupId => 40
  | .subgroupLocalInvocationId => 41

def SpirvBuiltIn.ofWord? (w : UInt32) : Option SpirvBuiltIn :=
  if w == 24 then some .numWorkgroups
  else if w == 25 then some .workgroupSize
  else if w == 26 then some .workgroupId
  else if w == 27 then some .localInvocationId
  else if w == 28 then some .globalInvocationId
  else if w == 29 then some .localInvocationIndex
  else if w == 36 then some .subgroupSize
  else if w == 40 then some .subgroupId
  else if w == 41 then some .subgroupLocalInvocationId
  else none

theorem SpirvBuiltIn.ofWord?_toWord (b : SpirvBuiltIn) :
    SpirvBuiltIn.ofWord? b.toWord = some b := by
  cases b <;> decide

/-- Decorations carried by `OpDecorate = 71` and `OpMemberDecorate = 72`
    (`Block = 2`, `ArrayStride = 6`, `BuiltIn = 11`, `NonWritable = 24`, `NonReadable = 25`,
    `Binding = 33`, `DescriptorSet = 34`, `Offset = 35`). -/
inductive SpirvDecoration where
  | block
  | arrayStride (byteStride : UInt32)
  | builtIn (b : SpirvBuiltIn)
  | nonWritable
  | nonReadable
  | binding (slot : UInt32)
  | descriptorSet (setIdx : UInt32)
  | offset (byteOffset : UInt32)
  deriving DecidableEq, Repr

structure SpirvDecorateDecl where
  targetId : UInt32
  dec : SpirvDecoration
  deriving DecidableEq, Repr


/-- SPIR-V execution/memory scopes (`Device = 1`, `Workgroup = 2`, `Subgroup = 3`, `Invocation = 4`). -/
inductive SpirvScope where
  | device
  | workgroup
  | subgroup
  | invocation
  deriving DecidableEq, Repr

def SpirvScope.toWord : SpirvScope → UInt32
  | .device => 1
  | .workgroup => 2
  | .subgroup => 3
  | .invocation => 4

def SpirvScope.ofWord? (w : UInt32) : Option SpirvScope :=
  if w == 1 then some .device
  else if w == 2 then some .workgroup
  else if w == 3 then some .subgroup
  else if w == 4 then some .invocation
  else none

theorem SpirvScope.ofWord?_toWord (s : SpirvScope) :
    SpirvScope.ofWord? s.toWord = some s := by
  cases s <;> decide

/-- Integer widths supported by `OpTypeInt` in compute kernels (`32` and `64` bits). -/
inductive SpirvIntWidth where
  | w32
  | w64
  deriving DecidableEq, Repr

def SpirvIntWidth.toWord : SpirvIntWidth → UInt32
  | .w32 => 32
  | .w64 => 64

def SpirvIntWidth.ofWord? (w : UInt32) : Option SpirvIntWidth :=
  if w == 32 then some .w32
  else if w == 64 then some .w64
  else none

theorem SpirvIntWidth.ofWord?_toWord (w : SpirvIntWidth) :
    SpirvIntWidth.ofWord? w.toWord = some w := by
  cases w <;> decide

/-- Type declarations (`OpTypeVoid = 19`, `OpTypeBool = 20`, `OpTypeInt = 21`, `OpTypeArray = 28`,
    `OpTypeRuntimeArray = 29`, `OpTypeStruct = 30`, `OpTypePointer = 32`, `OpTypeFunction = 33`). -/
inductive SpirvTypeDecl where
  | typeVoid (resId : UInt32)
  | typeBool (resId : UInt32)
  | typeInt (resId : UInt32) (width : SpirvIntWidth) (signed : Bool)
  | typeVector (resId compTyId count : UInt32)
  | typeArray (resId elemTyId lenConstId : UInt32)
  | typeRuntimeArray (resId elemTyId : UInt32)
  | typeStruct (resId : UInt32) (fieldTyIds : List UInt32)
  | typePointer (resId : UInt32) (sc : SpirvStorageClass) (pointeeTyId : UInt32)
  | typeFunction (resId retTyId : UInt32) (paramTyIds : List UInt32)
  deriving DecidableEq, Repr

/-- Constants & module-scope variables (`OpConstantTrue = 41`, `OpConstantFalse = 42`,
    `OpConstant = 43`, `OpConstantComposite = 44`, `OpVariable = 59`). -/
inductive SpirvGlobalDecl where
  | constTrue (tyId resId : UInt32)
  | constFalse (tyId resId : UInt32)
  | const32 (tyId resId val : UInt32)
  | const64 (tyId resId : UInt32) (val : UInt64)
  | constComposite (tyId resId : UInt32) (partIds : List UInt32)
  | variable (tyId resId : UInt32) (sc : SpirvStorageClass) (initId : Option UInt32 := none)
  deriving DecidableEq, Repr

/-- The type/constant/global-variable section interleaves all three kinds of declaration. -/
inductive SpirvTyGlobal where
  | ty (t : SpirvTypeDecl)
  | glob (g : SpirvGlobalDecl)
  deriving DecidableEq, Repr

/-- Function-body instructions with exact Khronos `SPIR-V 1.5/1.6` opcodes. -/
inductive SpirvInst where
  | opExtInst (tyId resId setId instNum : UInt32) (argIds : List UInt32)
  | opVariable (tyId resId : UInt32) (sc : SpirvStorageClass) (initId : Option UInt32 := none)
  | opFunctionCall (tyId resId fnId : UInt32) (argIds : List UInt32)
  | opLoad (tyId resId ptrId : UInt32)
  | opStore (ptrId valId : UInt32)
  | opAccessChain (tyId resId baseId : UInt32) (indices : List UInt32)
  | opVectorShuffle (tyId resId vec1Id vec2Id : UInt32) (components : List UInt32)
  | opCompositeConstruct (tyId resId : UInt32) (partIds : List UInt32)
  | opCompositeExtract (tyId resId compId fieldIdx : UInt32)
  | opUConvert (tyId resId valId : UInt32)
  | opIAdd (tyId resId aId bId : UInt32)
  | opISub (tyId resId aId bId : UInt32)
  | opIMul (tyId resId aId bId : UInt32)
  | opUDiv (tyId resId aId bId : UInt32)
  | opUMod (tyId resId aId bId : UInt32)
  | opUMulExtended (tyId resId aId bId : UInt32)
  | opLogicalOr (tyId resId aId bId : UInt32)
  | opLogicalAnd (tyId resId aId bId : UInt32)
  | opLogicalNot (tyId resId aId : UInt32)
  | opSelect (tyId resId condId trueId falseId : UInt32)
  | opIEqual (tyId resId aId bId : UInt32)
  | opINotEqual (tyId resId aId bId : UInt32)
  | opUGreaterThan (tyId resId aId bId : UInt32)
  | opUGreaterThanEqual (tyId resId aId bId : UInt32)
  | opSGreaterThanEqual (tyId resId aId bId : UInt32)
  | opULessThan (tyId resId aId bId : UInt32)
  | opULessThanEqual (tyId resId aId bId : UInt32)
  | opShiftRightLogical (tyId resId baseId shiftId : UInt32)
  | opShiftLeftLogical (tyId resId baseId shiftId : UInt32)
  | opBitwiseOr (tyId resId aId bId : UInt32)
  | opBitwiseXor (tyId resId aId bId : UInt32)
  | opBitwiseAnd (tyId resId aId bId : UInt32)
  | opNot (tyId resId aId : UInt32)
  | opBitReverse (tyId resId aId : UInt32)
  | opControlBarrier (execScope memScope semanticsMask : UInt32)
  | opMemoryBarrier (memScope semanticsMask : UInt32)
  | opPhi (tyId resId : UInt32) (incoming : List UInt32)
  | opLoopMerge (mergeLabelId contLabelId loopCtrl : UInt32)
  | opSelectionMerge (mergeLabelId selectionCtrl : UInt32)
  | opLabel (labelId : UInt32)
  | opBranch (targetLabelId : UInt32)
  | opBranchConditional (condId trueLabelId falseLabelId : UInt32)
  | opSwitch (selectorId defaultLabelId : UInt32) (targets : List UInt32)
  | opReturn
  | opReturnValue (valId : UInt32)
  deriving DecidableEq, Repr

/-- Debug-section instructions (`OpSource = 3`, `OpSourceExtension = 4`, `OpName = 5`,
    `OpMemberName = 6`). Operand words (including packed UTF-8 literals) are kept verbatim. -/
inductive SpirvDebugDecl where
  | source (ops : List UInt32)
  | sourceExtension (ops : List UInt32)
  | name (ops : List UInt32)
  | memberName (ops : List UInt32)
  deriving DecidableEq, Repr

/-- Annotation-section instructions. -/
inductive SpirvAnnotation where
  | decorate (d : SpirvDecorateDecl)
  | memberDecorate (structId member : UInt32) (dec : SpirvDecoration)
  deriving DecidableEq, Repr

/-- `OpExtInstImport = 11` with its packed literal name. -/
structure SpirvExtInstImport where
  resId : UInt32
  name : List UInt32
  deriving DecidableEq, Repr

/-- One `OpFunction … OpFunctionEnd` definition: header, `OpFunctionParameter`s, and every
    block instruction in binary order. -/
structure SpirvFunction where
  resultTyId : UInt32
  funcId : UInt32
  control : UInt32
  funcTyId : UInt32
  params : List (UInt32 × UInt32)
  body : List SpirvInst
  deriving DecidableEq, Repr

/-- Complete `SPIR-V 1.5 / 1.6` compute module in the logical layout of the specification
    (§2.4): capabilities, extended-instruction imports, memory model, the `GLCompute` entry
    point, execution modes, debug, annotations, types/constants/globals, function definitions. -/
structure SpirvModule where
  version : SpirvVersion := .v1_6
  generator : UInt32
  idBound : UInt32
  capabilities : List SpirvCapability
  extInstImports : List SpirvExtInstImport
  addrModel : SpirvAddressingModel
  memModel : SpirvMemoryModelKind
  entryFuncId : UInt32
  interfaceIds : List UInt32
  execModes : List SpirvExecutionMode
  debug : List SpirvDebugDecl
  annotations : List SpirvAnnotation
  tyGlobals : List SpirvTyGlobal
  functions : List SpirvFunction
  deriving DecidableEq, Repr


/-- Raw framed SPIR-V instruction (`opcode < 65536` and `operands`). -/
structure RawSpirvInst where
  opcode : Nat
  operands : List UInt32
  deriving DecidableEq, Repr

def RawSpirvInst.wf (r : RawSpirvInst) : Bool :=
  decide (r.opcode < 65536) && decide (r.operands.length + 1 < 65536)

def encodeRawInst (r : RawSpirvInst) : List UInt32 :=
  packSpirvWord0 (r.operands.length + 1) r.opcode :: r.operands

def encodeRawInstList : List RawSpirvInst → List UInt32
  | [] => []
  | r :: rs => encodeRawInst r ++ encodeRawInstList rs

theorem encodeRawInstList_append (xs ys : List RawSpirvInst) :
    encodeRawInstList (xs ++ ys) = encodeRawInstList xs ++ encodeRawInstList ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeRawInstList, ih, List.append_assoc]

/-- Errors returned by the binary `SPIR-V 1.6` decoder. -/
inductive SpirvDecodeError where
  | truncatedHeader
  | badMagic (got : UInt32)
  | badVersion (got : UInt32)
  | badSchema (got : UInt32)
  | zeroIdBound
  | zeroWordCount
  | truncatedInstruction
  | malformedSection (msg : String)
  deriving DecidableEq, Repr

/-- Fuel-totalized word-stream splitter into `RawSpirvInst`s. -/
def parseRawInstStreamAux : Nat → List UInt32 → Except SpirvDecodeError (List RawSpirvInst)
  | _, [] => .ok []
  | 0, _ :: _ => .error .truncatedInstruction
  | fuel + 1, w0 :: rest =>
    let wc := unpackSpirvWordCount w0
    let op := unpackSpirvOpcode w0
    if wc == 0 then
      .error .zeroWordCount
    else if rest.length < wc - 1 then
      .error .truncatedInstruction
    else
      let args := rest.take (wc - 1)
      let rem := rest.drop (wc - 1)
      match parseRawInstStreamAux fuel rem with
      | .ok tail => .ok (⟨op, args⟩ :: tail)
      | .error e => .error e

def parseRawInstStream (words : List UInt32) : Except SpirvDecodeError (List RawSpirvInst) :=
  parseRawInstStreamAux words.length words

private theorem parseRawInstStreamAux_fuel_mono :
    ∀ {f1 f2 : Nat} {ws : List UInt32},
      ws.length ≤ f1 → ws.length ≤ f2 →
      parseRawInstStreamAux f1 ws = parseRawInstStreamAux f2 ws
  | f1, f2, [], _, _ => by
    cases f1 <;> cases f2 <;> rfl
  | 0, _, _ :: _, h1, _ => by simp at h1
  | _, 0, _ :: _, _, h2 => by simp at h2
  | f1 + 1, f2 + 1, w0 :: rest, h1, h2 => by
    simp only [parseRawInstStreamAux]
    by_cases hwc0 : (unpackSpirvWordCount w0 == 0) = true
    · simp [hwc0]
    · simp only [hwc0, Bool.false_eq_true, ↓reduceIte]
      by_cases hlt : rest.length < unpackSpirvWordCount w0 - 1
      · simp [hlt]
      · simp only [hlt, ↓reduceIte]
        have hrem1 : (rest.drop (unpackSpirvWordCount w0 - 1)).length ≤ f1 := by
          rw [List.length_drop]; simp at h1; omega
        have hrem2 : (rest.drop (unpackSpirvWordCount w0 - 1)).length ≤ f2 := by
          rw [List.length_drop]; simp at h2; omega
        rw [parseRawInstStreamAux_fuel_mono hrem1 hrem2]

private theorem parseRawInstStream_cons {r : RawSpirvInst} {more : List UInt32}
    (hr : r.wf = true) :
    parseRawInstStream (encodeRawInst r ++ more) =
      (parseRawInstStream more).map (r :: ·) := by
  rcases r with ⟨op, ops⟩
  unfold RawSpirvInst.wf at hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
  rcases hr with ⟨hop, hwc⟩
  unfold parseRawInstStream encodeRawInst
  simp only [List.cons_append, List.length_cons, List.length_append]
  dsimp only [parseRawInstStreamAux]
  obtain ⟨hUnpackWc, hUnpackOp⟩ := unpack_packSpirvWord0 hwc hop
  rw [hUnpackWc, hUnpackOp]
  have hNe0 : (ops.length + 1 == 0) = false := by simp
  have hSub : ops.length + 1 - 1 = ops.length := by omega
  have hNotLt : ¬ ((ops ++ more).length < ops.length) := by simp
  simp only [hNe0, Bool.false_eq_true, ↓reduceIte, hSub, hNotLt,
    List.take_left, List.drop_left]
  rw [parseRawInstStreamAux_fuel_mono (f2 := more.length) (by omega) (Nat.le_refl _)]
  cases parseRawInstStreamAux more.length more <;> rfl

theorem parseRawInstStream_encodeRawInstList {rs : List RawSpirvInst}
    (hrs : rs.all RawSpirvInst.wf = true) :
    parseRawInstStream (encodeRawInstList rs) = .ok rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hrs
    unfold encodeRawInstList
    rw [parseRawInstStream_cons hrs.1, ih hrs.2]
    rfl

/-! ### Per-Section Instruction Encoders & Decoders -/

def encodeCapabilityRaw (c : SpirvCapability) : RawSpirvInst :=
  ⟨17, [c.toWord]⟩

def decodeCapabilityRaw (r : RawSpirvInst) : Except SpirvDecodeError SpirvCapability :=
  match r.opcode, r.operands with
  | 17, [w] =>
    match SpirvCapability.ofWord? w with
    | some c => .ok c
    | none => .error (.malformedSection "unknown capability")
  | _, _ => .error (.malformedSection "expected OpCapability")

theorem decodeCapabilityRaw_encode (c : SpirvCapability) :
    decodeCapabilityRaw (encodeCapabilityRaw c) = .ok c := by
  simp [encodeCapabilityRaw, decodeCapabilityRaw, SpirvCapability.ofWord?_toWord]

def encodeExecModeRaw (entryId : UInt32) : SpirvExecutionMode → RawSpirvInst
  | .localSize x y z => ⟨16, [entryId, 17, x, y, z]⟩
  | .subgroupSize sz => ⟨16, [entryId, 35, sz]⟩

def decodeExecModeRaw (entryId : UInt32) (r : RawSpirvInst) :
    Except SpirvDecodeError SpirvExecutionMode :=
  match r.opcode, r.operands with
  | 16, [ep, m, x, y, z] =>
    if ep == entryId && m == 17 then .ok (.localSize x y z)
    else .error (.malformedSection "bad LocalSize")
  | 16, [ep, m, sz] =>
    if ep == entryId && m == 35 then .ok (.subgroupSize sz)
    else .error (.malformedSection "bad SubgroupSize")
  | _, _ => .error (.malformedSection "expected OpExecutionMode")

theorem decodeExecModeRaw_encode (entryId : UInt32) (em : SpirvExecutionMode) :
    decodeExecModeRaw entryId (encodeExecModeRaw entryId em) = .ok em := by
  cases em <;> simp [encodeExecModeRaw, decodeExecModeRaw]

def encodeDecorationWords : SpirvDecoration → List UInt32
  | .block => [2]
  | .arrayStride s => [6, s]
  | .builtIn b => [11, b.toWord]
  | .nonWritable => [24]
  | .nonReadable => [25]
  | .binding slot => [33, slot]
  | .descriptorSet setIdx => [34, setIdx]
  | .offset o => [35, o]

def decodeDecorationWords : List UInt32 → Option SpirvDecoration
  | [dtag] =>
    if dtag == 2 then some .block
    else if dtag == 24 then some .nonWritable
    else if dtag == 25 then some .nonReadable
    else none
  | [dtag, arg] =>
    if dtag == 6 then some (.arrayStride arg)
    else if dtag == 11 then (SpirvBuiltIn.ofWord? arg).map .builtIn
    else if dtag == 33 then some (.binding arg)
    else if dtag == 34 then some (.descriptorSet arg)
    else if dtag == 35 then some (.offset arg)
    else none
  | _ => none

theorem decodeDecorationWords_encode (d : SpirvDecoration) :
    decodeDecorationWords (encodeDecorationWords d) = some d := by
  cases d <;> simp [encodeDecorationWords, decodeDecorationWords, SpirvBuiltIn.ofWord?_toWord]

def encodeDecorateRaw (d : SpirvDecorateDecl) : RawSpirvInst :=
  ⟨71, d.targetId :: encodeDecorationWords d.dec⟩

def decodeDecorateRaw (r : RawSpirvInst) : Except SpirvDecodeError SpirvDecorateDecl :=
  match r.opcode, r.operands with
  | 71, tgt :: ws =>
    match decodeDecorationWords ws with
    | some dec => .ok ⟨tgt, dec⟩
    | none => .error (.malformedSection "unknown decoration")
  | _, _ => .error (.malformedSection "expected OpDecorate")

theorem decodeDecorateRaw_encode (d : SpirvDecorateDecl) :
    decodeDecorateRaw (encodeDecorateRaw d) = .ok d := by
  rcases d with ⟨tgt, dec⟩
  simp [encodeDecorateRaw, decodeDecorateRaw, decodeDecorationWords_encode]

def encodeAnnotationRaw : SpirvAnnotation → RawSpirvInst
  | .decorate d => encodeDecorateRaw d
  | .memberDecorate sId mem dec => ⟨72, sId :: mem :: encodeDecorationWords dec⟩

def isAnnotationOpcode (op : Nat) : Bool := op == 71 || op == 72

def decodeAnnotationRaw (r : RawSpirvInst) : Except SpirvDecodeError SpirvAnnotation :=
  match r.opcode, r.operands with
  | 72, sId :: mem :: ws =>
    match decodeDecorationWords ws with
    | some dec => .ok (.memberDecorate sId mem dec)
    | none => .error (.malformedSection "unknown member decoration")
  | _, _ =>
    match decodeDecorateRaw r with
    | .ok d => .ok (.decorate d)
    | .error e => .error e

theorem decodeAnnotationRaw_encode (a : SpirvAnnotation) :
    decodeAnnotationRaw (encodeAnnotationRaw a) = .ok a := by
  cases a with
  | decorate d =>
    have h := decodeDecorateRaw_encode d
    simp only [encodeAnnotationRaw]
    unfold decodeAnnotationRaw
    simp [encodeDecorateRaw, h] at h ⊢
  | memberDecorate sId mem dec =>
    simp [encodeAnnotationRaw, decodeAnnotationRaw, decodeDecorationWords_encode]

def encodeDebugRaw : SpirvDebugDecl → RawSpirvInst
  | .source ops => ⟨3, ops⟩
  | .sourceExtension ops => ⟨4, ops⟩
  | .name ops => ⟨5, ops⟩
  | .memberName ops => ⟨6, ops⟩

def isDebugOpcode (op : Nat) : Bool := op == 3 || op == 4 || op == 5 || op == 6

def decodeDebugRaw (r : RawSpirvInst) : Except SpirvDecodeError SpirvDebugDecl :=
  match r.opcode with
  | 3 => .ok (.source r.operands)
  | 4 => .ok (.sourceExtension r.operands)
  | 5 => .ok (.name r.operands)
  | 6 => .ok (.memberName r.operands)
  | _ => .error (.malformedSection "expected debug instruction")

theorem decodeDebugRaw_encode (d : SpirvDebugDecl) :
    decodeDebugRaw (encodeDebugRaw d) = .ok d := by
  cases d <;> rfl

def encodeExtInstImportRaw (e : SpirvExtInstImport) : RawSpirvInst :=
  ⟨11, e.resId :: e.name⟩

def decodeExtInstImportRaw (r : RawSpirvInst) : Except SpirvDecodeError SpirvExtInstImport :=
  match r.opcode, r.operands with
  | 11, res :: name => .ok ⟨res, name⟩
  | _, _ => .error (.malformedSection "expected OpExtInstImport")

theorem decodeExtInstImportRaw_encode (e : SpirvExtInstImport) :
    decodeExtInstImportRaw (encodeExtInstImportRaw e) = .ok e := by
  cases e; rfl

def encodeTypeRaw : SpirvTypeDecl → RawSpirvInst
  | .typeVoid res => ⟨19, [res]⟩
  | .typeBool res => ⟨20, [res]⟩
  | .typeInt res w signed => ⟨21, [res, w.toWord, if signed then 1 else 0]⟩
  | .typeVector res comp count => ⟨23, [res, comp, count]⟩
  | .typeArray res elem lenId => ⟨28, [res, elem, lenId]⟩
  | .typeRuntimeArray res elem => ⟨29, [res, elem]⟩
  | .typeStruct res fields => ⟨30, res :: fields⟩
  | .typePointer res sc pointee => ⟨32, [res, sc.toWord, pointee]⟩
  | .typeFunction res retTy params => ⟨33, res :: retTy :: params⟩

def isTypeOpcode (op : Nat) : Bool :=
  op == 19 || op == 20 || op == 21 || op == 23 || op == 28 || op == 29 || op == 30 ||
  op == 32 || op == 33

def decodeTypeRaw (r : RawSpirvInst) : Except SpirvDecodeError SpirvTypeDecl :=
  match r.opcode, r.operands with
  | 19, [res] => .ok (.typeVoid res)
  | 20, [res] => .ok (.typeBool res)
  | 21, [res, wWord, sWord] =>
    match SpirvIntWidth.ofWord? wWord with
    | some w =>
      if sWord == 0 then .ok (.typeInt res w false)
      else if sWord == 1 then .ok (.typeInt res w true)
      else .error (.malformedSection "bad OpTypeInt signedness")
    | none => .error (.malformedSection "bad OpTypeInt width")
  | 23, [res, comp, count] => .ok (.typeVector res comp count)
  | 28, [res, elem, lenId] => .ok (.typeArray res elem lenId)
  | 29, [res, elem] => .ok (.typeRuntimeArray res elem)
  | 30, res :: fields => .ok (.typeStruct res fields)
  | 32, [res, scWord, pointee] =>
    match SpirvStorageClass.ofWord? scWord with
    | some sc => .ok (.typePointer res sc pointee)
    | none => .error (.malformedSection "bad OpTypePointer storage class")
  | 33, res :: retTy :: params => .ok (.typeFunction res retTy params)
  | _, _ => .error (.malformedSection "malformed type declaration")

theorem decodeTypeRaw_encode (t : SpirvTypeDecl) :
    decodeTypeRaw (encodeTypeRaw t) = .ok t := by
  cases t with
  | typeInt res w signed =>
    cases signed <;> simp [encodeTypeRaw, decodeTypeRaw, SpirvIntWidth.ofWord?_toWord]
  | typePointer res sc pointee =>
    simp [encodeTypeRaw, decodeTypeRaw, SpirvStorageClass.ofWord?_toWord]
  | _ => simp [encodeTypeRaw, decodeTypeRaw]

def encodeGlobalRaw : SpirvGlobalDecl → RawSpirvInst
  | .constTrue ty res => ⟨41, [ty, res]⟩
  | .constFalse ty res => ⟨42, [ty, res]⟩
  | .const32 ty res val => ⟨43, [ty, res, val]⟩
  | .const64 ty res val => ⟨43, [ty, res, u64Lo32 val, u64Hi32 val]⟩
  | .constComposite ty res parts => ⟨44, ty :: res :: parts⟩
  | .variable ty res sc init =>
    ⟨59, match init with | none => [ty, res, sc.toWord] | some i => [ty, res, sc.toWord, i]⟩

def isGlobalOpcode (op : Nat) : Bool :=
  op == 41 || op == 42 || op == 43 || op == 44 || op == 59

def decodeGlobalRaw (r : RawSpirvInst) : Except SpirvDecodeError SpirvGlobalDecl :=
  match r.opcode, r.operands with
  | 41, [ty, res] => .ok (.constTrue ty res)
  | 42, [ty, res] => .ok (.constFalse ty res)
  | 43, [ty, res, val] => .ok (.const32 ty res val)
  | 43, [ty, res, lo, hi] => .ok (.const64 ty res (u64OfLoHi32 lo hi))
  | 44, ty :: res :: parts => .ok (.constComposite ty res parts)
  | 59, [ty, res, scWord] =>
    match SpirvStorageClass.ofWord? scWord with
    | some sc => .ok (.variable ty res sc none)
    | none => .error (.malformedSection "bad OpVariable storage class")
  | 59, [ty, res, scWord, init] =>
    match SpirvStorageClass.ofWord? scWord with
    | some sc => .ok (.variable ty res sc (some init))
    | none => .error (.malformedSection "bad OpVariable storage class")
  | _, _ => .error (.malformedSection "malformed global/constant declaration")

theorem decodeGlobalRaw_encode (g : SpirvGlobalDecl) :
    decodeGlobalRaw (encodeGlobalRaw g) = .ok g := by
  cases g with
  | const64 ty res val =>
    simp [encodeGlobalRaw, decodeGlobalRaw, u64OfLoHi32_lo_hi]
  | «variable» ty res sc init =>
    cases init <;> simp [encodeGlobalRaw, decodeGlobalRaw, SpirvStorageClass.ofWord?_toWord]
  | _ => simp [encodeGlobalRaw, decodeGlobalRaw]

def encodeTyGlobalRaw : SpirvTyGlobal → RawSpirvInst
  | .ty t => encodeTypeRaw t
  | .glob g => encodeGlobalRaw g

def isTyGlobalOpcode (op : Nat) : Bool := isTypeOpcode op || isGlobalOpcode op

def decodeTyGlobalRaw (r : RawSpirvInst) : Except SpirvDecodeError SpirvTyGlobal :=
  if isTypeOpcode r.opcode then
    match decodeTypeRaw r with
    | .ok t => .ok (.ty t)
    | .error e => .error e
  else
    match decodeGlobalRaw r with
    | .ok g => .ok (.glob g)
    | .error e => .error e

theorem decodeTyGlobalRaw_encode (x : SpirvTyGlobal) :
    decodeTyGlobalRaw (encodeTyGlobalRaw x) = .ok x := by
  cases x with
  | ty t =>
    have hop : isTypeOpcode (encodeTypeRaw t).opcode = true := by cases t <;> rfl
    simp [encodeTyGlobalRaw, decodeTyGlobalRaw, hop, decodeTypeRaw_encode]
  | glob g =>
    have hop : isTypeOpcode (encodeGlobalRaw g).opcode = false := by cases g <;> rfl
    simp [encodeTyGlobalRaw, decodeTyGlobalRaw, hop, decodeGlobalRaw_encode]

def encodeInstRaw : SpirvInst → RawSpirvInst
  | .opExtInst ty res setId instNum args => ⟨12, ty :: res :: setId :: instNum :: args⟩
  | .opVariable ty res sc init =>
    ⟨59, match init with | none => [ty, res, sc.toWord] | some i => [ty, res, sc.toWord, i]⟩
  | .opFunctionCall ty res fn args => ⟨57, ty :: res :: fn :: args⟩
  | .opLoad ty res ptr => ⟨61, [ty, res, ptr]⟩
  | .opStore ptr val => ⟨62, [ptr, val]⟩
  | .opAccessChain ty res base indices => ⟨65, ty :: res :: base :: indices⟩
  | .opVectorShuffle ty res v1 v2 comps => ⟨79, ty :: res :: v1 :: v2 :: comps⟩
  | .opCompositeConstruct ty res parts => ⟨80, ty :: res :: parts⟩
  | .opCompositeExtract ty res comp idx => ⟨81, [ty, res, comp, idx]⟩
  | .opUConvert ty res val => ⟨113, [ty, res, val]⟩
  | .opIAdd ty res a b => ⟨128, [ty, res, a, b]⟩
  | .opISub ty res a b => ⟨130, [ty, res, a, b]⟩
  | .opIMul ty res a b => ⟨132, [ty, res, a, b]⟩
  | .opUDiv ty res a b => ⟨134, [ty, res, a, b]⟩
  | .opUMod ty res a b => ⟨137, [ty, res, a, b]⟩
  | .opUMulExtended ty res a b => ⟨151, [ty, res, a, b]⟩
  | .opLogicalOr ty res a b => ⟨166, [ty, res, a, b]⟩
  | .opLogicalAnd ty res a b => ⟨167, [ty, res, a, b]⟩
  | .opLogicalNot ty res a => ⟨168, [ty, res, a]⟩
  | .opSelect ty res cond t f => ⟨169, [ty, res, cond, t, f]⟩
  | .opIEqual ty res a b => ⟨170, [ty, res, a, b]⟩
  | .opINotEqual ty res a b => ⟨171, [ty, res, a, b]⟩
  | .opUGreaterThan ty res a b => ⟨172, [ty, res, a, b]⟩
  | .opUGreaterThanEqual ty res a b => ⟨174, [ty, res, a, b]⟩
  | .opSGreaterThanEqual ty res a b => ⟨175, [ty, res, a, b]⟩
  | .opULessThan ty res a b => ⟨176, [ty, res, a, b]⟩
  | .opULessThanEqual ty res a b => ⟨178, [ty, res, a, b]⟩
  | .opShiftRightLogical ty res base sh => ⟨194, [ty, res, base, sh]⟩
  | .opShiftLeftLogical ty res base sh => ⟨196, [ty, res, base, sh]⟩
  | .opBitwiseOr ty res a b => ⟨197, [ty, res, a, b]⟩
  | .opBitwiseXor ty res a b => ⟨198, [ty, res, a, b]⟩
  | .opBitwiseAnd ty res a b => ⟨199, [ty, res, a, b]⟩
  | .opNot ty res a => ⟨200, [ty, res, a]⟩
  | .opBitReverse ty res a => ⟨204, [ty, res, a]⟩
  | .opControlBarrier execS memS sem => ⟨224, [execS, memS, sem]⟩
  | .opMemoryBarrier memS sem => ⟨225, [memS, sem]⟩
  | .opPhi ty res incoming => ⟨245, ty :: res :: incoming⟩
  | .opLoopMerge mergeL contL ctrl => ⟨246, [mergeL, contL, ctrl]⟩
  | .opSelectionMerge mergeL ctrl => ⟨247, [mergeL, ctrl]⟩
  | .opLabel lbl => ⟨248, [lbl]⟩
  | .opBranch tgt => ⟨249, [tgt]⟩
  | .opBranchConditional cond tL fL => ⟨250, [cond, tL, fL]⟩
  | .opSwitch sel defL tgts => ⟨251, sel :: defL :: tgts⟩
  | .opReturn => ⟨253, []⟩
  | .opReturnValue v => ⟨254, [v]⟩

def isBodyOpcode (op : Nat) : Bool :=
  op == 12 || op == 57 || op == 59 || op == 61 || op == 62 || op == 65 || op == 79 ||
  op == 80 || op == 81 || op == 113 || op == 128 || op == 130 || op == 132 || op == 134 ||
  op == 137 || op == 151 || op == 166 || op == 167 || op == 168 || op == 169 || op == 170 ||
  op == 171 || op == 172 || op == 174 || op == 175 || op == 176 || op == 178 || op == 194 ||
  op == 196 || op == 197 || op == 198 || op == 199 || op == 200 || op == 204 || op == 224 ||
  op == 225 || op == 245 || op == 246 || op == 247 || op == 248 || op == 249 || op == 250 ||
  op == 251 || op == 253 || op == 254

def decodeInstRaw (r : RawSpirvInst) : Except SpirvDecodeError SpirvInst :=
  match r.opcode, r.operands with
  | 12, ty :: res :: setId :: instNum :: args => .ok (.opExtInst ty res setId instNum args)
  | 59, [ty, res, scWord] =>
    match SpirvStorageClass.ofWord? scWord with
    | some sc => .ok (.opVariable ty res sc none)
    | none => .error (.malformedSection "bad function OpVariable storage class")
  | 59, [ty, res, scWord, init] =>
    match SpirvStorageClass.ofWord? scWord with
    | some sc => .ok (.opVariable ty res sc (some init))
    | none => .error (.malformedSection "bad function OpVariable storage class")
  | 57, ty :: res :: fn :: args => .ok (.opFunctionCall ty res fn args)
  | 61, [ty, res, ptr] => .ok (.opLoad ty res ptr)
  | 62, [ptr, val] => .ok (.opStore ptr val)
  | 65, ty :: res :: base :: indices => .ok (.opAccessChain ty res base indices)
  | 79, ty :: res :: v1 :: v2 :: comps => .ok (.opVectorShuffle ty res v1 v2 comps)
  | 80, ty :: res :: parts => .ok (.opCompositeConstruct ty res parts)
  | 81, [ty, res, comp, idx] => .ok (.opCompositeExtract ty res comp idx)
  | 113, [ty, res, val] => .ok (.opUConvert ty res val)
  | 128, [ty, res, a, b] => .ok (.opIAdd ty res a b)
  | 130, [ty, res, a, b] => .ok (.opISub ty res a b)
  | 132, [ty, res, a, b] => .ok (.opIMul ty res a b)
  | 134, [ty, res, a, b] => .ok (.opUDiv ty res a b)
  | 137, [ty, res, a, b] => .ok (.opUMod ty res a b)
  | 151, [ty, res, a, b] => .ok (.opUMulExtended ty res a b)
  | 166, [ty, res, a, b] => .ok (.opLogicalOr ty res a b)
  | 167, [ty, res, a, b] => .ok (.opLogicalAnd ty res a b)
  | 168, [ty, res, a] => .ok (.opLogicalNot ty res a)
  | 169, [ty, res, cond, t, f] => .ok (.opSelect ty res cond t f)
  | 170, [ty, res, a, b] => .ok (.opIEqual ty res a b)
  | 171, [ty, res, a, b] => .ok (.opINotEqual ty res a b)
  | 172, [ty, res, a, b] => .ok (.opUGreaterThan ty res a b)
  | 174, [ty, res, a, b] => .ok (.opUGreaterThanEqual ty res a b)
  | 175, [ty, res, a, b] => .ok (.opSGreaterThanEqual ty res a b)
  | 176, [ty, res, a, b] => .ok (.opULessThan ty res a b)
  | 178, [ty, res, a, b] => .ok (.opULessThanEqual ty res a b)
  | 194, [ty, res, base, sh] => .ok (.opShiftRightLogical ty res base sh)
  | 196, [ty, res, base, sh] => .ok (.opShiftLeftLogical ty res base sh)
  | 197, [ty, res, a, b] => .ok (.opBitwiseOr ty res a b)
  | 198, [ty, res, a, b] => .ok (.opBitwiseXor ty res a b)
  | 199, [ty, res, a, b] => .ok (.opBitwiseAnd ty res a b)
  | 200, [ty, res, a] => .ok (.opNot ty res a)
  | 204, [ty, res, a] => .ok (.opBitReverse ty res a)
  | 224, [es, ms, sem] => .ok (.opControlBarrier es ms sem)
  | 225, [ms, sem] => .ok (.opMemoryBarrier ms sem)
  | 245, ty :: res :: incoming => .ok (.opPhi ty res incoming)
  | 246, [mL, cL, ctrl] => .ok (.opLoopMerge mL cL ctrl)
  | 247, [mL, ctrl] => .ok (.opSelectionMerge mL ctrl)
  | 248, [lbl] => .ok (.opLabel lbl)
  | 249, [tgt] => .ok (.opBranch tgt)
  | 250, [cond, tL, fL] => .ok (.opBranchConditional cond tL fL)
  | 251, sel :: defL :: tgts => .ok (.opSwitch sel defL tgts)
  | 253, [] => .ok .opReturn
  | 254, [v] => .ok (.opReturnValue v)
  | _, _ => .error (.malformedSection "unknown body instruction")

theorem decodeInstRaw_encode (i : SpirvInst) :
    decodeInstRaw (encodeInstRaw i) = .ok i := by
  cases i with
  | opVariable ty res sc init =>
    cases sc <;> cases init <;> rfl
  | _ => rfl

def encodeParamRaw (p : UInt32 × UInt32) : RawSpirvInst := ⟨55, [p.1, p.2]⟩

def decodeParamRaw (r : RawSpirvInst) : Except SpirvDecodeError (UInt32 × UInt32) :=
  match r.opcode, r.operands with
  | 55, [ty, res] => .ok (ty, res)
  | _, _ => .error (.malformedSection "expected OpFunctionParameter")

theorem decodeParamRaw_encode (p : UInt32 × UInt32) :
    decodeParamRaw (encodeParamRaw p) = .ok p := by
  cases p; rfl

/-- Lower function definitions into raw instructions in binary order. -/
def encodeFunctionsRaw : List SpirvFunction → List RawSpirvInst
  | [] => []
  | f :: fs =>
    ⟨54, [f.resultTyId, f.funcId, f.control, f.funcTyId]⟩ ::
      (f.params.map encodeParamRaw ++
        (f.body.map encodeInstRaw ++ (⟨56, []⟩ :: encodeFunctionsRaw fs)))

/-- Lower a `SpirvModule` into its sequence of `RawSpirvInst`s following the 5-word header. -/
def moduleToRawInsts (m : SpirvModule) : List RawSpirvInst :=
  m.capabilities.map encodeCapabilityRaw ++
  (m.extInstImports.map encodeExtInstImportRaw ++
  (⟨14, [m.addrModel.toWord, m.memModel.toWord]⟩ ::
   ⟨15, spirvExecModelGLCompute :: m.entryFuncId :: spirvMainWord0 :: spirvMainWord1 ::
     m.interfaceIds⟩ ::
  (m.execModes.map (encodeExecModeRaw m.entryFuncId) ++
  (m.debug.map encodeDebugRaw ++
  (m.annotations.map encodeAnnotationRaw ++
  (m.tyGlobals.map encodeTyGlobalRaw ++
   encodeFunctionsRaw m.functions))))))

/-- Decidable well-formedness of a `SpirvModule`: non-zero id bound and every instruction
    fits lossless 16-bit word-count framing. -/
def WellFormedSpirvModule (m : SpirvModule) : Bool :=
  decide (0 < m.idBound.toNat) && (moduleToRawInsts m).all RawSpirvInst.wf

/-- Encode a `SpirvModule` into its exact binary `Array UInt32` SPIR-V 1.5/1.6 word stream. -/
def encodeSpirvModuleWords (m : SpirvModule) : List UInt32 :=
  [spirvMagic, m.version.toWord, m.generator, m.idBound, 0] ++
  encodeRawInstList (moduleToRawInsts m)

def encodeSpirvModule (m : SpirvModule) : Array UInt32 :=
  (encodeSpirvModuleWords m).toArray

private def splitByOp (pred : Nat → Bool) : List RawSpirvInst → List RawSpirvInst × List RawSpirvInst
  | [] => ([], [])
  | r :: rs =>
    if pred r.opcode then
      let (ys, zs) := splitByOp pred rs
      (r :: ys, zs)
    else
      ([], r :: rs)

private theorem splitByOp_append {pred : Nat → Bool} {xs ys : List RawSpirvInst}
    (hxs : ∀ x ∈ xs, pred x.opcode = true)
    (hys : match ys with | [] => True | y :: _ => pred y.opcode = false) :
    splitByOp pred (xs ++ ys) = (xs, ys) := by
  induction xs with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      simp only [List.nil_append, splitByOp]
      simp [hys]
  | cons x xs ih =>
    have hx : pred x.opcode = true := hxs x (.head _)
    have hrest : ∀ z ∈ xs, pred z.opcode = true := fun z hz => hxs z (.tail _ hz)
    simp only [List.cons_append, splitByOp, hx, ↓reduceIte, ih hrest]

private def mapExcept {α β : Type} (f : α → Except SpirvDecodeError β) :
    List α → Except SpirvDecodeError (List β)
  | [] => .ok []
  | x :: xs =>
    match f x, mapExcept f xs with
    | .ok y, .ok ys => .ok (y :: ys)
    | .error e, _ => .error e
    | .ok _, .error e => .error e

private theorem mapExcept_map_ok {α β : Type} (enc : β → α)
    (dec : α → Except SpirvDecodeError β) (hRound : ∀ b, dec (enc b) = .ok b) :
    ∀ bs : List β, mapExcept dec (bs.map enc) = .ok bs
  | [] => rfl
  | b :: bs => by
    simp [mapExcept, hRound b, mapExcept_map_ok enc dec hRound bs]

/-- Split the maximal `pred`-prefix off a raw instruction list and decode every member. -/
private def takeSection {β : Type} (pred : Nat → Bool)
    (dec : RawSpirvInst → Except SpirvDecodeError β) (raws : List RawSpirvInst) :
    Except SpirvDecodeError (List β × List RawSpirvInst) :=
  match mapExcept dec (splitByOp pred raws).1 with
  | .ok ys => .ok (ys, (splitByOp pred raws).2)
  | .error e => .error e

/-- The head (if any) of a raw instruction list fails `pred`. -/
private def HeadFails (pred : Nat → Bool) : List RawSpirvInst → Prop
  | [] => True
  | y :: _ => pred y.opcode = false

private theorem headFails_append {pred : Nat → Bool} {xs ys : List RawSpirvInst}
    (hxs : ∀ x ∈ xs, pred x.opcode = false) (hys : HeadFails pred ys) :
    HeadFails pred (xs ++ ys) := by
  cases xs with
  | nil => exact hys
  | cons x xs => exact hxs x (.head _)

private theorem headFails_map {β : Type} {pred : Nat → Bool} (enc : β → RawSpirvInst)
    (h : ∀ b, pred (enc b).opcode = false) (bs : List β) {ys : List RawSpirvInst}
    (hys : HeadFails pred ys) : HeadFails pred (bs.map enc ++ ys) :=
  headFails_append (by intro x hx; obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx; exact h b) hys

private theorem takeSection_encode {β : Type} {pred : Nat → Bool}
    {dec : RawSpirvInst → Except SpirvDecodeError β} (enc : β → RawSpirvInst)
    (hPred : ∀ b, pred (enc b).opcode = true) (hRound : ∀ b, dec (enc b) = .ok b)
    (bs : List β) {ys : List RawSpirvInst} (hys : HeadFails pred ys) :
    takeSection pred dec (bs.map enc ++ ys) = .ok (bs, ys) := by
  have hSplit : splitByOp pred (bs.map enc ++ ys) = (bs.map enc, ys) :=
    splitByOp_append
      (by intro x hx; obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx; exact hPred b)
      (by cases ys <;> first | trivial | exact hys)
  simp [takeSection, hSplit, mapExcept_map_ok enc dec hRound bs]

/-- Fuel-totalized parser for the function-definition section. -/
def parseFunctionsAux : Nat → List RawSpirvInst → Except SpirvDecodeError (List SpirvFunction)
  | _, [] => .ok []
  | 0, _ :: _ => .error (.malformedSection "function section fuel exhausted")
  | fuel + 1, hd :: rest =>
    match hd.opcode, hd.operands with
    | 54, [retTy, fnId, ctrl, fnTy] =>
      match takeSection (· == 55) decodeParamRaw rest with
      | .error e => .error e
      | .ok (params, r1) =>
        match takeSection isBodyOpcode decodeInstRaw r1 with
        | .error e => .error e
        | .ok (body, r2) =>
          match r2 with
          | ⟨56, []⟩ :: r3 =>
            match parseFunctionsAux fuel r3 with
            | .ok fs => .ok (⟨retTy, fnId, ctrl, fnTy, params, body⟩ :: fs)
            | .error e => .error e
          | _ => .error (.malformedSection "expected OpFunctionEnd")
    | _, _ => .error (.malformedSection "expected OpFunction")

private theorem parseFunctionsAux_encode :
    ∀ (fs : List SpirvFunction) (fuel : Nat), (encodeFunctionsRaw fs).length ≤ fuel →
      parseFunctionsAux fuel (encodeFunctionsRaw fs) = .ok fs
  | [], fuel, _ => by cases fuel <;> rfl
  | f :: fs, fuel, hFuel => by
    cases fuel with
    | zero => simp [encodeFunctionsRaw] at hFuel
    | succ fuel =>
      have hLen : (encodeFunctionsRaw fs).length ≤ fuel := by
        simp only [encodeFunctionsRaw, List.length_cons, List.length_append,
          List.length_map] at hFuel
        omega
      have hParams := takeSection_encode (pred := (· == 55)) (dec := decodeParamRaw)
        encodeParamRaw (fun _ => rfl) decodeParamRaw_encode f.params
        (ys := f.body.map encodeInstRaw ++ (⟨56, []⟩ :: encodeFunctionsRaw fs))
        (headFails_map encodeInstRaw (by intro i; cases i <;> rfl) f.body
          (ys := ⟨56, []⟩ :: encodeFunctionsRaw fs) rfl)
      have hBody := takeSection_encode (pred := isBodyOpcode) (dec := decodeInstRaw)
        encodeInstRaw (by intro i; cases i <;> rfl) decodeInstRaw_encode f.body
        (ys := ⟨56, []⟩ :: encodeFunctionsRaw fs) rfl
      simp only [encodeFunctionsRaw, parseFunctionsAux, hParams, hBody,
        parseFunctionsAux_encode fs fuel hLen]

/-- Decode a `SpirvModule` from its binary `Array UInt32` SPIR-V 1.5/1.6 word stream. -/
def decodeSpirvModuleWords (words : List UInt32) : Except SpirvDecodeError SpirvModule :=
  match words with
  | magic :: ver :: gen :: bound :: schema :: instWords =>
    if magic != spirvMagic then
      .error (.badMagic magic)
    else
      match SpirvVersion.ofWord? ver with
      | none => .error (.badVersion ver)
      | some parsedVer =>
        if schema != 0 then
          .error (.badSchema schema)
        else if bound.toNat == 0 then
          .error .zeroIdBound
        else
          match parseRawInstStream instWords with
          | .error e => .error e
          | .ok raws =>
            match takeSection (· == 17) decodeCapabilityRaw raws with
            | .error e => .error e
            | .ok (caps, r0) =>
            match takeSection (· == 11) decodeExtInstImportRaw r0 with
            | .error e => .error e
            | .ok (exts, r1) =>
            match r1 with
            | ⟨14, [addrW, memW]⟩ :: ⟨15, epModel :: entryFuncId :: m0 :: m1 :: ifaceIds⟩ :: r2 =>
              if epModel != spirvExecModelGLCompute || m0 != spirvMainWord0 || m1 != spirvMainWord1 then
                .error (.malformedSection "bad OpEntryPoint header")
              else
                match SpirvAddressingModel.ofWord? addrW, SpirvMemoryModelKind.ofWord? memW with
                | some addrM, some memM =>
                  match takeSection (· == 16) (decodeExecModeRaw entryFuncId) r2 with
                  | .error e => .error e
                  | .ok (ems, r3) =>
                  match takeSection isDebugOpcode decodeDebugRaw r3 with
                  | .error e => .error e
                  | .ok (dbg, r4) =>
                  match takeSection isAnnotationOpcode decodeAnnotationRaw r4 with
                  | .error e => .error e
                  | .ok (anns, r5) =>
                  match takeSection isTyGlobalOpcode decodeTyGlobalRaw r5 with
                  | .error e => .error e
                  | .ok (tgs, r6) =>
                  match parseFunctionsAux r6.length r6 with
                  | .error e => .error e
                  | .ok fns =>
                    .ok {
                      version := parsedVer
                      generator := gen
                      idBound := bound
                      capabilities := caps
                      extInstImports := exts
                      addrModel := addrM
                      memModel := memM
                      entryFuncId := entryFuncId
                      interfaceIds := ifaceIds
                      execModes := ems
                      debug := dbg
                      annotations := anns
                      tyGlobals := tgs
                      functions := fns
                    }
                | _, _ => .error (.malformedSection "bad OpMemoryModel operands")
            | _ => .error (.malformedSection "expected OpMemoryModel; OpEntryPoint")
  | _ => .error .truncatedHeader

def decodeSpirvModule (words : Array UInt32) : Except SpirvDecodeError SpirvModule :=
  decodeSpirvModuleWords words.toList

private theorem headFails_functions {pred : Nat → Bool} (h54 : pred 54 = false)
    (fs : List SpirvFunction) : HeadFails pred (encodeFunctionsRaw fs) := by
  cases fs with
  | nil => trivial
  | cons f fs => exact h54

/-- Lossless roundtrip of binary SPIR-V 1.5/1.6 encoding for well-formed compute modules. -/
theorem decodeSpirvModule_encodeSpirvModule {m : SpirvModule}
    (hm : WellFormedSpirvModule m = true) :
    decodeSpirvModule (encodeSpirvModule m) = .ok m := by
  unfold WellFormedSpirvModule at hm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
  have hBoundNe0 : (m.idBound.toNat == 0) = false := by
    have := hm.1; simp; omega
  change decodeSpirvModuleWords (encodeSpirvModuleWords m) = .ok m
  unfold encodeSpirvModuleWords decodeSpirvModuleWords
  simp only [List.cons_append, List.nil_append, bne_self_eq_false, Bool.false_eq_true,
    ↓reduceIte, SpirvVersion.ofWord?_toWord, hBoundNe0]
  rw [parseRawInstStream_encodeRawInstList hm.2]
  dsimp only
  unfold moduleToRawInsts
  have hFn : ∀ pred : Nat → Bool, pred 54 = false →
      HeadFails pred (encodeFunctionsRaw m.functions) :=
    fun pred h => headFails_functions h m.functions
  have hTg : ∀ pred : Nat → Bool, pred 54 = false →
      (∀ x : SpirvTyGlobal, pred (encodeTyGlobalRaw x).opcode = false) →
      HeadFails pred (m.tyGlobals.map encodeTyGlobalRaw ++ encodeFunctionsRaw m.functions) :=
    fun pred h54 h => headFails_map encodeTyGlobalRaw h m.tyGlobals (hFn pred h54)
  have hAnnOp : ∀ a : SpirvAnnotation, (encodeAnnotationRaw a).opcode = 71 ∨
      (encodeAnnotationRaw a).opcode = 72 := by
    intro a; cases a with
    | decorate d => exact .inl rfl
    | memberDecorate _ _ _ => exact .inr rfl
  have hDbgOp : ∀ d : SpirvDebugDecl, isDebugOpcode (encodeDebugRaw d).opcode = true := by
    intro d; cases d <;> rfl
  rw [takeSection_encode (pred := fun x => x == 17) encodeCapabilityRaw (fun _ => rfl) decodeCapabilityRaw_encode
    m.capabilities
    (headFails_map (pred := fun x => x == 17) encodeExtInstImportRaw (fun _ => rfl) m.extInstImports (ys := ⟨14, [m.addrModel.toWord, m.memModel.toWord]⟩ :: _) rfl)]
  dsimp only
  rw [takeSection_encode (pred := fun x => x == 11) encodeExtInstImportRaw (fun _ => rfl) decodeExtInstImportRaw_encode
    m.extInstImports (ys := ⟨14, [m.addrModel.toWord, m.memModel.toWord]⟩ :: _) rfl]
  simp only [bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
    SpirvAddressingModel.ofWord?_toWord, SpirvMemoryModelKind.ofWord?_toWord]
  rw [takeSection_encode (encodeExecModeRaw m.entryFuncId)
    (by intro em; cases em <;> rfl) (decodeExecModeRaw_encode m.entryFuncId) m.execModes
    (headFails_map encodeDebugRaw (by intro d; cases d <;> rfl) m.debug
      (headFails_map encodeAnnotationRaw
        (by intro a; rcases hAnnOp a with h | h <;> simp [h]) m.annotations
        (hTg _ rfl (by intro x; cases x with
          | ty t => cases t <;> rfl
          | glob g => cases g <;> rfl))))]
  dsimp only
  rw [takeSection_encode encodeDebugRaw hDbgOp decodeDebugRaw_encode m.debug
    (headFails_map encodeAnnotationRaw
      (by intro a; rcases hAnnOp a with h | h <;> simp [h, isDebugOpcode]) m.annotations
      (hTg _ rfl (by intro x; cases x with
          | ty t => cases t <;> rfl
          | glob g => cases g <;> rfl)))]
  dsimp only
  rw [takeSection_encode encodeAnnotationRaw
    (by intro a; rcases hAnnOp a with h | h <;> simp [h, isAnnotationOpcode])
    decodeAnnotationRaw_encode m.annotations (hTg _ rfl (by intro x; cases x with
          | ty t => cases t <;> rfl
          | glob g => cases g <;> rfl))]
  dsimp only
  rw [takeSection_encode encodeTyGlobalRaw
    (by intro x; cases x with
        | ty t => cases t <;> rfl
        | glob g => cases g <;> rfl)
    decodeTyGlobalRaw_encode m.tyGlobals (hFn _ rfl)]
  dsimp only
  rw [parseFunctionsAux_encode m.functions _ (Nat.le_refl _)]

/-- Injectivity of `encodeSpirvModule` on well-formed SPIR-V compute modules. -/
theorem encodeSpirvModule_injective {m₁ m₂ : SpirvModule}
    (h₁ : WellFormedSpirvModule m₁ = true) (h₂ : WellFormedSpirvModule m₂ = true)
    (hEq : encodeSpirvModule m₁ = encodeSpirvModule m₂) : m₁ = m₂ := by
  have d₁ := decodeSpirvModule_encodeSpirvModule h₁
  have d₂ := decodeSpirvModule_encodeSpirvModule h₂
  rw [hEq] at d₁
  have hOk : Except.ok m₁ = (Except.ok m₂ : Except SpirvDecodeError SpirvModule) :=
    d₁.symm.trans d₂
  injection hOk


/-- `#tooth` Corrupting the `0x07230203` SPIR-V magic header word is rejected by `decodeSpirvModule`. -/
theorem tooth_corrupted_spirv_magic_rejected (ver gen bound : UInt32) (rest : List UInt32) :
    decodeSpirvModule (#[0xDEADBEEF, ver, gen, bound, 0] ++ rest.toArray) =
      .error (.badMagic 0xDEADBEEF) := by
  unfold decodeSpirvModule
  simp [decodeSpirvModuleWords, spirvMagic]

/-- `#tooth` Downgrading or corrupting the SPIR-V 1.5/1.6 version header (`0x00010500` / `0x00010600`)
    to `0x00010000` is rejected by `decodeSpirvModule`. -/
theorem tooth_corrupted_spirv_version_rejected (gen bound : UInt32) (rest : List UInt32) :
    decodeSpirvModule (#[spirvMagic, 0x00010000, gen, bound, 0] ++ rest.toArray) =
      .error (.badVersion 0x00010000) := by
  unfold decodeSpirvModule
  simp [decodeSpirvModuleWords, spirvMagic, SpirvVersion.ofWord?, spirvVersion15, spirvVersion16]

/-! ## §2. Genuine Multi-Wave Wave32 Workgroup Operational Semantics (`64 KiB` Shared LDS) -/

/-- Native RDNA2 Wave32 subgroup width (`32` SIMD lanes per wave). -/
def wave32Lanes : Nat := 32

/-- Full RDNA2 WGP `Workgroup` LDS capacity: `65,536` bytes (`64 KiB` = `16,384` `UInt32` dwords). -/
def ldsCapacityBytes : Nat := 65536
def ldsCapacityDwords : Nat := 16384

theorem ldsCapacityBytes_eq_four_mul_dwords : ldsCapacityBytes = 4 * ldsCapacityDwords := by rfl

/-- Multi-wave workgroup geometry (`numWaves * 32` threads, e.g. `numWaves = 8` -> `256` threads). -/
structure WorkgroupConfig where
  workgroupId : Nat
  numWaves : Nat
  wavesPos : 0 < numWaves
  workgroupCount : Nat := 1

def WorkgroupConfig.totalThreads (cfg : WorkgroupConfig) : Nat :=
  cfg.numWaves * wave32Lanes

def WorkgroupConfig.localTid (_cfg : WorkgroupConfig) (wave lane : Nat) : Nat :=
  wave * wave32Lanes + lane

def WorkgroupConfig.globalTid (cfg : WorkgroupConfig) (wave lane : Nat) : Nat :=
  cfg.workgroupId * cfg.totalThreads + cfg.localTid wave lane

/-- Typed runtime SSA values per SIMT lane. -/
inductive SpirvVal where
  | vUndef
  | vBool (b : Bool)
  | vU32 (v : UInt32)
  | vU64 (v : UInt64)
  | vPair32 (lo hi : UInt32)
  | vPair64 (lo hi : UInt64)
  | vPtr (sc : SpirvStorageClass) (binding : Nat) (elemIdx : Nat) (width : SpirvIntWidth)
  deriving DecidableEq, Repr

/-- Shared memory state across ALL waves of a workgroup:
    - `lds` : persistent `64 KiB` (`16,384`-dword) `Workgroup` shared memory (never wiped between waves!)
    - `ssbo` : global `StorageBuffer` descriptor bindings (`binding -> dwordOffset -> UInt32`)
    - `pushConsts` : immutable public `PushConstant` dwords (`dwordOffset -> UInt32`). -/
structure GpuMemState where
  lds : Nat → UInt32
  ssbo : Nat → Nat → UInt32
  pushConsts : Nat → UInt32

def writeFn {α : Type} (m : Nat → α) (idx : Nat) (val : α) : Nat → α :=
  fun k => if k = idx then val else m k

def writeSsboDword (ssbo : Nat → Nat → UInt32) (binding addr : Nat) (val : UInt32) :
    Nat → Nat → UInt32 :=
  fun b k => if b = binding ∧ k = addr then val else ssbo b k

theorem writeFn_same {α : Type} (m : Nat → α) (idx : Nat) (val : α) :
    writeFn m idx val idx = val := by
  simp [writeFn]

theorem writeFn_other {α : Type} (m : Nat → α) {idx k : Nat} (val : α) (hne : k ≠ idx) :
    writeFn m idx val k = m k := by
  simp [writeFn, hne]

theorem writeFn_comm {α : Type} (m : Nat → α) {i₁ i₂ : Nat} (v₁ v₂ : α) (hne : i₁ ≠ i₂) :
    writeFn (writeFn m i₁ v₁) i₂ v₂ = writeFn (writeFn m i₂ v₂) i₁ v₁ := by
  funext k
  unfold writeFn
  by_cases h2 : k = i₂
  · subst h2; simp [hne.symm]
  · by_cases h1 : k = i₁
    · subst h1; simp [h2]
    · simp [h1, h2]

theorem writeSsboDword_comm (ssbo : Nat → Nat → UInt32) {b₁ a₁ b₂ a₂ : Nat} (v₁ v₂ : UInt32)
    (hne : (b₁, a₁) ≠ (b₂, a₂)) :
    writeSsboDword (writeSsboDword ssbo b₁ a₁ v₁) b₂ a₂ v₂ =
      writeSsboDword (writeSsboDword ssbo b₂ a₂ v₂) b₁ a₁ v₁ := by
  funext b k
  unfold writeSsboDword
  split
  · split
    · rename_i h2 h1
      exact False.elim (hne (Prod.ext (h1.1.symm.trans h2.1) (h1.2.symm.trans h2.2)))
    · rfl
  · split <;> rfl

def readU64Dwords (f : Nat → UInt32) (elemIdx : Nat) : UInt64 :=
  u64OfLoHi32 (f (2 * elemIdx)) (f (2 * elemIdx + 1))

def writeU64Dwords (f : Nat → UInt32) (elemIdx : Nat) (v : UInt64) : Nat → UInt32 :=
  writeFn (writeFn f (2 * elemIdx) (u64Lo32 v)) (2 * elemIdx + 1) (u64Hi32 v)

theorem readU64Dwords_writeU64Dwords_same (f : Nat → UInt32) (idx : Nat) (v : UInt64) :
    readU64Dwords (writeU64Dwords f idx v) idx = v := by
  unfold readU64Dwords writeU64Dwords
  rw [writeFn_other _ _ (by omega), writeFn_same, writeFn_same, u64OfLoHi32_lo_hi]

theorem readU64Dwords_writeU64Dwords_other (f : Nat → UInt32) {idx k : Nat} (v : UInt64)
    (hne : k ≠ idx) :
    readU64Dwords (writeU64Dwords f idx v) k = readU64Dwords f k := by
  unfold readU64Dwords writeU64Dwords
  rw [writeFn_other _ _ (by omega), writeFn_other _ _ (by omega),
      writeFn_other _ _ (by omega), writeFn_other _ _ (by omega)]

def writeSsboU64 (ssbo : Nat → Nat → UInt32) (binding elemIdx : Nat) (v : UInt64) :
    Nat → Nat → UInt32 :=
  writeSsboDword (writeSsboDword ssbo binding (2 * elemIdx) (u64Lo32 v))
    binding (2 * elemIdx + 1) (u64Hi32 v)

theorem readSsboU64_writeSsboU64_same (ssbo : Nat → Nat → UInt32) (b idx : Nat) (v : UInt64) :
    readU64Dwords (writeSsboU64 ssbo b idx v b) idx = v := by
  unfold readU64Dwords writeSsboU64 writeSsboDword
  have h : ¬ (2 * idx = 2 * idx + 1) := by omega
  simp only [h, true_and, ite_false, ite_true, u64OfLoHi32_lo_hi]

theorem readSsboU64_writeSsboU64_other_idx (ssbo : Nat → Nat → UInt32) (b : Nat) {idx k : Nat}
    (v : UInt64) (hne : k ≠ idx) :
    readU64Dwords (writeSsboU64 ssbo b idx v b) k = readU64Dwords (ssbo b) k := by
  unfold readU64Dwords writeSsboU64 writeSsboDword
  have h1 : ¬ (2 * k = 2 * idx + 1) := by omega
  have h2 : ¬ (2 * k = 2 * idx) := by omega
  have h4 : ¬ (2 * k + 1 = 2 * idx) := by omega
  simp [h1, h2, h4]

/-- Resolved static metadata of a `SpirvModule` for operational execution. -/
structure SpirvModuleEnv where
  intWidths : Nat → Option SpirvIntWidth
  ptrInfo : Nat → Option (SpirvStorageClass × Nat × SpirvIntWidth)
  initConst : Nat → SpirvVal
  builtIns : Nat → Option SpirvBuiltIn

/-- Initialize a lane's SSA register file with module constants and built-in invocation IDs. -/
def initLaneRegs (env : SpirvModuleEnv) (cfg : WorkgroupConfig) (wave lane : Nat) :
    Nat → SpirvVal :=
  fun ssaId =>
    match env.builtIns ssaId with
    | some .numWorkgroups => .vU32 (UInt32.ofNat cfg.workgroupCount)
    | some .workgroupSize => .vU32 (UInt32.ofNat cfg.totalThreads)
    | some .workgroupId => .vU32 (UInt32.ofNat cfg.workgroupId)
    | some .localInvocationId => .vU32 (UInt32.ofNat (cfg.localTid wave lane))
    | some .globalInvocationId => .vU32 (UInt32.ofNat (cfg.globalTid wave lane))
    | some .localInvocationIndex => .vU32 (UInt32.ofNat (cfg.localTid wave lane))
    | some .subgroupSize => .vU32 32
    | some .subgroupId => .vU32 (UInt32.ofNat wave)
    | some .subgroupLocalInvocationId => .vU32 (UInt32.ofNat lane)
    | none =>
      match env.ptrInfo ssaId with
      | some (sc, binding, w) => .vPtr sc binding 0 w
      | none => env.initConst ssaId

/-- Runtime errors during multi-wave `SPIR-V` execution. -/
inductive SimtExecError where
  | typeMismatch
  | ldsOutOfBounds (dwordAddr : Nat)
  | unexpectedBarrierInEpoch
  | barrierDivergence
  deriving DecidableEq, Repr

/-- Resolve a SPIR-V 32-bit constant `<id>` from `SpirvModuleEnv` (or treat `w` as an inline word
    when `env.initConst w.toNat = .vUndef`). -/
def resolveSpirvU32Const (env : SpirvModuleEnv) (w : UInt32) : UInt32 :=
  match env.initConst w.toNat with
  | .vU32 c => c
  | _ => w

def isWorkgroupAcqRelBarrier (env : SpirvModuleEnv) (es ms sem : UInt32) : Bool :=
  resolveSpirvU32Const env es == SpirvScope.workgroup.toWord &&
  resolveSpirvU32Const env ms == SpirvScope.workgroup.toWord &&
  resolveSpirvU32Const env sem == spirvSemWorkgroupAcqRel

/-- Pure per-lane ALU + `OpAccessChain` + `OpLoad` evaluation (excluding `OpStore` / `OpControlBarrier`). -/
def evalLanePureInst (env : SpirvModuleEnv) (mem : GpuMemState) (regs : Nat → SpirvVal)
    (inst : SpirvInst) : Except SimtExecError (Nat × SpirvVal) :=
  match inst with
  | .opAccessChain tyId resId baseId [idxId] =>
    match regs baseId.toNat, regs idxId.toNat with
    | .vPtr sc binding baseOff elemW, .vU32 idx =>
      let w := (env.ptrInfo tyId.toNat).map (·.2.2) |>.getD elemW
      .ok (resId.toNat, .vPtr sc binding (baseOff + idx.toNat) w)
    | .vPtr sc binding baseOff elemW, .vU64 idx =>
      let w := (env.ptrInfo tyId.toNat).map (·.2.2) |>.getD elemW
      .ok (resId.toNat, .vPtr sc binding (baseOff + idx.toNat) w)
    | _, _ => .error .typeMismatch
  | .opLoad _ resId ptrId =>
    match regs ptrId.toNat with
    | .vPtr .workgroup _ elemIdx .w32 =>
      if elemIdx < ldsCapacityDwords then
        .ok (resId.toNat, .vU32 (mem.lds elemIdx))
      else
        .error (.ldsOutOfBounds elemIdx)
    | .vPtr .workgroup _ elemIdx .w64 =>
      if 2 * elemIdx + 1 < ldsCapacityDwords then
        .ok (resId.toNat, .vU64 (readU64Dwords mem.lds elemIdx))
      else
        .error (.ldsOutOfBounds (2 * elemIdx + 1))
    | .vPtr .storageBuffer binding elemIdx .w32 =>
      .ok (resId.toNat, .vU32 (mem.ssbo binding elemIdx))
    | .vPtr .storageBuffer binding elemIdx .w64 =>
      .ok (resId.toNat, .vU64 (readU64Dwords (mem.ssbo binding) elemIdx))
    | .vPtr .pushConstant _ elemIdx .w32 =>
      .ok (resId.toNat, .vU32 (mem.pushConsts elemIdx))
    | .vPtr .pushConstant _ elemIdx .w64 =>
      .ok (resId.toNat, .vU64 (readU64Dwords mem.pushConsts elemIdx))
    | _ => .error .typeMismatch
  | .opCompositeExtract _ resId compId fieldIdx =>
    match regs compId.toNat, fieldIdx.toNat with
    | .vPair32 lo _, 0 => .ok (resId.toNat, .vU32 lo)
    | .vPair32 _ hi, 1 => .ok (resId.toNat, .vU32 hi)
    | .vPair64 lo _, 0 => .ok (resId.toNat, .vU64 lo)
    | .vPair64 _ hi, 1 => .ok (resId.toNat, .vU64 hi)
    | _, _ => .error .typeMismatch
  | .opUConvert tyId resId valId =>
    match env.intWidths tyId.toNat, regs valId.toNat with
    | some .w64, .vU32 v => .ok (resId.toNat, .vU64 (UInt64.ofNat v.toNat))
    | some .w32, .vU64 v => .ok (resId.toNat, .vU32 (UInt32.ofNat (v.toNat % 4294967296)))
    | _, _ => .error .typeMismatch
  | .opIAdd _ resId aId bId =>
    match regs aId.toNat, regs bId.toNat with
    | .vU32 a, .vU32 b => .ok (resId.toNat, .vU32 (a + b))
    | .vU64 a, .vU64 b => .ok (resId.toNat, .vU64 (a + b))
    | _, _ => .error .typeMismatch
  | .opISub _ resId aId bId =>
    match regs aId.toNat, regs bId.toNat with
    | .vU32 a, .vU32 b => .ok (resId.toNat, .vU32 (a - b))
    | .vU64 a, .vU64 b => .ok (resId.toNat, .vU64 (a - b))
    | _, _ => .error .typeMismatch
  | .opIMul _ resId aId bId =>
    match regs aId.toNat, regs bId.toNat with
    | .vU32 a, .vU32 b => .ok (resId.toNat, .vU32 (a * b))
    | .vU64 a, .vU64 b => .ok (resId.toNat, .vU64 (a * b))
    | _, _ => .error .typeMismatch
  | .opUDiv _ resId aId bId =>
    match regs aId.toNat, regs bId.toNat with
    | .vU32 a, .vU32 b => .ok (resId.toNat, .vU32 (if b == 0 then 0 else a / b))
    | .vU64 a, .vU64 b => .ok (resId.toNat, .vU64 (if b == 0 then 0 else a / b))
    | _, _ => .error .typeMismatch
  | .opUMod _ resId aId bId =>
    match regs aId.toNat, regs bId.toNat with
    | .vU32 a, .vU32 b => .ok (resId.toNat, .vU32 (if b == 0 then 0 else a % b))
    | .vU64 a, .vU64 b => .ok (resId.toNat, .vU64 (if b == 0 then 0 else a % b))
    | _, _ => .error .typeMismatch
  | .opUMulExtended _ resId aId bId =>
    match regs aId.toNat, regs bId.toNat with
    | .vU32 a, .vU32 b =>
      let prod := a.toNat * b.toNat
      .ok (resId.toNat, .vPair32 (UInt32.ofNat (prod % 4294967296)) (UInt32.ofNat (prod / 4294967296)))
    | .vU64 a, .vU64 b =>
      let prod := a.toNat * b.toNat
      .ok (resId.toNat, .vPair64 (UInt64.ofNat (prod % (2 ^ 64))) (UInt64.ofNat (prod / (2 ^ 64))))
    | _, _ => .error .typeMismatch
  | .opLogicalOr _ resId aId bId =>
    match regs aId.toNat, regs bId.toNat with
    | .vBool a, .vBool b => .ok (resId.toNat, .vBool (a || b))
    | _, _ => .error .typeMismatch
  | .opLogicalAnd _ resId aId bId =>
    match regs aId.toNat, regs bId.toNat with
    | .vBool a, .vBool b => .ok (resId.toNat, .vBool (a && b))
    | _, _ => .error .typeMismatch
  | .opLogicalNot _ resId aId =>
    match regs aId.toNat with
    | .vBool a => .ok (resId.toNat, .vBool (!a))
    | _ => .error .typeMismatch
  | .opSelect _ resId condId tId fId =>
    match regs condId.toNat, regs tId.toNat, regs fId.toNat with
    | .vBool c, .vU32 t, .vU32 f => .ok (resId.toNat, .vU32 (if c then t else f))
    | .vBool c, .vU64 t, .vU64 f => .ok (resId.toNat, .vU64 (if c then t else f))
    | _, _, _ => .error .typeMismatch
  | .opIEqual _ resId aId bId =>
    match regs aId.toNat, regs bId.toNat with
    | .vU32 a, .vU32 b => .ok (resId.toNat, .vBool (a == b))
    | .vU64 a, .vU64 b => .ok (resId.toNat, .vBool (a == b))
    | _, _ => .error .typeMismatch
  | .opINotEqual _ resId aId bId =>
    match regs aId.toNat, regs bId.toNat with
    | .vU32 a, .vU32 b => .ok (resId.toNat, .vBool (a != b))
    | .vU64 a, .vU64 b => .ok (resId.toNat, .vBool (a != b))
    | _, _ => .error .typeMismatch
  | .opUGreaterThan _ resId aId bId =>
    match regs aId.toNat, regs bId.toNat with
    | .vU32 a, .vU32 b => .ok (resId.toNat, .vBool (decide (b.toNat < a.toNat)))
    | .vU64 a, .vU64 b => .ok (resId.toNat, .vBool (decide (b.toNat < a.toNat)))
    | _, _ => .error .typeMismatch
  | .opUGreaterThanEqual _ resId aId bId =>
    match regs aId.toNat, regs bId.toNat with
    | .vU32 a, .vU32 b => .ok (resId.toNat, .vBool (decide (b.toNat ≤ a.toNat)))
    | .vU64 a, .vU64 b => .ok (resId.toNat, .vBool (decide (b.toNat ≤ a.toNat)))
    | _, _ => .error .typeMismatch
  | .opULessThan _ resId aId bId =>
    match regs aId.toNat, regs bId.toNat with
    | .vU32 a, .vU32 b => .ok (resId.toNat, .vBool (decide (a.toNat < b.toNat)))
    | .vU64 a, .vU64 b => .ok (resId.toNat, .vBool (decide (a.toNat < b.toNat)))
    | _, _ => .error .typeMismatch
  | .opULessThanEqual _ resId aId bId =>
    match regs aId.toNat, regs bId.toNat with
    | .vU32 a, .vU32 b => .ok (resId.toNat, .vBool (decide (a.toNat ≤ b.toNat)))
    | .vU64 a, .vU64 b => .ok (resId.toNat, .vBool (decide (a.toNat ≤ b.toNat)))
    | _, _ => .error .typeMismatch
  | .opShiftRightLogical _ resId baseId shId =>
    match regs baseId.toNat, regs shId.toNat with
    | .vU32 a, .vU32 sh => .ok (resId.toNat, .vU32 (UInt32.ofNat (a.toNat / 2 ^ (sh.toNat % 32))))
    | .vU64 a, .vU64 sh => .ok (resId.toNat, .vU64 (UInt64.ofNat (a.toNat / 2 ^ (sh.toNat % 64))))
    | _, _ => .error .typeMismatch
  | .opShiftLeftLogical _ resId baseId shId =>
    match regs baseId.toNat, regs shId.toNat with
    | .vU32 a, .vU32 sh =>
      .ok (resId.toNat, .vU32 (UInt32.ofNat ((a.toNat * 2 ^ (sh.toNat % 32)) % 4294967296)))
    | .vU64 a, .vU64 sh =>
      .ok (resId.toNat, .vU64 (UInt64.ofNat ((a.toNat * 2 ^ (sh.toNat % 64)) % (2 ^ 64))))
    | _, _ => .error .typeMismatch
  | .opBitwiseOr _ resId aId bId =>
    match regs aId.toNat, regs bId.toNat with
    | .vU32 a, .vU32 b => .ok (resId.toNat, .vU32 (a ||| b))
    | .vU64 a, .vU64 b => .ok (resId.toNat, .vU64 (a ||| b))
    | _, _ => .error .typeMismatch
  | .opBitwiseXor _ resId aId bId =>
    match regs aId.toNat, regs bId.toNat with
    | .vU32 a, .vU32 b => .ok (resId.toNat, .vU32 (a ^^^ b))
    | .vU64 a, .vU64 b => .ok (resId.toNat, .vU64 (a ^^^ b))
    | _, _ => .error .typeMismatch
  | .opBitwiseAnd _ resId aId bId =>
    match regs aId.toNat, regs bId.toNat with
    | .vU32 a, .vU32 b => .ok (resId.toNat, .vU32 (a &&& b))
    | .vU64 a, .vU64 b => .ok (resId.toNat, .vU64 (a &&& b))
    | _, _ => .error .typeMismatch
  | .opNot _ resId aId =>
    match regs aId.toNat with
    | .vU32 a => .ok (resId.toNat, .vU32 (~~~a))
    | .vU64 a => .ok (resId.toNat, .vU64 (~~~a))
    | _ => .error .typeMismatch
  | _ => .error .typeMismatch

/-- Apply a single lane's `OpStore` to `GpuMemState` with `64 KiB` LDS bounds enforcement. -/
def applyLaneStore (mem : GpuMemState) (regs : Nat → SpirvVal) (ptrId valId : UInt32) :
    Except SimtExecError GpuMemState :=
  match regs ptrId.toNat, regs valId.toNat with
  | .vPtr .workgroup _ elemIdx .w32, .vU32 v =>
    if elemIdx < ldsCapacityDwords then
      .ok { mem with lds := writeFn mem.lds elemIdx v }
    else
      .error (.ldsOutOfBounds elemIdx)
  | .vPtr .workgroup _ elemIdx .w64, .vU64 v =>
    if 2 * elemIdx + 1 < ldsCapacityDwords then
      .ok { mem with lds := writeU64Dwords mem.lds elemIdx v }
    else
      .error (.ldsOutOfBounds (2 * elemIdx + 1))
  | .vPtr .storageBuffer binding elemIdx .w32, .vU32 v =>
    .ok { mem with ssbo := writeSsboDword mem.ssbo binding elemIdx v }
  | .vPtr .storageBuffer binding elemIdx .w64, .vU64 v =>
    .ok { mem with ssbo := writeSsboU64 mem.ssbo binding elemIdx v }
  | _, _ => .error .typeMismatch

/-- State of one Wave32 subgroup (`32` SIMD lanes + `EXEC_LO` active mask + barrier latch). -/
structure Wave32State where
  pc : Nat
  execMask : Nat → Bool
  laneRegs : Nat → Nat → SpirvVal
  atBarrier : Bool

def allActive32 : Nat → Bool := fun lane => decide (lane < wave32Lanes)

/-- Execute all active lanes `0 .. k - 1` of a Wave32 store instruction sequentially across active lanes. -/
def execWaveStoreLanes (execMask : Nat → Bool) (laneRegs : Nat → Nat → SpirvVal)
    (ptrId valId : UInt32) : Nat → GpuMemState → Except SimtExecError GpuMemState
  | 0, mem => .ok mem
  | k + 1, mem =>
    match execWaveStoreLanes execMask laneRegs ptrId valId k mem with
    | .error e => .error e
    | .ok mem' =>
      if execMask k then applyLaneStore mem' (laneRegs k) ptrId valId else .ok mem'

/-- Check that all active lanes `0 .. k - 1` evaluate a pure instruction without runtime error. -/
def checkWavePureLanesErr (env : SpirvModuleEnv) (mem : GpuMemState) (execMask : Nat → Bool)
    (laneRegs : Nat → Nat → SpirvVal) (inst : SpirvInst) : Nat → Option SimtExecError
  | 0 => none
  | k + 1 =>
    match checkWavePureLanesErr env mem execMask laneRegs inst k with
    | some e => some e
    | none =>
      if execMask k then
        match evalLanePureInst env mem (laneRegs k) inst with
        | .error e => some e
        | .ok _ => none
      else
        none

/-- Parallel SIMT per-lane pure register update (`O(1)` lookup depth per lane, zero cross-lane wrapper chain). -/
def stepLanePureRegs (env : SpirvModuleEnv) (mem : GpuMemState) (execMask : Nat → Bool)
    (laneRegs : Nat → Nat → SpirvVal) (inst : SpirvInst) (lane : Nat) : Nat → SpirvVal :=
  if lane < wave32Lanes ∧ execMask lane = true then
    match evalLanePureInst env mem (laneRegs lane) inst with
    | .ok (dst, v) => writeFn (laneRegs lane) dst v
    | .error _ => laneRegs lane
  else
    laneRegs lane

/-- Evaluate a pure instruction across all active lanes `0 .. k - 1` of a Wave32 subgroup. -/
def evalWavePureLanes (env : SpirvModuleEnv) (mem : GpuMemState) (execMask : Nat → Bool)
    (laneRegs : Nat → Nat → SpirvVal) (inst : SpirvInst) (k : Nat) :
    Except SimtExecError (Nat → Nat → SpirvVal) :=
  match checkWavePureLanesErr env mem execMask laneRegs inst k with
  | some e => .error e
  | none => .ok (stepLanePureRegs env mem execMask laneRegs inst)

/-- Step one Wave32 subgroup by one instruction inside a `SpirvInst` sequence.
    When a wave reaches `OpControlBarrier(.workgroup, .workgroup, spirvSemWorkgroupAcqRel)`,
    it sets `atBarrier := true` and blocks until all waves in the workgroup arrive. -/
def stepWave32One (env : SpirvModuleEnv) (prog : List SpirvInst) (wSt : Wave32State)
    (mem : GpuMemState) : Except SimtExecError (Wave32State × GpuMemState) :=
  if wSt.atBarrier then
    .ok (wSt, mem)
  else
    match prog[wSt.pc]? with
    | none => .ok (wSt, mem)
    | some (.opControlBarrier es ms sem) =>
      if isWorkgroupAcqRelBarrier env es ms sem then
        .ok ({ wSt with atBarrier := true }, mem)
      else
        .error .typeMismatch
    | some (.opStore ptrId valId) =>
      match execWaveStoreLanes wSt.execMask wSt.laneRegs ptrId valId wave32Lanes mem with
      | .error e => .error e
      | .ok mem' => .ok ({ wSt with pc := wSt.pc + 1 }, mem')
    | some (.opLabel _) =>
      .ok ({ wSt with pc := wSt.pc + 1 }, mem)
    | some inst =>
      match evalWavePureLanes env mem wSt.execMask wSt.laneRegs inst wave32Lanes with
      | .error e => .error e
      | .ok regs' => .ok ({ wSt with pc := wSt.pc + 1, laneRegs := regs' }, mem)

/-- Multi-wave workgroup execution state: all `numWaves` Wave32 states + shared `64 KiB` LDS & SSBOs. -/
structure WorkgroupExecState where
  waves : Nat → Wave32State
  mem : GpuMemState

def initWorkgroupExecState (env : SpirvModuleEnv) (cfg : WorkgroupConfig) (initMem : GpuMemState) :
    WorkgroupExecState :=
  { waves := fun w =>
      { pc := 0
        execMask := allActive32
        laneRegs := fun lane => initLaneRegs env cfg w lane
        atBarrier := false }
    mem := initMem }

/-- Step wave `w` once inside the multi-wave workgroup (no-op if `w ≥ cfg.numWaves`). -/
def stepWorkgroupWave (env : SpirvModuleEnv) (cfg : WorkgroupConfig) (prog : List SpirvInst)
    (w : Nat) (st : WorkgroupExecState) : Except SimtExecError WorkgroupExecState :=
  if w < cfg.numWaves then
    match stepWave32One env prog (st.waves w) st.mem with
    | .error e => .error e
    | .ok (wSt', mem') => .ok { waves := writeFn st.waves w wSt', mem := mem' }
  else
    .ok st

/-- Execute an arbitrary cross-wave instruction-interleaving schedule `sched : List Nat` within one
    barrier epoch. -/
def runInterleavedSchedule (env : SpirvModuleEnv) (cfg : WorkgroupConfig) (prog : List SpirvInst) :
    List Nat → WorkgroupExecState → Except SimtExecError WorkgroupExecState
  | [], st => .ok st
  | w :: ws, st =>
    match stepWorkgroupWave env cfg prog w st with
    | .error e => .error e
    | .ok st' => runInterleavedSchedule env cfg prog ws st'

/-- Check whether all `numWaves` Wave32 subgroups have arrived at `OpControlBarrier`. -/
def allWavesAtBarrier (cfg : WorkgroupConfig) (waves : Nat → Wave32State) : Bool :=
  (List.range cfg.numWaves).all fun w => (waves w).atBarrier

/-- Lockstep workgroup-wide `OpControlBarrier` release: advances every wave past the barrier ONLY
    when all `numWaves` waves in the workgroup have reached the barrier, preserving 100% of shared
    `Workgroup` LDS and global `StorageBuffer` writes! -/
def releaseWorkgroupBarrier (cfg : WorkgroupConfig) (st : WorkgroupExecState) :
    Except SimtExecError WorkgroupExecState :=
  if allWavesAtBarrier cfg st.waves then
    .ok { waves := fun w =>
            if w < cfg.numWaves then
              let ws := st.waves w
              { ws with pc := ws.pc + 1, atBarrier := false }
            else
              st.waves w
          mem := st.mem }
  else
    .error .barrierDivergence

/-- A barrier-segmented kernel consists of barrier-free epochs `epochs : List (List SpirvInst)`,
    where adjacent epochs are separated by `OpControlBarrier(.workgroup, .workgroup, 0x108)`. -/
def BarrierEpoch := List SpirvInst

/-- Run one barrier epoch under wave schedule `sched : List Nat` (every wave steps through `epoch`
    and arrives at the trailing `OpControlBarrier`). -/
def runOneBarrierEpoch (env : SpirvModuleEnv) (cfg : WorkgroupConfig) (epoch : List SpirvInst)
    (hasTrailingBarrier : Bool) (sched : List Nat) (st : WorkgroupExecState) :
    Except SimtExecError WorkgroupExecState :=
  let prog := if hasTrailingBarrier then
      epoch ++ [.opControlBarrier SpirvScope.workgroup.toWord SpirvScope.workgroup.toWord spirvSemWorkgroupAcqRel]
    else
      epoch
  let resetWaves : WorkgroupExecState :=
    { waves := fun w => { (st.waves w) with pc := 0, atBarrier := false }, mem := st.mem }
  match runInterleavedSchedule env cfg prog sched resetWaves with
  | .error e => .error e
  | .ok stAfter =>
    if hasTrailingBarrier then releaseWorkgroupBarrier cfg stAfter else .ok stAfter

/-- Execute a multi-epoch multi-wave workgroup kernel across per-epoch schedules `scheds`.
    Shared `Workgroup` LDS (`st.mem.lds`) persists intact across ALL epochs and ALL waves! -/
def runMultiWaveEpochs (env : SpirvModuleEnv) (cfg : WorkgroupConfig) :
    List (List SpirvInst) → List (List Nat) → WorkgroupExecState →
    Except SimtExecError WorkgroupExecState
  | [], _, st => .ok st
  | [lastEpoch], scheds, st =>
    runOneBarrierEpoch env cfg lastEpoch false (scheds.headD []) st
  | ep :: nextEp :: rest, scheds, st =>
    match runOneBarrierEpoch env cfg ep true (scheds.headD []) st with
    | .error e => .error e
    | .ok st' => runMultiWaveEpochs env cfg (nextEp :: rest) (scheds.tail) st'

/-- Canonical wave schedule for an epoch of length `L` (with optional +1 barrier instruction):
    runs Wave `0` for `steps` instructions, then Wave `1`, ..., up to Wave `numWaves - 1`. -/
def canonicalEpochSchedule (numWaves steps : Nat) : List Nat :=
  (List.range numWaves).flatMap (fun w => List.replicate steps w)

/-! ## §3. Compositional `Faial` MAP Data-Race Freedom & `SIMT-CT` Side-Channel Immunity -/

/-- Per-thread (`tid = wave * 32 + lane`) memory footprint of one barrier epoch (`Faial` MAP). -/
structure EpochAccessProtocol where
  ldsRead : Nat → Nat → Bool
  ldsWrite : Nat → Nat → Bool
  ssboRead : Nat → Nat → Nat → Bool
  ssboWrite : Nat → Nat → Nat → Bool

/-- **`Faial` Memory-Access-Protocol Data-Race Freedom (`FaialMapRaceFree`)**:
    Within the barrier epoch, for every pair of distinct threads `t₁ ≠ t₂` in the workgroup,
    `t₁`'s shared `Workgroup` LDS and global `StorageBuffer` write sets are strictly disjoint
    from `t₂`'s write AND read sets (`W(t₁) ∩ (W(t₂) ∪ R(t₂)) = ∅`). -/
def FaialMapRaceFree (numThreads : Nat) (proto : EpochAccessProtocol) : Prop :=
  ∀ t₁ t₂ : Nat, t₁ < numThreads → t₂ < numThreads → t₁ ≠ t₂ →
    (∀ a : Nat, proto.ldsWrite t₁ a = true →
      proto.ldsWrite t₂ a = false ∧ proto.ldsRead t₂ a = false) ∧
    (∀ b a : Nat, proto.ssboWrite t₁ b a = true →
      proto.ssboWrite t₂ b a = false ∧ proto.ssboRead t₂ b a = false)

/-- Two `GpuMemState`s agree on all locations in wave `w`'s read/write footprint under `proto`. -/
def MemAgreesOnWaveFootprint (w : Nat) (proto : EpochAccessProtocol) (m₁ m₂ : GpuMemState) : Prop :=
  m₁.pushConsts = m₂.pushConsts ∧
  (∀ lane a : Nat, lane < wave32Lanes →
    (proto.ldsRead (w * wave32Lanes + lane) a = true ∨
     proto.ldsWrite (w * wave32Lanes + lane) a = true) →
    m₁.lds a = m₂.lds a) ∧
  (∀ lane b a : Nat, lane < wave32Lanes →
    (proto.ssboRead (w * wave32Lanes + lane) b a = true ∨
     proto.ssboWrite (w * wave32Lanes + lane) b a = true) →
    m₁.ssbo b a = m₂.ssbo b a)

/-- Per-wave state invariant lifted across all `numWaves` Wave32 subgroups of a workgroup. -/
def AllWavesInv (cfg : WorkgroupConfig) (waveInv : Nat → Wave32State → Prop)
    (st : WorkgroupExecState) : Prop :=
  ∀ w : Nat, w < cfg.numWaves → waveInv w (st.waves w)

/-- Semantic soundness of an `EpochAccessProtocol` on a program `prog` under wave invariant `waveInv`:
    1. `inv_preserved` & `step_total`: reachable wave states step cleanly and preserve `waveInv`;
    2. `read_locality`: wave `w`'s step outcome (`wSt'`) and write footprint depend ONLY on `w`'s
       footprint, and wave `w` modifies ONLY addresses inside `w`'s write set (`ldsWrite`, `ssboWrite`). -/
structure WaveRespectsProtocol (env : SpirvModuleEnv) (cfg : WorkgroupConfig)
    (prog : List SpirvInst) (waveInv : Nat → Wave32State → Prop)
    (proto : EpochAccessProtocol) : Prop where
  inv_preserved :
    ∀ (w : Nat) (_hw : w < cfg.numWaves) (wSt wSt' : Wave32State) (m m' : GpuMemState),
      waveInv w wSt →
      stepWave32One env prog wSt m = .ok (wSt', m') →
      waveInv w wSt'
  step_total :
    ∀ (w : Nat) (_hw : w < cfg.numWaves) (wSt : Wave32State) (m : GpuMemState),
      waveInv w wSt →
      ∃ wSt' m', stepWave32One env prog wSt m = .ok (wSt', m')
  read_locality :
    ∀ (w : Nat) (_hw : w < cfg.numWaves) (wSt : Wave32State),
      waveInv w wSt →
      ∀ (m₁ m₂ : GpuMemState),
        MemAgreesOnWaveFootprint w proto m₁ m₂ →
        (match stepWave32One env prog wSt m₁, stepWave32One env prog wSt m₂ with
         | .error e₁, .error e₂ => e₁ = e₂
         | .ok (wSt₁, m₁'), .ok (wSt₂, m₂') =>
           wSt₁ = wSt₂ ∧
           m₁'.pushConsts = m₁.pushConsts ∧
           m₂'.pushConsts = m₂.pushConsts ∧
           (∀ a : Nat,
             (∃ lane < wave32Lanes, proto.ldsWrite (w * wave32Lanes + lane) a = true) →
               m₁'.lds a = m₂'.lds a) ∧
           (∀ a : Nat,
             (∀ lane < wave32Lanes, proto.ldsWrite (w * wave32Lanes + lane) a = false) →
               m₁'.lds a = m₁.lds a ∧ m₂'.lds a = m₂.lds a) ∧
           (∀ b a : Nat,
             (∃ lane < wave32Lanes, proto.ssboWrite (w * wave32Lanes + lane) b a = true) →
               m₁'.ssbo b a = m₂'.ssbo b a) ∧
           (∀ b a : Nat,
             (∀ lane < wave32Lanes, proto.ssboWrite (w * wave32Lanes + lane) b a = false) →
               m₁'.ssbo b a = m₁.ssbo b a ∧ m₂'.ssbo b a = m₂.ssbo b a)
         | _, _ => False)

private theorem wave_threads_ne {w₁ w₂ l₁ l₂ : Nat} (hw : w₁ ≠ w₂)
    (hl₁ : l₁ < wave32Lanes) (hl₂ : l₂ < wave32Lanes) :
    w₁ * wave32Lanes + l₁ ≠ w₂ * wave32Lanes + l₂ := by
  unfold wave32Lanes at *
  omega

theorem stepWorkgroupWave_total_and_inv {env : SpirvModuleEnv} {cfg : WorkgroupConfig}
    {prog : List SpirvInst} {waveInv : Nat → Wave32State → Prop} {proto : EpochAccessProtocol}
    (hResp : WaveRespectsProtocol env cfg prog waveInv proto)
    (w : Nat) {st : WorkgroupExecState} (hInv : AllWavesInv cfg waveInv st) :
    ∃ st', stepWorkgroupWave env cfg prog w st = .ok st' ∧ AllWavesInv cfg waveInv st' := by
  unfold stepWorkgroupWave
  by_cases hw : w < cfg.numWaves
  · simp only [hw, ↓reduceIte]
    obtain ⟨wSt', m', hStep⟩ := hResp.step_total w hw (st.waves w) st.mem (hInv w hw)
    refine ⟨{ waves := writeFn st.waves w wSt', mem := m' }, by simp [hStep], ?_⟩
    intro w' hw'
    unfold writeFn
    by_cases hww : w' = w
    · subst hww; simp [hResp.inv_preserved w' hw' _ _ _ _ (hInv w' hw') hStep]
    · simp [hww, hInv w' hw']
  · simp [hw]; exact hInv

/-- **Cross-Wave Diamond Commutativity Lemma (`stepWorkgroupWave_comm`)**:
    Under `FaialMapRaceFree`, stepping two distinct Wave32 subgroups `w₁ ≠ w₂` strictly commutes! -/
theorem stepWorkgroupWave_comm {env : SpirvModuleEnv} {cfg : WorkgroupConfig}
    {prog : List SpirvInst} {waveInv : Nat → Wave32State → Prop} {proto : EpochAccessProtocol}
    (hResp : WaveRespectsProtocol env cfg prog waveInv proto)
    (hDrf : FaialMapRaceFree cfg.totalThreads proto)
    {w₁ w₂ : Nat} (hne : w₁ ≠ w₂) (st : WorkgroupExecState)
    (hInv : AllWavesInv cfg waveInv st) :
    (stepWorkgroupWave env cfg prog w₁ st >>= stepWorkgroupWave env cfg prog w₂) =
    (stepWorkgroupWave env cfg prog w₂ st >>= stepWorkgroupWave env cfg prog w₁) := by
  by_cases hw₁ : w₁ < cfg.numWaves
  · by_cases hw₂ : w₂ < cfg.numWaves
    · obtain ⟨s₁, hs₁, _⟩ := stepWorkgroupWave_total_and_inv hResp w₁ hInv
      obtain ⟨s₂, hs₂, _⟩ := stepWorkgroupWave_total_and_inv hResp w₂ hInv
      unfold stepWorkgroupWave at hs₁ hs₂ ⊢
      simp only [hw₁, hw₂, ↓reduceIte] at hs₁ hs₂ ⊢
      have hSelf₁ := hResp.read_locality w₁ hw₁ (st.waves w₁) (hInv w₁ hw₁) st.mem st.mem
        ⟨rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
      have hSelf₂ := hResp.read_locality w₂ hw₂ (st.waves w₂) (hInv w₂ hw₂) st.mem st.mem
        ⟨rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
      cases hStep1 : stepWave32One env prog (st.waves w₁) st.mem with
      | error e => rw [hStep1] at hs₁; cases hs₁
      | ok p1 =>
        rcases p1 with ⟨wSt₁, m₁⟩
        cases hStep2 : stepWave32One env prog (st.waves w₂) st.mem with
        | error e => rw [hStep2] at hs₂; cases hs₂
        | ok p2 =>
          rcases p2 with ⟨wSt₂, m₂⟩
          rw [hStep1] at hSelf₁
          rw [hStep2] at hSelf₂
          rcases hSelf₁ with ⟨_, hpc₁, _, _, hNoLds₁, _, hNoSsbo₁⟩
          rcases hSelf₂ with ⟨_, hpc₂, _, _, hNoLds₂, _, hNoSsbo₂⟩
          have hAgree2After1 : MemAgreesOnWaveFootprint w₂ proto st.mem m₁ := by
            refine ⟨hpc₁.symm, ?_, ?_⟩
            · intro l₂ a hl₂ hFoot₂
              have hNoW₁ : ∀ l₁ < wave32Lanes, proto.ldsWrite (w₁ * wave32Lanes + l₁) a = false := by
                intro l₁ hl₁
                cases hW : proto.ldsWrite (w₁ * wave32Lanes + l₁) a with
                | false => rfl
                | true =>
                  have ht₁ : w₁ * wave32Lanes + l₁ < cfg.totalThreads := by
                    unfold WorkgroupConfig.totalThreads wave32Lanes at *; omega
                  have ht₂ : w₂ * wave32Lanes + l₂ < cfg.totalThreads := by
                    unfold WorkgroupConfig.totalThreads wave32Lanes at *; omega
                  have hDisj := (hDrf _ _ ht₁ ht₂ (wave_threads_ne hne hl₁ hl₂)).1 a hW
                  rcases hFoot₂ with hR | hWr
                  · rw [hDisj.2] at hR; cases hR
                  · rw [hDisj.1] at hWr; cases hWr
              exact (hNoLds₁ a hNoW₁).1.symm
            · intro l₂ b a hl₂ hFoot₂
              have hNoW₁ : ∀ l₁ < wave32Lanes, proto.ssboWrite (w₁ * wave32Lanes + l₁) b a = false := by
                intro l₁ hl₁
                cases hW : proto.ssboWrite (w₁ * wave32Lanes + l₁) b a with
                | false => rfl
                | true =>
                  have ht₁ : w₁ * wave32Lanes + l₁ < cfg.totalThreads := by
                    unfold WorkgroupConfig.totalThreads wave32Lanes at *; omega
                  have ht₂ : w₂ * wave32Lanes + l₂ < cfg.totalThreads := by
                    unfold WorkgroupConfig.totalThreads wave32Lanes at *; omega
                  have hDisj := (hDrf _ _ ht₁ ht₂ (wave_threads_ne hne hl₁ hl₂)).2 b a hW
                  rcases hFoot₂ with hR | hWr
                  · rw [hDisj.2] at hR; cases hR
                  · rw [hDisj.1] at hWr; cases hWr
              exact (hNoSsbo₁ b a hNoW₁).1.symm
          have hAgree1After2 : MemAgreesOnWaveFootprint w₁ proto st.mem m₂ := by
            refine ⟨hpc₂.symm, ?_, ?_⟩
            · intro l₁ a hl₁ hFoot₁
              have hNoW₂ : ∀ l₂ < wave32Lanes, proto.ldsWrite (w₂ * wave32Lanes + l₂) a = false := by
                intro l₂ hl₂
                cases hW : proto.ldsWrite (w₂ * wave32Lanes + l₂) a with
                | false => rfl
                | true =>
                  have ht₁ : w₁ * wave32Lanes + l₁ < cfg.totalThreads := by
                    unfold WorkgroupConfig.totalThreads wave32Lanes at *; omega
                  have ht₂ : w₂ * wave32Lanes + l₂ < cfg.totalThreads := by
                    unfold WorkgroupConfig.totalThreads wave32Lanes at *; omega
                  have hDisj := (hDrf _ _ ht₂ ht₁ (wave_threads_ne hne.symm hl₂ hl₁)).1 a hW
                  rcases hFoot₁ with hR | hWr
                  · rw [hDisj.2] at hR; cases hR
                  · rw [hDisj.1] at hWr; cases hWr
              exact (hNoLds₂ a hNoW₂).1.symm
            · intro l₁ b a hl₁ hFoot₁
              have hNoW₂ : ∀ l₂ < wave32Lanes, proto.ssboWrite (w₂ * wave32Lanes + l₂) b a = false := by
                intro l₂ hl₂
                cases hW : proto.ssboWrite (w₂ * wave32Lanes + l₂) b a with
                | false => rfl
                | true =>
                  have ht₁ : w₁ * wave32Lanes + l₁ < cfg.totalThreads := by
                    unfold WorkgroupConfig.totalThreads wave32Lanes at *; omega
                  have ht₂ : w₂ * wave32Lanes + l₂ < cfg.totalThreads := by
                    unfold WorkgroupConfig.totalThreads wave32Lanes at *; omega
                  have hDisj := (hDrf _ _ ht₂ ht₁ (wave_threads_ne hne.symm hl₂ hl₁)).2 b a hW
                  rcases hFoot₁ with hR | hWr
                  · rw [hDisj.2] at hR; cases hR
                  · rw [hDisj.1] at hWr; cases hWr
              exact (hNoSsbo₂ b a hNoW₂).1.symm
          have hLoc2 := hResp.read_locality w₂ hw₂ (st.waves w₂) (hInv w₂ hw₂) st.mem m₁ hAgree2After1
          have hLoc1 := hResp.read_locality w₁ hw₁ (st.waves w₁) (hInv w₁ hw₁) st.mem m₂ hAgree1After2
          rw [hStep2] at hLoc2
          rw [hStep1] at hLoc1
          simp only [Bind.bind, Except.bind,
            writeFn_other st.waves _ hne.symm, writeFn_other st.waves _ hne]
          cases hStep2_after1 : stepWave32One env prog (st.waves w₂) m₁ with
          | error e => rw [hStep2_after1] at hLoc2; cases hLoc2
          | ok p12 =>
            rcases p12 with ⟨wSt₂', m₁₂⟩
            cases hStep1_after2 : stepWave32One env prog (st.waves w₁) m₂ with
            | error e => rw [hStep1_after2] at hLoc1; cases hLoc1
            | ok p21 =>
              rcases p21 with ⟨wSt₁', m₂₁⟩
              rw [hStep2_after1] at hLoc2
              rw [hStep1_after2] at hLoc1
              rcases hLoc2 with ⟨hwSt₂Eq, _, hpc₁₂, hW₂Lds, hNoW₂Lds, hW₂Ssbo, hNoW₂Ssbo⟩
              rcases hLoc1 with ⟨hwSt₁Eq, _, hpc₂₁, hW₁Lds, hNoW₁Lds, hW₁Ssbo, hNoW₁Ssbo⟩
              subst hwSt₂Eq; subst hwSt₁Eq
              dsimp only
              have hWavesEq := writeFn_comm st.waves wSt₁ wSt₂ hne
              have hMemEq : m₁₂ = m₂₁ := by
                cases m₁₂ with | mk lds12 ssbo12 pc12 =>
                cases m₂₁ with | mk lds21 ssbo21 pc21 =>
                simp only at hpc₁₂ hpc₂₁ hW₂Lds hNoW₂Lds hW₂Ssbo hNoW₂Ssbo hW₁Lds hNoW₁Lds hW₁Ssbo hNoW₁Ssbo
                have hLdsEq : lds12 = lds21 := by
                  funext a
                  by_cases hex₂ : ∃ l₂ < wave32Lanes, proto.ldsWrite (w₂ * wave32Lanes + l₂) a = true
                  · obtain ⟨l₂, hl₂, hw₂a⟩ := hex₂
                    have hNoW₁a : ∀ l₁ < wave32Lanes, proto.ldsWrite (w₁ * wave32Lanes + l₁) a = false := by
                      intro l₁ hl₁
                      have ht₁ : w₁ * wave32Lanes + l₁ < cfg.totalThreads := by
                        unfold WorkgroupConfig.totalThreads wave32Lanes at *; omega
                      have ht₂ : w₂ * wave32Lanes + l₂ < cfg.totalThreads := by
                        unfold WorkgroupConfig.totalThreads wave32Lanes at *; omega
                      exact (hDrf _ _ ht₂ ht₁ (wave_threads_ne hne.symm hl₂ hl₁)).1 a hw₂a |>.1
                    rw [← hW₂Lds a ⟨l₂, hl₂, hw₂a⟩, (hNoW₁Lds a hNoW₁a).2]
                  · have hAll₂ : ∀ l₂ < wave32Lanes, proto.ldsWrite (w₂ * wave32Lanes + l₂) a = false := by
                      intro l₂ hl₂
                      cases h : proto.ldsWrite (w₂ * wave32Lanes + l₂) a with
                      | false => rfl
                      | true => exact False.elim (hex₂ ⟨l₂, hl₂, h⟩)
                    by_cases hex₁ : ∃ l₁ < wave32Lanes, proto.ldsWrite (w₁ * wave32Lanes + l₁) a = true
                    · rw [(hNoW₂Lds a hAll₂).2, hW₁Lds a hex₁]
                    · have hAll₁ : ∀ l₁ < wave32Lanes, proto.ldsWrite (w₁ * wave32Lanes + l₁) a = false := by
                        intro l₁ hl₁
                        cases h : proto.ldsWrite (w₁ * wave32Lanes + l₁) a with
                        | false => rfl
                        | true => exact False.elim (hex₁ ⟨l₁, hl₁, h⟩)
                      rw [(hNoW₂Lds a hAll₂).2, (hNoW₁Lds a hAll₁).2,
                          (hNoLds₁ a hAll₁).1, (hNoLds₂ a hAll₂).1]
                have hSsboEq : ssbo12 = ssbo21 := by
                  funext b a
                  by_cases hex₂ : ∃ l₂ < wave32Lanes, proto.ssboWrite (w₂ * wave32Lanes + l₂) b a = true
                  · obtain ⟨l₂, hl₂, hw₂a⟩ := hex₂
                    have hNoW₁a : ∀ l₁ < wave32Lanes, proto.ssboWrite (w₁ * wave32Lanes + l₁) b a = false := by
                      intro l₁ hl₁
                      have ht₁ : w₁ * wave32Lanes + l₁ < cfg.totalThreads := by
                        unfold WorkgroupConfig.totalThreads wave32Lanes at *; omega
                      have ht₂ : w₂ * wave32Lanes + l₂ < cfg.totalThreads := by
                        unfold WorkgroupConfig.totalThreads wave32Lanes at *; omega
                      exact (hDrf _ _ ht₂ ht₁ (wave_threads_ne hne.symm hl₂ hl₁)).2 b a hw₂a |>.1
                    rw [← hW₂Ssbo b a ⟨l₂, hl₂, hw₂a⟩, (hNoW₁Ssbo b a hNoW₁a).2]
                  · have hAll₂ : ∀ l₂ < wave32Lanes, proto.ssboWrite (w₂ * wave32Lanes + l₂) b a = false := by
                      intro l₂ hl₂
                      cases h : proto.ssboWrite (w₂ * wave32Lanes + l₂) b a with
                      | false => rfl
                      | true => exact False.elim (hex₂ ⟨l₂, hl₂, h⟩)
                    by_cases hex₁ : ∃ l₁ < wave32Lanes, proto.ssboWrite (w₁ * wave32Lanes + l₁) b a = true
                    · rw [(hNoW₂Ssbo b a hAll₂).2, hW₁Ssbo b a hex₁]
                    · have hAll₁ : ∀ l₁ < wave32Lanes, proto.ssboWrite (w₁ * wave32Lanes + l₁) b a = false := by
                        intro l₁ hl₁
                        cases h : proto.ssboWrite (w₁ * wave32Lanes + l₁) b a with
                        | false => rfl
                        | true => exact False.elim (hex₁ ⟨l₁, hl₁, h⟩)
                      rw [(hNoW₂Ssbo b a hAll₂).2, (hNoW₁Ssbo b a hAll₁).2,
                          (hNoSsbo₁ b a hAll₁).1, (hNoSsbo₂ b a hAll₂).1]
                have hPcEq : pc12 = pc21 := by
                  rw [hpc₁₂, hpc₁, hpc₂₁, hpc₂]
                rw [hLdsEq, hSsboEq, hPcEq]
              rw [hWavesEq, hMemEq]
    · unfold stepWorkgroupWave
      simp only [Bind.bind, Except.bind, hw₁, hw₂, ↓reduceIte]
      cases stepWave32One env prog (st.waves w₁) st.mem with
      | error _ => rfl
      | ok _ => simp
  · by_cases hw₂ : w₂ < cfg.numWaves
    · unfold stepWorkgroupWave
      simp only [Bind.bind, Except.bind, hw₁, hw₂, ↓reduceIte]
      cases stepWave32One env prog (st.waves w₂) st.mem with
      | error _ => rfl
      | ok _ => simp
    · unfold stepWorkgroupWave
      simp [Bind.bind, Except.bind, hw₁, hw₂]

/-- Adjacent-swap equivalence of wave schedules (`w₁ :: w₂ :: ws ~ w₂ :: w₁ :: ws` for `w₁ ≠ w₂`). -/
inductive SchedPerm : List Nat → List Nat → Prop where
  | refl (s : List Nat) : SchedPerm s s
  | swap {w₁ w₂ : Nat} (hne : w₁ ≠ w₂) (rest : List Nat) :
      SchedPerm (w₁ :: w₂ :: rest) (w₂ :: w₁ :: rest)
  | cons (w : Nat) {s₁ s₂ : List Nat} : SchedPerm s₁ s₂ → SchedPerm (w :: s₁) (w :: s₂)
  | trans {s₁ s₂ s₃ : List Nat} : SchedPerm s₁ s₂ → SchedPerm s₂ s₃ → SchedPerm s₁ s₃

/-- **Multi-Wave Schedule Confluence Theorem (`multiWave_schedule_confluence`)**:
    Under `FaialMapRaceFree` and `WaveRespectsProtocol`, ANY two valid cross-wave instruction
    schedules related by arbitrary non-interfering wave reorderings (`SchedPerm`) produce the
    **exact same** multi-wave workgroup state (shared `64 KiB` LDS + global `StorageBuffer` +
    all Wave32 registers)! -/
theorem multiWave_schedule_confluence {env : SpirvModuleEnv} {cfg : WorkgroupConfig}
    {prog : List SpirvInst} {waveInv : Nat → Wave32State → Prop} {proto : EpochAccessProtocol}
    (hResp : WaveRespectsProtocol env cfg prog waveInv proto)
    (hDrf : FaialMapRaceFree cfg.totalThreads proto)
    {sched₁ sched₂ : List Nat} (hPerm : SchedPerm sched₁ sched₂) :
    ∀ st : WorkgroupExecState,
      AllWavesInv cfg waveInv st →
      runInterleavedSchedule env cfg prog sched₁ st =
      runInterleavedSchedule env cfg prog sched₂ st := by
  induction hPerm with
  | refl _ => intro _ _; rfl
  | @swap w₁ w₂ hne rest =>
    intro st hInv
    have hComm := stepWorkgroupWave_comm hResp hDrf hne st hInv
    obtain ⟨s₁, hs₁, hInv₁⟩ := stepWorkgroupWave_total_and_inv hResp w₁ hInv
    obtain ⟨s₂, hs₂, hInv₂⟩ := stepWorkgroupWave_total_and_inv hResp w₂ hInv
    obtain ⟨s₁₂, hs₁₂, _⟩ := stepWorkgroupWave_total_and_inv hResp w₂ hInv₁
    obtain ⟨s₂₁, hs₂₁, _⟩ := stepWorkgroupWave_total_and_inv hResp w₁ hInv₂
    dsimp only [runInterleavedSchedule]
    rw [hs₁, hs₂]
    dsimp only [runInterleavedSchedule]
    rw [hs₁₂, hs₂₁]
    have hEq12 : (Except.ok s₁₂ : Except SimtExecError WorkgroupExecState) = .ok s₂₁ := by
      simpa [Bind.bind, Except.bind, hs₁, hs₂, hs₁₂, hs₂₁] using hComm
    injection hEq12 with hStateEq
    rw [hStateEq]
  | cons w _ ih =>
    intro st hInv
    dsimp only [runInterleavedSchedule]
    obtain ⟨st', hst', hInv'⟩ := stepWorkgroupWave_total_and_inv hResp w hInv
    rw [hst']
    exact ih st' hInv'
  | trans _ _ ih₁ ih₂ =>
    intro st hInv
    exact (ih₁ st hInv).trans (ih₂ st hInv)

/-- Any schedule `sched` with identical per-wave step counts (`∀ w, sched.count w = ...`) reduces
    by `SchedPerm` to grouping waves in canonical order `0, 1, ..., numWaves - 1`! -/
private theorem schedPerm_bubble_front (w : Nat) :
    ∀ (xs ys : List Nat),
      (∀ x ∈ xs, x ≠ w) →
      SchedPerm (xs ++ w :: ys) (w :: xs ++ ys)
  | [], _, _ => .refl _
  | x :: xs, ys, hne =>
    have hx : x ≠ w := hne x (.head _)
    have hrest : ∀ z ∈ xs, z ≠ w := fun z hz => hne z (.tail _ hz)
    .trans (.cons x (schedPerm_bubble_front w xs ys hrest)) (.swap hx (xs ++ ys))

private def extractAllWave (w : Nat) : List Nat → List Nat × List Nat
  | [] => ([], [])
  | x :: xs =>
    let (ws, rest) := extractAllWave w xs
    if x = w then (w :: ws, rest) else (ws, x :: rest)

private theorem schedPerm_extractAllWave (w : Nat) :
    ∀ s : List Nat,
      SchedPerm s ((extractAllWave w s).1 ++ (extractAllWave w s).2)
  | [] => .refl []
  | x :: xs => by
    dsimp only [extractAllWave]
    by_cases hxw : x = w
    · subst hxw
      simp only [↓reduceIte, List.cons_append]
      exact .cons x (schedPerm_extractAllWave x xs)
    · simp only [hxw, ↓reduceIte]
      have hPermTail := schedPerm_extractAllWave w xs
      -- `x :: (ws ++ rest) ~ ws ++ (x :: rest)` since every element of `ws` equals `w ≠ x`
      have hAllW : ∀ z ∈ (extractAllWave w xs).1, z = w := by
        clear hPermTail hxw
        induction xs with
        | nil => intro _ h; cases h
        | cons y ys ih =>
          dsimp only [extractAllWave]
          split
          · intro z hz; rcases List.mem_cons.mp hz with rfl | hm
            · rfl
            · exact ih z hm
          · exact ih
      have hPushX : ∀ (ws rest : List Nat), (∀ z ∈ ws, z = w) →
          SchedPerm (x :: ws ++ rest) (ws ++ x :: rest) := by
        intro ws rest hws
        induction ws with
        | nil => exact .refl _
        | cons z ws ih =>
          have hzw : z = w := hws z (.head _)
          cases hzw
          exact .trans (.swap hxw (ws ++ rest))
            (.cons w (ih (fun u hu => hws u (.tail _ hu))))
      exact .trans (.cons x hPermTail) (hPushX _ _ hAllW)

private theorem extractAllWave_fst_eq_replicate (w : Nat) :
    ∀ s : List Nat, (extractAllWave w s).1 = List.replicate (s.count w) w
  | [] => rfl
  | x :: xs => by
    dsimp only [extractAllWave]
    by_cases hxw : x = w
    · subst hxw
      simp [List.count_cons_self, List.replicate_succ, extractAllWave_fst_eq_replicate x xs]
    · simp [hxw, extractAllWave_fst_eq_replicate w xs]

private theorem extractAllWave_snd_count (w u : Nat) :
    ∀ s : List Nat, ((extractAllWave w s).2).count u = if u = w then 0 else s.count u
  | [] => by simp [extractAllWave]
  | x :: xs => by
    dsimp only [extractAllWave]
    by_cases hxw : x = w
    · subst hxw
      simp only [↓reduceIte, extractAllWave_snd_count x u xs]
      by_cases hux : u = x
      · subst hux; simp
      · have hne : (x == u) = false := beq_false_of_ne (Ne.symm hux)
        simp [hux, List.count_cons, hne]
    · simp only [hxw, ↓reduceIte, List.count_cons, extractAllWave_snd_count w u xs]
      by_cases hux : u = w
      · subst hux
        have hne : (x == u) = false := beq_false_of_ne hxw
        simp [hne]
      · simp [hux]

private theorem extractAllWave_snd_mem {w z : Nat} :
    ∀ {s : List Nat}, z ∈ (extractAllWave w s).2 → z ∈ s ∧ z ≠ w
  | [], h => by cases h
  | x :: xs, h => by
    dsimp only [extractAllWave] at h
    by_cases hxw : x = w
    · simp only [hxw, ↓reduceIte] at h
      obtain ⟨hm, hne⟩ := extractAllWave_snd_mem h
      exact ⟨.tail _ hm, hne⟩
    · simp only [hxw, ↓reduceIte, List.mem_cons] at h
      rcases h with rfl | hm
      · exact ⟨.head _, hxw⟩
      · obtain ⟨hm', hne⟩ := extractAllWave_snd_mem hm
        exact ⟨.tail _ hm', hne⟩

/-- Any two schedules `s₁, s₂` bounded by `< bound` with identical per-wave step counts (`count w`)
    are `SchedPerm`-equivalent! -/
theorem schedPerm_of_same_counts :
    ∀ (bound : Nat) {s₁ s₂ : List Nat},
      (∀ w ∈ s₁, w < bound) →
      (∀ w ∈ s₂, w < bound) →
      (∀ w < bound, s₁.count w = s₂.count w) →
      SchedPerm s₁ s₂
  | 0, s₁, s₂, h₁, h₂, _ => by
    cases s₁ with
    | nil =>
      cases s₂ with
      | nil => exact .refl []
      | cons y _ => exact absurd (h₂ y (.head _)) (by omega)
    | cons x _ => exact absurd (h₁ x (.head _)) (by omega)
  | b + 1, s₁, s₂, h₁, h₂, hCnt => by
    have p₁ := schedPerm_extractAllWave b s₁
    have p₂ := schedPerm_extractAllWave b s₂
    rw [extractAllWave_fst_eq_replicate b s₁] at p₁
    rw [extractAllWave_fst_eq_replicate b s₂, ← hCnt b (by omega)] at p₂
    have hSub₁ : ∀ w ∈ (extractAllWave b s₁).2, w < b := by
      intro w hw
      obtain ⟨hm, hne⟩ := extractAllWave_snd_mem hw
      have hlt := h₁ w hm
      omega
    have hSub₂ : ∀ w ∈ (extractAllWave b s₂).2, w < b := by
      intro w hw
      obtain ⟨hm, hne⟩ := extractAllWave_snd_mem hw
      have hlt := h₂ w hm
      omega
    have hSubCnt : ∀ w < b, ((extractAllWave b s₁).2).count w = ((extractAllWave b s₂).2).count w := by
      intro w hw
      have hne : w ≠ b := by omega
      rw [extractAllWave_snd_count b w s₁, extractAllWave_snd_count b w s₂]
      simp [hne, hCnt w (by omega)]
    have ih := schedPerm_of_same_counts b hSub₁ hSub₂ hSubCnt
    have hPrepend : ∀ (k : Nat) {u v : List Nat}, SchedPerm u v →
        SchedPerm (List.replicate k b ++ u) (List.replicate k b ++ v) := by
      intro k u v huv
      induction k with
      | zero => simpa using huv
      | succ k ihk => exact .cons b ihk
    have hSymm : ∀ {u v : List Nat}, SchedPerm u v → SchedPerm v u := by
      intro u v huv
      induction huv with
      | refl s => exact .refl s
      | swap hne rest => exact .swap hne.symm rest
      | cons w _ ihs => exact .cons w ihs
      | trans _ _ iha ihb => exact .trans ihb iha
    exact .trans p₁ (.trans (hPrepend (s₁.count b) ih) (hSymm p₂))

/-! ### `#tooth` Witnesses for Cross-Wave Synchronization & Persistent Shared `64 KiB` LDS -/

/-- Minimal 2-wave (`64`-thread = `2 × Wave32`) SPIR-V module environment for cross-wave LDS tree
    reduction:
    - `%1` : `LocalInvocationId` (`0 .. 63`)
    - `%2` : `Workgroup` LDS pointer (`u32[]`)
    - `%3` : `StorageBuffer` binding `0` (`u32[]` input)
    - `%4` : `StorageBuffer` binding `1` (`u32[]` output)
    - `%5` : constant `32 : u32` (cross-wave stride: Wave 0 reads `tid + 32` written by Wave 1!)
    - `%6` : pointer type `Workgroup u32*`
    - `%7` : pointer type `StorageBuffer u32*`
    - `%8` : `u32` type -/
def twoWaveReductionEnv : SpirvModuleEnv where
  intWidths id := if id == 8 then some .w32 else none
  ptrInfo id :=
    if id == 2 || id == 6 || id == 12 || id == 13 || id == 16 then some (.workgroup, 0, .w32)
    else if id == 3 || id == 7 || id == 10 then some (.storageBuffer, 0, .w32)
    else if id == 4 || id == 19 then some (.storageBuffer, 1, .w32)
    else none
  initConst id := if id == 5 then .vU32 32 else .vUndef
  builtIns id := if id == 1 then some .localInvocationId else none

def twoWavePhase0WriteLds : List SpirvInst :=
  [ -- %10 = &inBuf[tid]; %11 = inBuf[tid]; %12 = &lds[tid]; lds[tid] = %11
    .opAccessChain 7 10 3 [1],
    .opLoad 8 11 10,
    .opAccessChain 6 12 2 [1],
    .opStore 12 11
  ]

def twoWavePhase1CrossWaveRead : List SpirvInst :=
  [ -- %13 = &lds[tid]; %14 = lds[tid]; %15 = (tid + 32) & 63? Wait: (tid ^ 32) pairs Wave 0 <-> Wave 1!
    .opAccessChain 6 13 2 [1],
    .opLoad 8 14 13,
    .opBitwiseXor 8 15 1 5,
    .opAccessChain 6 16 2 [15],
    .opLoad 8 17 16,
    .opIAdd 8 18 14 17,
    .opAccessChain 7 19 4 [1],
    .opStore 19 18
  ]

def twoWaveCfg : WorkgroupConfig :=
  { workgroupId := 0, numWaves := 2, wavesPos := by decide, workgroupCount := 1 }

/-- Project a single `StorageBuffer` dword out of an execution result (`Option UInt32` has `DecidableEq`). -/
def peekSsboDword (binding addr : Nat) (res : Except SimtExecError WorkgroupExecState) : Option UInt32 :=
  match res with
  | .ok s => some (s.mem.ssbo binding addr)
  | .error _ => none

/-- **`#tooth` Missing `OpControlBarrier` Causes Cross-Wave Shared-LDS Data Race
    (`tooth_missing_barrier_causes_cross_wave_lds_race`)**:
    In a 2-wave (`64`-thread) workgroup where Wave `0` and Wave `1` exchange values via `lds[tid ^ 32]`:
    1. **Without `OpControlBarrier`** (concatenating `Phase0 ++ Phase1` into a single epoch), running
       Wave `0` to completion before Wave `1` (`schedWave0First`) vs running both waves through
       `Phase0` before `Phase1` (`schedPhased`) yields **distinct global outputs** (`10 ≠ 52`)!
    2. **With `OpControlBarrier(.workgroup, .workgroup, spirvSemWorkgroupAcqRel)`** separating
       `Phase0` and `Phase1`, Wave `0` blocks at the barrier until Wave `1` finishes `Phase0`, so
       putting Wave `0` first in the schedule STILL produces the **exact cross-wave sum `52`**! -/
theorem tooth_missing_barrier_causes_cross_wave_lds_race :
    let initMem : GpuMemState :=
      { lds := fun _ => 0
        ssbo := fun b idx => if b == 0 then (if idx < 32 then 10 else 42) else 0
        pushConsts := fun _ => 0 }
    let buggyNoBarrierProg := twoWavePhase0WriteLds ++ twoWavePhase1CrossWaveRead
    let schedWave0First := List.replicate 12 0 ++ List.replicate 12 1
    let schedInterleaved := List.replicate 4 0 ++ List.replicate 4 1 ++
                            List.replicate 8 0 ++ List.replicate 8 1
    let initSt := initWorkgroupExecState twoWaveReductionEnv twoWaveCfg initMem
    -- 1. Without OpControlBarrier, two valid 12-step-per-wave schedules disagree on outBuf[0]:
    peekSsboDword 1 0
      (runInterleavedSchedule twoWaveReductionEnv twoWaveCfg buggyNoBarrierProg schedWave0First initSt) = some 10 ∧
    peekSsboDword 1 0
      (runInterleavedSchedule twoWaveReductionEnv twoWaveCfg buggyNoBarrierProg schedInterleaved initSt) = some 52 ∧
    peekSsboDword 1 0
      (runInterleavedSchedule twoWaveReductionEnv twoWaveCfg buggyNoBarrierProg schedWave0First initSt) ≠
    peekSsboDword 1 0
      (runInterleavedSchedule twoWaveReductionEnv twoWaveCfg buggyNoBarrierProg schedInterleaved initSt) ∧
    -- 2. With OpControlBarrier separating the two epochs, Wave-0-first schedule produces 52 on both waves:
    peekSsboDword 1 0
      (runMultiWaveEpochs twoWaveReductionEnv twoWaveCfg
        [twoWavePhase0WriteLds, twoWavePhase1CrossWaveRead]
        [List.replicate 5 0 ++ List.replicate 5 1, List.replicate 8 0 ++ List.replicate 8 1]
        initSt) = some 52 ∧
    peekSsboDword 1 32
      (runMultiWaveEpochs twoWaveReductionEnv twoWaveCfg
        [twoWavePhase0WriteLds, twoWavePhase1CrossWaveRead]
        [List.replicate 5 0 ++ List.replicate 5 1, List.replicate 8 0 ++ List.replicate 8 1]
        initSt) = some 52 := by
  dsimp only
  decide

/-- **`#tooth` Single-Wave Wiped-LDS Execution Corrupts Multi-Wave Barrier Reductions
    (`tooth_single_wave_lds_wipe_corrupts_multiwave_reduction`)**:
    Wiping `lds := fun _ => 0` between waves (as in broken 1-wave-per-workgroup simulators) loses
    Wave `0`'s shared-memory writes before Wave `1` runs (`42 ≠ 52`), whereas persistent multi-wave
    `Workgroup` LDS preserves `52` across both Wave32 subgroups. -/
theorem tooth_single_wave_lds_wipe_corrupts_multiwave_reduction :
    let initMem : GpuMemState :=
      { lds := fun _ => 0
        ssbo := fun b idx => if b == 0 then (if idx < 32 then 10 else 42) else 0
        pushConsts := fun _ => 0 }
    let initSt := initWorkgroupExecState twoWaveReductionEnv twoWaveCfg initMem
    let wipedWave1Prog := twoWavePhase0WriteLds ++ twoWavePhase1CrossWaveRead
    peekSsboDword 1 32
      (runMultiWaveEpochs twoWaveReductionEnv twoWaveCfg
        [twoWavePhase0WriteLds, twoWavePhase1CrossWaveRead]
        [canonicalEpochSchedule 2 5, canonicalEpochSchedule 2 8] initSt) = some 52 ∧
    peekSsboDword 1 32
      (runInterleavedSchedule twoWaveReductionEnv twoWaveCfg wipedWave1Prog
        (List.replicate 12 1) initSt) = some 42 ∧
    peekSsboDword 1 32
      (runMultiWaveEpochs twoWaveReductionEnv twoWaveCfg
        [twoWavePhase0WriteLds, twoWavePhase1CrossWaveRead]
        [canonicalEpochSchedule 2 5, canonicalEpochSchedule 2 8] initSt) ≠
    peekSsboDword 1 32
      (runInterleavedSchedule twoWaveReductionEnv twoWaveCfg wipedWave1Prog
        (List.replicate 12 1) initSt) := by
  dsimp only
  decide

/-! ### `SIMT-CT` Constant-Time Side-Channel Model & 32-Bank RDNA2 LDS Conflict Freedom -/

/-- RDNA2 `64 KiB` LDS physical bank index (`32` banks × `4`-byte dwords):
    `ldsBank(byteAddr) = (byteAddr / 4) % 32`. -/
def ldsBank (byteAddr : Nat) : Nat :=
  (byteAddr / 4) % 32

/-- **`LdsBankConflictFree32`**: across all 32 lanes `lane ∈ [0, 32)` of a Wave32 subgroup,
    `ldsBank ∘ byteAddrFn` is injective (`32` lanes map to `32` distinct LDS banks -> `0` bank
    serialization!). -/
def LdsBankConflictFree32 (byteAddrFn : Nat → Nat) : Prop :=
  ∀ l₁ l₂ : Nat, l₁ < wave32Lanes → l₂ < wave32Lanes →
    ldsBank (byteAddrFn l₁) = ldsBank (byteAddrFn l₂) → l₁ = l₂

/-- Count how many lanes `l < 32` collide with lane `0` in the same LDS bank at distinct byte
    addresses (`1` = conflict-free; `32` = worst-case 32-way bank serialization). -/
def ldsLane0BankWays (byteAddrFn : Nat → Nat) : Nat :=
  ((List.range 32).filter fun l =>
    decide (ldsBank (byteAddrFn l) = ldsBank (byteAddrFn 0))).length

private theorem pow_two_dvd_of_odd :
    ∀ (k g c : Nat), c % 2 = 1 → 2 ^ k ∣ g * c → 2 ^ k ∣ g
  | 0, g, _, _, _ => Nat.one_dvd g
  | k + 1, g, c, hodd, hdvd => by
    have h2prime : IsPrimeNat 2 := ⟨by decide, fun d hd => by
      have hpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by decide)
      have hle : d ≤ 2 := Nat.le_of_dvd (by decide) hd
      omega⟩
    have hnc : ¬ (2 ∣ c) := fun hc => by obtain ⟨t, rfl⟩ := hc; omega
    have h2dvd : 2 ∣ g * c := by
      rw [Nat.pow_succ] at hdvd
      exact Nat.dvd_trans (Nat.dvd_mul_left 2 (2 ^ k)) hdvd
    obtain ⟨g', rfl⟩ := h2prime.dvd_mul (Nat.mul_comm g c ▸ h2dvd) hnc
    have hk : 2 ^ k ∣ g' * c := by
      obtain ⟨u, hu⟩ := hdvd
      refine ⟨u, ?_⟩
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2] at hu
      have hAssoc : 2 * (g' * c) = 2 * (2 ^ k * u) := by
        calc 2 * (g' * c) = 2 * g' * c := (Nat.mul_assoc 2 g' c).symm
        _ = 2 * 2 ^ k * u := hu
        _ = 2 * (2 ^ k * u) := Nat.mul_assoc 2 (2 ^ k) u
      exact (Nat.mul_right_inj (by decide : 2 ≠ 0)).mp hAssoc
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2]
    exact Nat.mul_dvd_mul_left 2 (pow_two_dvd_of_odd k g' c hodd hk)

private theorem odd_mul_sub_not_dvd_32 {s d : Nat} (hOdd : s % 2 = 1) (hdPos : 0 < d) (hdLt : d < 32) :
    (s * d) % 32 ≠ 0 := by
  intro hMod0
  have hdvd : 2 ^ 5 ∣ d * s := by
    rw [Nat.mul_comm]
    exact Nat.dvd_of_mod_eq_zero hMod0
  have hd32 : 32 ∣ d := pow_two_dvd_of_odd 5 d s hOdd hdvd
  have hle := Nat.le_of_dvd hdPos hd32
  omega

/-- **Universal Odd-Stride Wave32 LDS Bank-Conflict-Free Theorem (`odd_stride_lds_bank_conflict_free`)**:
    For **every** base dword offset `baseDword` and **every** odd dword stride `stride` (`stride % 2 = 1`,
    including unit stride `1`, `+1`-padded 32×32 transpose stride `33`, and `+1`-padded Poseidon2
    width-12 stride `13`), `byteAddr(lane) = 4 * (baseDword + stride * lane)` hits `32` pairwise
    distinct LDS banks across every Wave32 subgroup (`0` bank conflicts)! -/
theorem odd_stride_lds_bank_conflict_free (baseDword stride : Nat) (hOdd : stride % 2 = 1) :
    LdsBankConflictFree32 (fun lane => 4 * (baseDword + stride * lane)) := by
  intro l₁ l₂ hl₁ hl₂ hBank
  unfold wave32Lanes at hl₁ hl₂
  unfold ldsBank at hBank
  have hDiv1 : 4 * (baseDword + stride * l₁) / 4 = baseDword + stride * l₁ := by omega
  have hDiv2 : 4 * (baseDword + stride * l₂) / 4 = baseDword + stride * l₂ := by omega
  rw [hDiv1, hDiv2] at hBank
  by_cases hEq : l₁ = l₂
  · exact hEq
  · by_cases hlt : l₁ < l₂
    · have hdPos : 0 < l₂ - l₁ := by omega
      have hdLt : l₂ - l₁ < 32 := by omega
      have hDiff : baseDword + stride * l₂ = (baseDword + stride * l₁) + stride * (l₂ - l₁) := by
        rw [Nat.mul_sub_left_distrib]
        have hle : stride * l₁ ≤ stride * l₂ := Nat.mul_le_mul_left stride (by omega)
        omega
      have hMod0 : (stride * (l₂ - l₁)) % 32 = 0 := by
        have h1 := Nat.div_add_mod (baseDword + stride * l₁) 32
        have h2 := Nat.div_add_mod (baseDword + stride * l₂) 32
        have h3 := Nat.div_add_mod (stride * (l₂ - l₁)) 32
        omega
      exact False.elim (odd_mul_sub_not_dvd_32 hOdd hdPos hdLt hMod0)
    · have hgt : l₂ < l₁ := by omega
      have hdPos : 0 < l₁ - l₂ := by omega
      have hdLt : l₁ - l₂ < 32 := by omega
      have hDiff : baseDword + stride * l₁ = (baseDword + stride * l₂) + stride * (l₁ - l₂) := by
        rw [Nat.mul_sub_left_distrib]
        have hle : stride * l₂ ≤ stride * l₁ := Nat.mul_le_mul_left stride (by omega)
        omega
      have hMod0 : (stride * (l₁ - l₂)) % 32 = 0 := by
        have h1 := Nat.div_add_mod (baseDword + stride * l₁) 32
        have h2 := Nat.div_add_mod (baseDword + stride * l₂) 32
        have h3 := Nat.div_add_mod (stride * (l₁ - l₂)) 32
        omega
      exact False.elim (odd_mul_sub_not_dvd_32 hOdd hdPos hdLt hMod0)

/-- Bank-skewed shared-LDS dword offset for 2-level multi-wave Wave32 Merkle tree nodes (`8` dwords =
    `4 × u64` per node): `merkleSkewedLdsDword idx = 9 * idx + idx / 32`. -/
def merkleSkewedLdsDword (idx : Nat) : Nat :=
  9 * idx + idx / 32

theorem merkleSkewedLdsDword_slots_disjoint {i₁ i₂ d₁ d₂ : Nat}
    (hd₁ : d₁ < 8) (hd₂ : d₂ < 8) (hne : i₁ ≠ i₂) :
    merkleSkewedLdsDword i₁ + d₁ ≠ merkleSkewedLdsDword i₂ + d₂ := by
  unfold merkleSkewedLdsDword
  by_cases hlt : i₁ < i₂
  · have hDiv : i₁ / 32 ≤ i₂ / 32 := Nat.div_le_div_right (by omega)
    omega
  · have hgt : i₂ < i₁ := by omega
    have hDiv : i₂ / 32 ≤ i₁ / 32 := Nat.div_le_div_right (by omega)
    omega

/-- **2-Epoch Skewed Merkle LDS Bank-Conflict-Free Theorem (`merkle_skewed_lds_bank_conflict_free_both_epochs`)**:
    For **every** wave `w : Nat` and **every** dword sub-offset `d < 8`, `merkleSkewedLdsDword`:
    1. Is **32-bank conflict-free in Epoch 0** (`idx = 32 * w + lane`), AND
    2. Is **32-bank conflict-free in Epoch 1** (`idx = 2 * (32 * w + lane) + childBit` for BOTH
       left child `childBit = 0` and right child `childBit = 1`)! -/
theorem merkle_skewed_lds_bank_conflict_free_both_epochs (w d : Nat) :
    LdsBankConflictFree32 (fun lane => 4 * (merkleSkewedLdsDword (w * 32 + lane) + d)) ∧
    (∀ childBit : Nat, childBit < 2 →
      LdsBankConflictFree32 (fun lane => 4 * (merkleSkewedLdsDword (2 * (w * 32 + lane) + childBit) + d))) := by
  refine ⟨?_, ?_⟩
  · intro l₁ l₂ hl₁ hl₂ hBank
    unfold wave32Lanes at hl₁ hl₂
    dsimp only at hBank
    have hEqFn : ∀ l < 32, 4 * (merkleSkewedLdsDword (w * 32 + l) + d) =
        4 * ((289 * w + d) + 9 * l) := by
      intro l _; unfold merkleSkewedLdsDword
      have hDiv : (w * 32 + l) / 32 = w := by omega
      omega
    rw [hEqFn l₁ hl₁, hEqFn l₂ hl₂] at hBank
    exact odd_stride_lds_bank_conflict_free (289 * w + d) 9 rfl l₁ l₂ hl₁ hl₂ hBank
  · intro c hc l₁ l₂ hl₁ hl₂ hBank
    unfold wave32Lanes at hl₁ hl₂
    unfold ldsBank merkleSkewedLdsDword at hBank
    have h4_1 : 4 * (9 * (2 * (w * 32 + l₁) + c) + (2 * (w * 32 + l₁) + c) / 32 + d) / 4 =
        9 * (2 * (w * 32 + l₁) + c) + (2 * (w * 32 + l₁) + c) / 32 + d := by omega
    have h4_2 : 4 * (9 * (2 * (w * 32 + l₂) + c) + (2 * (w * 32 + l₂) + c) / 32 + d) / 4 =
        9 * (2 * (w * 32 + l₂) + c) + (2 * (w * 32 + l₂) + c) / 32 + d := by omega
    rw [h4_1, h4_2] at hBank
    -- Notice `(2 * (w * 32 + l) + c) / 32 = 2 * w + l / 16` since `c < 2`!
    have hDivL₁ : (2 * (w * 32 + l₁) + c) / 32 = 2 * w + l₁ / 16 := by omega
    have hDivL₂ : (2 * (w * 32 + l₂) + c) / 32 = 2 * w + l₂ / 16 := by omega
    rw [hDivL₁, hDivL₂] at hBank
    -- Now modulo 2, `(18 * l + l / 16)` has parity `l / 16 ∈ {0, 1}`, so `l₁ / 16 = l₂ / 16`!
    -- Once `l₁ / 16 = l₂ / 16`, `18 * l₁ ≡ 18 * l₂ (mod 32)` -> `9 * (l₁ % 16) ≡ 9 * (l₂ % 16) (mod 16)`!
    -- Since `l₁ < 32` and `l₂ < 32` are bounded, `omega` closes the linear/mod-32 case split directly!
    have hq₁ : l₁ / 16 = 0 ∨ l₁ / 16 = 1 := by omega
    have hq₂ : l₂ / 16 = 0 ∨ l₂ / 16 = 1 := by omega
    -- Check parity first: `(A + 18 * l₁ + l₁ / 16) % 2 = (A + 18 * l₂ + l₂ / 16) % 2`
    have hPar : (9 * (2 * (w * 32 + l₁) + c) + (2 * w + l₁ / 16) + d) % 2 =
                (9 * (2 * (w * 32 + l₂) + c) + (2 * w + l₂ / 16) + d) % 2 := by omega
    have hSameHalf : l₁ / 16 = l₂ / 16 := by omega
    rw [hSameHalf] at hBank
    -- Now `(base + 18 * l₁) % 32 = (base + 18 * l₂) % 32` with `|l₁ - l₂| < 16`!
    -- Since `9` is odd, `18 * k % 32 = 0` for `0 ≤ k < 16` implies `k = 0`!
    by_cases hEq : l₁ = l₂
    · exact hEq
    · by_cases hlt : l₁ < l₂
      · have hkLt : l₂ - l₁ < 16 := by omega
        have hMod32 : (18 * (l₂ - l₁)) % 32 = 0 := by
          have d1 := Nat.div_add_mod (9 * (2 * (w * 32 + l₁) + c) + (2 * w + l₂ / 16) + d) 32
          have d2 := Nat.div_add_mod (9 * (2 * (w * 32 + l₂) + c) + (2 * w + l₂ / 16) + d) 32
          have d3 := Nat.div_add_mod (18 * (l₂ - l₁)) 32
          have hSub : 9 * (2 * (w * 32 + l₂) + c) =
              9 * (2 * (w * 32 + l₁) + c) + 18 * (l₂ - l₁) := by
            rw [Nat.mul_sub_left_distrib]
            have : 18 * l₁ ≤ 18 * l₂ := Nat.mul_le_mul_left 18 (by omega)
            omega
          omega
        have hMod32' : (9 * (2 * (l₂ - l₁))) % 32 = 0 := by
          have : 9 * (2 * (l₂ - l₁)) = 18 * (l₂ - l₁) := by omega
          rwa [this]
        exact False.elim (odd_mul_sub_not_dvd_32 (s := 9) (d := 2 * (l₂ - l₁)) rfl (by omega) (by omega) hMod32')
      · have hkLt : l₁ - l₂ < 16 := by omega
        have hMod32 : (18 * (l₁ - l₂)) % 32 = 0 := by
          have d1 := Nat.div_add_mod (9 * (2 * (w * 32 + l₁) + c) + (2 * w + l₂ / 16) + d) 32
          have d2 := Nat.div_add_mod (9 * (2 * (w * 32 + l₂) + c) + (2 * w + l₂ / 16) + d) 32
          have d3 := Nat.div_add_mod (18 * (l₁ - l₂)) 32
          have hSub : 9 * (2 * (w * 32 + l₁) + c) =
              9 * (2 * (w * 32 + l₂) + c) + 18 * (l₁ - l₂) := by
            rw [Nat.mul_sub_left_distrib]
            have : 18 * l₂ ≤ 18 * l₁ := Nat.mul_le_mul_left 18 (by omega)
            omega
          omega
        have hMod32' : (9 * (2 * (l₁ - l₂))) % 32 = 0 := by
          have : 9 * (2 * (l₁ - l₂)) = 18 * (l₁ - l₂) := by omega
          rwa [this]
        exact False.elim (odd_mul_sub_not_dvd_32 (s := 9) (d := 2 * (l₁ - l₂)) rfl (by omega) (by omega) hMod32')

/-- **`#tooth` Unpadded Stride-32 LDS Access Causes Worst-Case 32-Way Bank Serialization
    (`tooth_stride32_lds_causes_32way_bank_conflict`)**:
    Accessing `byteAddr(lane) = 4 * (baseDword + 32 * lane)` across a Wave32 subgroup maps all `32`
    distinct lane addresses into the single LDS bank `baseDword % 32` (`ldsLane0BankWays = 32` and
    `¬ LdsBankConflictFree32`), whereas `+1` row padding (`stride = 33`) achieves `ldsLane0BankWays = 1`
    and `LdsBankConflictFree32`! -/
theorem tooth_stride32_lds_causes_32way_bank_conflict (baseDword : Nat) :
    let unpadded := fun lane => 4 * (baseDword + 32 * lane)
    let padded33 := fun lane => 4 * (baseDword + 33 * lane)
    (∀ lane < 32, ldsBank (unpadded lane) = baseDword % 32) ∧
    ldsLane0BankWays unpadded = 32 ∧
    ¬ LdsBankConflictFree32 unpadded ∧
    LdsBankConflictFree32 padded33 := by
  refine ⟨?_, ?_, ?_, odd_stride_lds_bank_conflict_free baseDword 33 rfl⟩
  · intro lane _
    unfold ldsBank
    have h4 : 4 * (baseDword + 32 * lane) / 4 = baseDword + 32 * lane := by omega
    rw [h4]
    omega
  · unfold ldsLane0BankWays
    have hAll : ∀ l ∈ List.range 32,
        decide (ldsBank (4 * (baseDword + 32 * l)) = ldsBank (4 * (baseDword + 32 * 0))) = true := by
      intro l _
      unfold ldsBank
      have h1 : 4 * (baseDword + 32 * l) / 4 = baseDword + 32 * l := by omega
      have h2 : 4 * (baseDword + 32 * 0) / 4 = baseDword := by omega
      rw [h1, h2]
      simp [Nat.add_mul_mod_self_left]
    rw [List.filter_eq_self.mpr hAll, List.length_range]
  · intro hFree
    have h01 := hFree 0 1 (by decide) (by decide) (by
      unfold ldsBank
      have h1 : 4 * (baseDword + 32 * 0) / 4 = baseDword := by omega
      have h2 : 4 * (baseDword + 32 * 1) / 4 = baseDword + 32 := by omega
      rw [h1, h2]; omega)
    omega

/-! ### Static `SIMT-CT` Information-Flow Type System & Leakage-Trace Noninterference -/

/-- Two-point information-flow lattice: `pub` (public dispatch geometry / constants) ≤ `sec` (witness). -/
inductive SecLabel where
  | pub
  | sec
  deriving DecidableEq, Repr

def SecLabel.join : SecLabel → SecLabel → SecLabel
  | .pub, .pub => .pub
  | _, _ => .sec

/-- Hardware side-channel observation emitted by one Wave32 instruction step:
    - `pc` : instruction address
    - `activeMask` : 32-lane `EXEC_LO` active predicate (`List Bool` of length 32)
    - `memTraces` : per-lane memory access descriptor `(storageClass, binding, elemIdx)` (exposes
      both global VMEM coalescing spread AND physical LDS bank `(4 * elemIdx / 4) % 32`!). -/
structure SimtWaveObs where
  pc : Nat
  activeMask : List Bool
  memTraces : List (Option (SpirvStorageClass × Nat × Nat))
  deriving DecidableEq, Repr

def observeLaneMem (regs : Nat → SpirvVal) : SpirvInst → Option (SpirvStorageClass × Nat × Nat)
  | .opLoad _ _ ptrId | .opStore ptrId _ =>
    match regs ptrId.toNat with
    | .vPtr sc binding elemIdx _ => some (sc, binding, elemIdx)
    | _ => none
  | _ => none

def stepWaveObs (wSt : Wave32State) (inst : SpirvInst) : SimtWaveObs :=
  { pc := wSt.pc
    activeMask := (List.range wave32Lanes).map wSt.execMask
    memTraces := (List.range wave32Lanes).map fun lane =>
      if wSt.execMask lane then observeLaneMem (wSt.laneRegs lane) inst else none }

/-- Collect the complete Wave32 hardware side-channel observation trace across a straight-line
    epoch `prog` starting from `(wSt, mem)`. -/
def runWaveWithObs (env : SpirvModuleEnv) (prog : List SpirvInst) :
    Nat → Wave32State → GpuMemState → List SimtWaveObs
  | 0, _, _ => []
  | fuel + 1, wSt, mem =>
    if wSt.atBarrier then []
    else
      match prog[wSt.pc]? with
      | none => []
      | some inst =>
        let obs := stepWaveObs wSt inst
        match stepWave32One env prog wSt mem with
        | .error _ => [obs]
        | .ok (wSt', mem') => obs :: runWaveWithObs env prog fuel wSt' mem'

/-- Static `SIMT-CT` typing environment:
    - `ssboSec binding` classifies each `StorageBuffer` as `pub` or `sec`
    - `ldsSec` classifies `Workgroup` LDS contents (`sec` when holding witness intermediates!)
    - `regSec ssaId` assigns a `SecLabel` to every SSA `%id` (`pub` values must match across
      all public-equivalent memories!). -/
structure SimtCtPolicy where
  ssboSec : Nat → SecLabel
  ldsSec : SecLabel
  regSec : Nat → SecLabel

/-- Static `SIMT-CT` instruction checker:
    1. Zero `EXEC`-mask divergence: no branches (`opBranchConditional`, `opBranch`) inside straight-line
       epochs; conditional selection uses branchless `OpSelect` (`v_cndmask_b32`)!
    2. Public-affine addressing: every `OpAccessChain` index `%idx` is `pub`, and every pointer
       register `%ptr` is `pub` (so `OpLoad` / `OpStore` addresses never depend on secrets!).
    3. Monotone label propagation on all fixed-latency VALU operations (`OpUMulExtended`, `OpIAdd`,
       `OpISub`, `OpIMul`, `OpBitwise*`, `OpShift*`, `OpSelect`, comparisons). -/
def checkInstSimtCt (pol : SimtCtPolicy) : SpirvInst → Bool
  | .opAccessChain _ resId baseId [idxId] =>
    (pol.regSec baseId.toNat == .pub) &&
    (pol.regSec idxId.toNat == .pub) &&
    (pol.regSec resId.toNat == .pub)
  | .opAccessChain _ _ _ _ => false
  | .opLoad _ _ ptrId =>
    pol.regSec ptrId.toNat == .pub
  | .opStore ptrId _ =>
    pol.regSec ptrId.toNat == .pub
  | .opCompositeExtract _ resId compId _ =>
    (pol.regSec resId.toNat == .sec) || (pol.regSec compId.toNat == .pub)
  | .opUConvert _ resId valId
  | .opNot _ resId valId
  | .opLogicalNot _ resId valId =>
    (pol.regSec resId.toNat == .sec) || (pol.regSec valId.toNat == .pub)
  | .opIAdd _ resId aId bId
  | .opISub _ resId aId bId
  | .opIMul _ resId aId bId
  | .opUMulExtended _ resId aId bId
  | .opLogicalOr _ resId aId bId
  | .opLogicalAnd _ resId aId bId
  | .opIEqual _ resId aId bId
  | .opINotEqual _ resId aId bId
  | .opUGreaterThan _ resId aId bId
  | .opUGreaterThanEqual _ resId aId bId
  | .opULessThan _ resId aId bId
  | .opULessThanEqual _ resId aId bId
  | .opShiftRightLogical _ resId aId bId
  | .opShiftLeftLogical _ resId aId bId
  | .opBitwiseXor _ resId aId bId
  | .opBitwiseOr _ resId aId bId
  | .opBitwiseAnd _ resId aId bId =>
    (pol.regSec resId.toNat == .sec) ||
    ((pol.regSec aId.toNat == .pub) && (pol.regSec bId.toNat == .pub))
  | .opSelect _ resId cId tId fId =>
    (pol.regSec resId.toNat == .sec) ||
    ((pol.regSec cId.toNat == .pub) && (pol.regSec tId.toNat == .pub) && (pol.regSec fId.toNat == .pub))
  | .opControlBarrier es ms sem =>
    (es == SpirvScope.workgroup.toWord) &&
    (ms == SpirvScope.workgroup.toWord) &&
    (sem == spirvSemWorkgroupAcqRel)
  | .opLabel _ => true
  | _ => false

/-- Strict `SIMT-CT` check refining `OpLoad`, `OpStore`, and `OpAccessChain` label soundness:
    - `OpLoad` into a `pub` register requires a `pub` source memory space;
    - `OpStore` of a `sec` register requires a `sec` target memory space (no `sec -> pub` flow);
    - `OpAccessChain` requires `pub` base pointer and `pub` index with consistent pointer metadata. -/
def checkInstSimtCtStrict (env : SpirvModuleEnv) (pol : SimtCtPolicy) (inst : SpirvInst) : Bool :=
  match inst with
  | .opLoad _ resId ptrId =>
    (pol.regSec ptrId.toNat == .pub) &&
    (match pol.regSec resId.toNat with
     | .sec => true
     | .pub =>
       match env.ptrInfo ptrId.toNat with
       | some (.pushConstant, _, _) => true
       | some (.storageBuffer, b, _) => pol.ssboSec b == .pub
       | some (.workgroup, _, _) => pol.ldsSec == .pub
       | _ => false)
  | .opStore ptrId valId =>
    (pol.regSec ptrId.toNat == .pub) &&
    (match pol.regSec valId.toNat with
     | .pub => true
     | .sec =>
       match env.ptrInfo ptrId.toNat with
       | some (.storageBuffer, b, _) => pol.ssboSec b == .sec
       | some (.workgroup, _, _) => pol.ldsSec == .sec
       | _ => false)
  | .opAccessChain tyId resId baseId [idxId] =>
    (pol.regSec baseId.toNat == .pub) &&
    (pol.regSec idxId.toNat == .pub) &&
    (pol.regSec resId.toNat == .pub) &&
    (match env.ptrInfo baseId.toNat, env.ptrInfo resId.toNat, env.ptrInfo tyId.toNat with
     | some (sc1, b1, w1), some (sc2, b2, w2), some (sc3, b3, w3) =>
       decide (sc1 = sc2 ∧ b1 = b2 ∧ w1 = w2 ∧ sc1 = sc3 ∧ b1 = b3 ∧ w1 = w3)
     | _, _, _ => false)
  | .opAccessChain _ _ _ _ => false
  | .opControlBarrier es ms sem => isWorkgroupAcqRelBarrier env es ms sem
  | other => checkInstSimtCt pol other

def checkProgSimtCt (env : SpirvModuleEnv) (pol : SimtCtPolicy) (prog : List SpirvInst) : Bool :=
  prog.all (checkInstSimtCtStrict env pol)

/-- Two `SpirvVal`s have matching runtime tag/width shape (`vU32` vs `vU32`, `vU64` vs `vU64`, etc.)
    so secret data differences never induce type-error divergence! -/
def SpirvVal.SameShape : SpirvVal → SpirvVal → Prop
  | .vUndef, .vUndef => True
  | .vBool _, .vBool _ => True
  | .vU32 _, .vU32 _ => True
  | .vU64 _, .vU64 _ => True
  | .vPair32 _ _, .vPair32 _ _ => True
  | .vPair64 _ _, .vPair64 _ _ => True
  | .vPtr sc1 b1 i1 w1, .vPtr sc2 b2 i2 w2 => sc1 = sc2 ∧ b1 = b2 ∧ i1 = i2 ∧ w1 = w2
  | _, _ => False

theorem SpirvVal.sameShape_refl (v : SpirvVal) : SpirvVal.SameShape v v := by
  cases v <;> simp [SpirvVal.SameShape]

/-- Static consistency of scalar constants in `SpirvModuleEnv` (constants are scalar, never raw pointers). -/
def ScalarConstEnv (env : SpirvModuleEnv) : Prop :=
  ∀ id sc b off w, env.initConst id ≠ .vPtr sc b off w

/-- Low-equivalence (`pub`-indistinguishability) of memories and Wave32 states under `pol`. -/
def MemLowEq (pol : SimtCtPolicy) (m₁ m₂ : GpuMemState) : Prop :=
  m₁.pushConsts = m₂.pushConsts ∧
  (pol.ldsSec = .pub → m₁.lds = m₂.lds) ∧
  (∀ b : Nat, pol.ssboSec b = .pub → m₁.ssbo b = m₂.ssbo b)

def LaneRegsLowEq (env : SpirvModuleEnv) (pol : SimtCtPolicy) (r₁ r₂ : Nat → SpirvVal) : Prop :=
  (∀ id : Nat, SpirvVal.SameShape (r₁ id) (r₂ id)) ∧
  (∀ id : Nat, pol.regSec id = .pub → r₁ id = r₂ id) ∧
  (∀ id sc b off w, r₁ id = .vPtr sc b off w →
    pol.regSec id = .pub → env.ptrInfo id = some (sc, b, w))

def WaveLowEq (env : SpirvModuleEnv) (pol : SimtCtPolicy) (w₁ w₂ : Wave32State) : Prop :=
  w₁.pc = w₂.pc ∧
  w₁.atBarrier = w₂.atBarrier ∧
  w₁.execMask = w₂.execMask ∧
  (∀ lane < wave32Lanes, LaneRegsLowEq env pol (w₁.laneRegs lane) (w₂.laneRegs lane))

theorem initWave_lowEq (env : SpirvModuleEnv) (pol : SimtCtPolicy) (cfg : WorkgroupConfig)
    (hScalar : ScalarConstEnv env) :
    ∀ w : Nat,
      let wSt : Wave32State :=
        { pc := 0, execMask := allActive32, laneRegs := fun l => initLaneRegs env cfg w l, atBarrier := false }
      WaveLowEq env pol wSt wSt := by
  intro w
  refine ⟨rfl, rfl, rfl, fun lane _ => ⟨fun _ => SpirvVal.sameShape_refl _, fun _ _ => rfl, ?_⟩⟩
  intro id sc b off width hEq _
  dsimp only [initLaneRegs] at hEq
  cases hb : env.builtIns id with
  | some bi => rw [hb] at hEq; cases bi <;> cases hEq
  | none =>
    rw [hb] at hEq
    cases hp : env.ptrInfo id with
    | some info =>
      rw [hp] at hEq
      rcases info with ⟨sc', b', w'⟩
      cases hEq
      rfl
    | none =>
      rw [hp] at hEq
      exact False.elim (hScalar id sc b off width hEq)

private theorem writeFn_laneRegsLowEq {env : SpirvModuleEnv} {pol : SimtCtPolicy}
    {r₁ r₂ : Nat → SpirvVal} (hLow : LaneRegsLowEq env pol r₁ r₂)
    (dst : Nat) {v₁ v₂ : SpirvVal}
    (hShape : SpirvVal.SameShape v₁ v₂)
    (hPubEq : pol.regSec dst = .pub → v₁ = v₂)
    (hPtr : ∀ sc b off w, v₁ = .vPtr sc b off w → pol.regSec dst = .pub →
      env.ptrInfo dst = some (sc, b, w)) :
    LaneRegsLowEq env pol (writeFn r₁ dst v₁) (writeFn r₂ dst v₂) := by
  refine ⟨?_, ?_, ?_⟩
  · intro id
    unfold writeFn
    by_cases hid : id = dst
    · subst hid; simpa using hShape
    · simp [hid]; exact hLow.1 id
  · intro id hPub
    unfold writeFn
    by_cases hid : id = dst
    · subst hid; simp [hPubEq hPub]
    · simp [hid, hLow.2.1 id hPub]
  · intro id sc b off w hEq hPub
    unfold writeFn at hEq
    by_cases hid : id = dst
    · subst hid
      simp only [↓reduceIte] at hEq
      exact hPtr sc b off w hEq hPub
    · simp only [hid, ↓reduceIte] at hEq
      exact hLow.2.2 id sc b off w hEq hPub

private theorem evalBinU32U64_lowEq {env : SpirvModuleEnv} {pol : SimtCtPolicy}
    {r₁ r₂ : Nat → SpirvVal} (resId aId bId : UInt32)
    (f32 : UInt32 → UInt32 → SpirvVal) (f64 : UInt64 → UInt64 → SpirvVal)
    (hSh32 : ∀ x₁ y₁ x₂ y₂, SpirvVal.SameShape (f32 x₁ y₁) (f32 x₂ y₂))
    (hNoPtr32 : ∀ x y sc b o w, f32 x y ≠ .vPtr sc b o w)
    (hSh64 : ∀ x₁ y₁ x₂ y₂, SpirvVal.SameShape (f64 x₁ y₁) (f64 x₂ y₂))
    (hNoPtr64 : ∀ x y sc b o w, f64 x y ≠ .vPtr sc b o w)
    (hRegs : LaneRegsLowEq env pol r₁ r₂)
    (hCt : ((pol.regSec resId.toNat == .sec) ||
            ((pol.regSec aId.toNat == .pub) && (pol.regSec bId.toNat == .pub))) = true) :
    match (match r₁ aId.toNat, r₁ bId.toNat with
           | .vU32 a, .vU32 b => Except.ok (resId.toNat, f32 a b)
           | .vU64 a, .vU64 b => Except.ok (resId.toNat, f64 a b)
           | _, _ => Except.error SimtExecError.typeMismatch),
          (match r₂ aId.toNat, r₂ bId.toNat with
           | .vU32 a, .vU32 b => Except.ok (resId.toNat, f32 a b)
           | .vU64 a, .vU64 b => Except.ok (resId.toNat, f64 a b)
           | _, _ => Except.error SimtExecError.typeMismatch) with
    | .error e₁, .error e₂ => e₁ = e₂
    | .ok (d₁, v₁), .ok (d₂, v₂) =>
      d₁ = d₂ ∧
      SpirvVal.SameShape v₁ v₂ ∧
      (pol.regSec d₁ = .pub → v₁ = v₂) ∧
      (∀ sc b off w, v₁ = .vPtr sc b off w → pol.regSec d₁ = .pub →
        env.ptrInfo d₁ = some (sc, b, w))
    | _, _ => False := by
  have hShA := hRegs.1 aId.toNat
  have hShB := hRegs.1 bId.toNat
  have hPubOps : pol.regSec resId.toNat = .pub → r₁ aId.toNat = r₂ aId.toNat ∧ r₁ bId.toNat = r₂ bId.toNat := by
    intro hPub
    rw [hPub] at hCt
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hCt
    rcases hCt with hBad | ⟨ha, hb⟩
    · cases hBad
    · exact ⟨hRegs.2.1 _ ha, hRegs.2.1 _ hb⟩
  cases ha1 : r₁ aId.toNat <;> cases ha2 : r₂ aId.toNat <;>
    (rw [ha1, ha2] at hShA; try cases hShA) <;>
  cases hb1 : r₁ bId.toNat <;> cases hb2 : r₂ bId.toNat <;>
    (rw [hb1, hb2] at hShB; try cases hShB) <;>
  dsimp only
  · refine ⟨rfl, hSh32 _ _ _ _, fun hPub => ?_, fun sc b off w hPtr _ => False.elim (hNoPtr32 _ _ sc b off w hPtr)⟩
    obtain ⟨ea, eb⟩ := hPubOps hPub
    rw [ha1, ha2] at ea; cases ea
    rw [hb1, hb2] at eb; cases eb
    rfl
  · refine ⟨rfl, hSh64 _ _ _ _, fun hPub => ?_, fun sc b off w hPtr _ => False.elim (hNoPtr64 _ _ sc b off w hPtr)⟩
    obtain ⟨ea, eb⟩ := hPubOps hPub
    rw [ha1, ha2] at ea; cases ea
    rw [hb1, hb2] at eb; cases eb
    rfl
  all_goals rfl

private theorem evalLanePureInst_lowEq {env : SpirvModuleEnv} {pol : SimtCtPolicy}
    {m₁ m₂ : GpuMemState} {r₁ r₂ : Nat → SpirvVal} {inst : SpirvInst}
    (hMem : MemLowEq pol m₁ m₂)
    (hRegs : LaneRegsLowEq env pol r₁ r₂)
    (hCt : checkInstSimtCtStrict env pol inst = true)
    (hNotStore : ∀ p v, inst ≠ .opStore p v)
    (hNotBarrier : ∀ es ms sem, inst ≠ .opControlBarrier es ms sem)
    (hNotLabel : ∀ l, inst ≠ .opLabel l) :
    match evalLanePureInst env m₁ r₁ inst, evalLanePureInst env m₂ r₂ inst with
    | .error e₁, .error e₂ => e₁ = e₂
    | .ok (d₁, v₁), .ok (d₂, v₂) =>
      d₁ = d₂ ∧
      SpirvVal.SameShape v₁ v₂ ∧
      (pol.regSec d₁ = .pub → v₁ = v₂) ∧
      (∀ sc b off w, v₁ = .vPtr sc b off w → pol.regSec d₁ = .pub →
        env.ptrInfo d₁ = some (sc, b, w))
    | _, _ => False := by
  cases inst with
  | opExtInst _ _ _ _ _ | opVariable _ _ _ _
  | opFunctionCall _ _ _ _ | opVectorShuffle _ _ _ _ _ | opCompositeConstruct _ _ _
  | opUDiv _ _ _ _ | opUMod _ _ _ _ | opSGreaterThanEqual _ _ _ _ | opBitReverse _ _ _
  | opMemoryBarrier _ _ | opPhi _ _ _
  | opLoopMerge _ _ _ | opSelectionMerge _ _ | opBranch _ | opBranchConditional _ _ _
  | opSwitch _ _ _ | opReturn | opReturnValue _ =>
    simp [checkInstSimtCtStrict, checkInstSimtCt] at hCt
  | opStore p v => exact False.elim (hNotStore p v rfl)
  | opControlBarrier es ms sem => exact False.elim (hNotBarrier es ms sem rfl)
  | opLabel l => exact False.elim (hNotLabel l rfl)
  | opAccessChain tyId resId baseId indices =>
    cases indices with
    | nil => simp [checkInstSimtCtStrict] at hCt
    | cons idxId rest =>
      cases rest with
      | cons _ _ => simp [checkInstSimtCtStrict] at hCt
      | nil =>
        dsimp only [checkInstSimtCtStrict] at hCt
        simp only [Bool.and_eq_true, beq_iff_eq] at hCt
        rcases hCt with ⟨⟨⟨hBasePub, hIdxPub⟩, _⟩, hPtrMeta⟩
        have hBaseEq := hRegs.2.1 baseId.toNat hBasePub
        have hIdxEq := hRegs.2.1 idxId.toNat hIdxPub
        dsimp only [evalLanePureInst]
        rw [← hBaseEq, ← hIdxEq]
        cases hB : r₁ baseId.toNat with
        | vPtr sc binding baseOff elemW =>
          cases hI : r₁ idxId.toNat with
          | vU32 idx =>
            refine ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, fun _ => rfl, ?_⟩
            intro sc' b' off' w' hEq _
            injection hEq with hsc hb _ hw
            subst hsc; subst hb; subst hw
            have hInfoBase := hRegs.2.2 baseId.toNat _ _ _ _ hB hBasePub
            rw [hInfoBase] at hPtrMeta
            cases hResInfo : env.ptrInfo resId.toNat with
            | none => rw [hResInfo] at hPtrMeta; simp at hPtrMeta
            | some p2 =>
              cases hTyInfo : env.ptrInfo tyId.toNat with
              | none => rw [hResInfo, hTyInfo] at hPtrMeta; simp at hPtrMeta
              | some p3 =>
                rw [hResInfo, hTyInfo] at hPtrMeta
                rcases p2 with ⟨sc2, b2, w2⟩
                rcases p3 with ⟨sc3, b3, w3⟩
                simp only [decide_eq_true_eq] at hPtrMeta
                rcases hPtrMeta with ⟨rfl, rfl, rfl, _, _, rfl⟩
                rfl
          | vU64 idx =>
            refine ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, fun _ => rfl, ?_⟩
            intro sc' b' off' w' hEq _
            injection hEq with hsc hb _ hw
            subst hsc; subst hb; subst hw
            have hInfoBase := hRegs.2.2 baseId.toNat _ _ _ _ hB hBasePub
            rw [hInfoBase] at hPtrMeta
            cases hResInfo : env.ptrInfo resId.toNat with
            | none => rw [hResInfo] at hPtrMeta; simp at hPtrMeta
            | some p2 =>
              cases hTyInfo : env.ptrInfo tyId.toNat with
              | none => rw [hResInfo, hTyInfo] at hPtrMeta; simp at hPtrMeta
              | some p3 =>
                rw [hResInfo, hTyInfo] at hPtrMeta
                rcases p2 with ⟨sc2, b2, w2⟩
                rcases p3 with ⟨sc3, b3, w3⟩
                simp only [decide_eq_true_eq] at hPtrMeta
                rcases hPtrMeta with ⟨rfl, rfl, rfl, _, _, rfl⟩
                rfl
          | _ => rfl
        | _ => cases r₁ idxId.toNat <;> rfl
  | opLoad tyId resId ptrId =>
    dsimp only [checkInstSimtCtStrict] at hCt
    simp only [Bool.and_eq_true, beq_iff_eq] at hCt
    rcases hCt with ⟨hPtrPub, hDstChk⟩
    have hPtrEq := hRegs.2.1 ptrId.toNat hPtrPub
    dsimp only [evalLanePureInst]
    rw [← hPtrEq]
    cases hP : r₁ ptrId.toNat with
    | vPtr sc binding elemIdx width =>
      have hInfo := hRegs.2.2 ptrId.toNat sc binding elemIdx width hP hPtrPub
      cases sc with
      | workgroup =>
        cases width with
        | w32 =>
          dsimp only
          by_cases hB : elemIdx < ldsCapacityDwords
          · simp only [hB, ↓reduceIte]
            refine ⟨trivial, trivial, fun hPub => ?_, fun _ _ _ _ h => by cases h⟩
            rw [hPub, hInfo] at hDstChk
            simp only [beq_iff_eq] at hDstChk
            rw [hMem.2.1 hDstChk]
          · simp only [hB, ↓reduceIte]
        | w64 =>
          dsimp only
          by_cases hB : 2 * elemIdx + 1 < ldsCapacityDwords
          · simp only [hB, ↓reduceIte]
            refine ⟨trivial, trivial, fun hPub => ?_, fun _ _ _ _ h => by cases h⟩
            rw [hPub, hInfo] at hDstChk
            simp only [beq_iff_eq] at hDstChk
            rw [hMem.2.1 hDstChk]
          · simp only [hB, ↓reduceIte]
      | storageBuffer =>
        cases width with
        | w32 =>
          dsimp only
          refine ⟨rfl, trivial, fun hPub => ?_, fun _ _ _ _ h => by cases h⟩
          rw [hPub, hInfo] at hDstChk
          simp only [beq_iff_eq] at hDstChk
          rw [hMem.2.2 binding hDstChk]
        | w64 =>
          dsimp only
          refine ⟨rfl, trivial, fun hPub => ?_, fun _ _ _ _ h => by cases h⟩
          rw [hPub, hInfo] at hDstChk
          simp only [beq_iff_eq] at hDstChk
          rw [hMem.2.2 binding hDstChk]
      | pushConstant =>
        cases width with
        | w32 =>
          dsimp only
          refine ⟨rfl, trivial, fun _ => ?_, fun _ _ _ _ h => by cases h⟩
          rw [hMem.1]
        | w64 =>
          dsimp only
          refine ⟨rfl, trivial, fun _ => ?_, fun _ _ _ _ h => by cases h⟩
          rw [hMem.1]
      | input | function =>
        cases width <;> rfl
    | _ => rfl
  | opCompositeExtract tyId resId compId fieldIdx =>
    dsimp only [checkInstSimtCtStrict, checkInstSimtCt] at hCt
    have hSh := hRegs.1 compId.toNat
    dsimp only [evalLanePureInst]
    cases h1 : r₁ compId.toNat <;> cases h2 : r₂ compId.toNat <;>
      (rw [h1, h2] at hSh; try cases hSh)
    · cases hF : fieldIdx.toNat with
      | zero =>
        refine ⟨rfl, trivial, fun hPub => ?_, fun _ _ _ _ h => by cases h⟩
        rw [hPub] at hCt; simp only [Bool.or_eq_true, beq_iff_eq] at hCt
        rcases hCt with hBad | hCompPub
        · cases hBad
        · have hEq := hRegs.2.1 compId.toNat hCompPub; rw [h1, h2] at hEq; cases hEq; rfl
      | succ n =>
        cases n with
        | zero =>
          refine ⟨rfl, trivial, fun hPub => ?_, fun _ _ _ _ h => by cases h⟩
          rw [hPub] at hCt; simp only [Bool.or_eq_true, beq_iff_eq] at hCt
          rcases hCt with hBad | hCompPub
          · cases hBad
          · have hEq := hRegs.2.1 compId.toNat hCompPub; rw [h1, h2] at hEq; cases hEq; rfl
        | succ _ => rfl
    · cases hF : fieldIdx.toNat with
      | zero =>
        refine ⟨rfl, trivial, fun hPub => ?_, fun _ _ _ _ h => by cases h⟩
        rw [hPub] at hCt; simp only [Bool.or_eq_true, beq_iff_eq] at hCt
        rcases hCt with hBad | hCompPub
        · cases hBad
        · have hEq := hRegs.2.1 compId.toNat hCompPub; rw [h1, h2] at hEq; cases hEq; rfl
      | succ n =>
        cases n with
        | zero =>
          refine ⟨rfl, trivial, fun hPub => ?_, fun _ _ _ _ h => by cases h⟩
          rw [hPub] at hCt; simp only [Bool.or_eq_true, beq_iff_eq] at hCt
          rcases hCt with hBad | hCompPub
          · cases hBad
          · have hEq := hRegs.2.1 compId.toNat hCompPub; rw [h1, h2] at hEq; cases hEq; rfl
        | succ _ => rfl
  | opUConvert tyId resId valId =>
    dsimp only [checkInstSimtCtStrict, checkInstSimtCt] at hCt
    have hSh := hRegs.1 valId.toNat
    dsimp only [evalLanePureInst]
    cases hw : env.intWidths tyId.toNat with
    | none => rfl
    | some w =>
      cases w with
      | w32 =>
        cases h1 : r₁ valId.toNat <;> cases h2 : r₂ valId.toNat <;>
          (rw [h1, h2] at hSh; try cases hSh)
        refine ⟨rfl, trivial, fun hPub => ?_, fun _ _ _ _ h => by cases h⟩
        rw [hPub] at hCt; simp only [Bool.or_eq_true, beq_iff_eq] at hCt
        rcases hCt with hBad | hValPub
        · cases hBad
        · have hEq := hRegs.2.1 valId.toNat hValPub; rw [h1, h2] at hEq; cases hEq; rfl
      | w64 =>
        cases h1 : r₁ valId.toNat <;> cases h2 : r₂ valId.toNat <;>
          (rw [h1, h2] at hSh; try cases hSh)
        refine ⟨rfl, trivial, fun hPub => ?_, fun _ _ _ _ h => by cases h⟩
        rw [hPub] at hCt; simp only [Bool.or_eq_true, beq_iff_eq] at hCt
        rcases hCt with hBad | hValPub
        · cases hBad
        · have hEq := hRegs.2.1 valId.toNat hValPub; rw [h1, h2] at hEq; cases hEq; rfl
  | opSelect tyId resId cId tId fId =>
    dsimp only [checkInstSimtCtStrict, checkInstSimtCt] at hCt
    have hShC := hRegs.1 cId.toNat
    have hShT := hRegs.1 tId.toNat
    have hShF := hRegs.1 fId.toNat
    dsimp only [evalLanePureInst]
    cases hc1 : r₁ cId.toNat <;> cases hc2 : r₂ cId.toNat <;>
      (rw [hc1, hc2] at hShC; try cases hShC)
    cases ht1 : r₁ tId.toNat <;> cases ht2 : r₂ tId.toNat <;>
      (rw [ht1, ht2] at hShT; try cases hShT)
    · cases hf1 : r₁ fId.toNat <;> cases hf2 : r₂ fId.toNat <;>
        (rw [hf1, hf2] at hShF; try cases hShF)
      refine ⟨rfl, trivial, fun hPub => ?_, fun _ _ _ _ h => by cases h⟩
      rw [hPub] at hCt; simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hCt
      rcases hCt with hBad | ⟨⟨hCPub, hTPub⟩, hFPub⟩
      · cases hBad
      · have ec := hRegs.2.1 cId.toNat hCPub; rw [hc1, hc2] at ec; cases ec
        have et := hRegs.2.1 tId.toNat hTPub; rw [ht1, ht2] at et; cases et
        have ef := hRegs.2.1 fId.toNat hFPub; rw [hf1, hf2] at ef; cases ef
        rfl
    · cases hf1 : r₁ fId.toNat <;> cases hf2 : r₂ fId.toNat <;>
        (rw [hf1, hf2] at hShF; try cases hShF)
      refine ⟨rfl, trivial, fun hPub => ?_, fun _ _ _ _ h => by cases h⟩
      rw [hPub] at hCt; simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hCt
      rcases hCt with hBad | ⟨⟨hCPub, hTPub⟩, hFPub⟩
      · cases hBad
      · have ec := hRegs.2.1 cId.toNat hCPub; rw [hc1, hc2] at ec; cases ec
        have et := hRegs.2.1 tId.toNat hTPub; rw [ht1, ht2] at et; cases et
        have ef := hRegs.2.1 fId.toNat hFPub; rw [hf1, hf2] at ef; cases ef
        rfl
  | opIAdd _ resId aId bId =>
    exact evalBinU32U64_lowEq resId aId bId _ _
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h) hRegs hCt
  | opISub _ resId aId bId =>
    exact evalBinU32U64_lowEq resId aId bId _ _
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h) hRegs hCt
  | opIMul _ resId aId bId =>
    exact evalBinU32U64_lowEq resId aId bId _ _
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h) hRegs hCt
  | opUMulExtended _ resId aId bId =>
    exact evalBinU32U64_lowEq resId aId bId _ _
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h) hRegs hCt
  | opIEqual _ resId aId bId =>
    exact evalBinU32U64_lowEq resId aId bId _ _
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h) hRegs hCt
  | opINotEqual _ resId aId bId =>
    exact evalBinU32U64_lowEq resId aId bId _ _
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h) hRegs hCt
  | opUGreaterThan _ resId aId bId =>
    exact evalBinU32U64_lowEq resId aId bId _ _
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h) hRegs hCt
  | opUGreaterThanEqual _ resId aId bId =>
    exact evalBinU32U64_lowEq resId aId bId _ _
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h) hRegs hCt
  | opULessThan _ resId aId bId =>
    exact evalBinU32U64_lowEq resId aId bId _ _
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h) hRegs hCt
  | opULessThanEqual _ resId aId bId =>
    exact evalBinU32U64_lowEq resId aId bId _ _
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h) hRegs hCt
  | opLogicalOr _ resId aId bId =>
    dsimp only [checkInstSimtCtStrict, checkInstSimtCt] at hCt
    have hShA := hRegs.1 aId.toNat
    have hShB := hRegs.1 bId.toNat
    dsimp only [evalLanePureInst]
    cases ha1 : r₁ aId.toNat <;> cases ha2 : r₂ aId.toNat <;>
      (rw [ha1, ha2] at hShA; try cases hShA) <;>
    cases hb1 : r₁ bId.toNat <;> cases hb2 : r₂ bId.toNat <;>
      (rw [hb1, hb2] at hShB; try cases hShB) <;>
    dsimp only
    · refine ⟨rfl, trivial, fun hPub => ?_, fun _ _ _ _ h => by cases h⟩
      rw [hPub] at hCt; simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hCt
      rcases hCt with hBad | ⟨ha, hb⟩
      · cases hBad
      · have ea := hRegs.2.1 _ ha; rw [ha1, ha2] at ea; cases ea
        have eb := hRegs.2.1 _ hb; rw [hb1, hb2] at eb; cases eb
        rfl
    all_goals rfl
  | opLogicalAnd _ resId aId bId =>
    dsimp only [checkInstSimtCtStrict, checkInstSimtCt] at hCt
    have hShA := hRegs.1 aId.toNat
    have hShB := hRegs.1 bId.toNat
    dsimp only [evalLanePureInst]
    cases ha1 : r₁ aId.toNat <;> cases ha2 : r₂ aId.toNat <;>
      (rw [ha1, ha2] at hShA; try cases hShA) <;>
    cases hb1 : r₁ bId.toNat <;> cases hb2 : r₂ bId.toNat <;>
      (rw [hb1, hb2] at hShB; try cases hShB) <;>
    dsimp only
    · refine ⟨rfl, trivial, fun hPub => ?_, fun _ _ _ _ h => by cases h⟩
      rw [hPub] at hCt; simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hCt
      rcases hCt with hBad | ⟨ha, hb⟩
      · cases hBad
      · have ea := hRegs.2.1 _ ha; rw [ha1, ha2] at ea; cases ea
        have eb := hRegs.2.1 _ hb; rw [hb1, hb2] at eb; cases eb
        rfl
    all_goals rfl
  | opLogicalNot _ resId aId =>
    dsimp only [checkInstSimtCtStrict, checkInstSimtCt] at hCt
    have hShA := hRegs.1 aId.toNat
    dsimp only [evalLanePureInst]
    cases ha1 : r₁ aId.toNat <;> cases ha2 : r₂ aId.toNat <;>
      (rw [ha1, ha2] at hShA; try cases hShA) <;>
    dsimp only
    · refine ⟨rfl, trivial, fun hPub => ?_, fun _ _ _ _ h => by cases h⟩
      rw [hPub] at hCt; simp only [Bool.or_eq_true, beq_iff_eq] at hCt
      rcases hCt with hBad | ha
      · cases hBad
      · have ea := hRegs.2.1 _ ha; rw [ha1, ha2] at ea; cases ea; rfl
    all_goals rfl
  | opNot _ resId aId =>
    dsimp only [checkInstSimtCtStrict, checkInstSimtCt] at hCt
    have hShA := hRegs.1 aId.toNat
    dsimp only [evalLanePureInst]
    cases ha1 : r₁ aId.toNat <;> cases ha2 : r₂ aId.toNat <;>
      (rw [ha1, ha2] at hShA; try cases hShA) <;>
    dsimp only
    · refine ⟨rfl, trivial, fun hPub => ?_, fun _ _ _ _ h => by cases h⟩
      rw [hPub] at hCt; simp only [Bool.or_eq_true, beq_iff_eq] at hCt
      rcases hCt with hBad | ha
      · cases hBad
      · have ea := hRegs.2.1 _ ha; rw [ha1, ha2] at ea; cases ea; rfl
    · refine ⟨rfl, trivial, fun hPub => ?_, fun _ _ _ _ h => by cases h⟩
      rw [hPub] at hCt; simp only [Bool.or_eq_true, beq_iff_eq] at hCt
      rcases hCt with hBad | ha
      · cases hBad
      · have ea := hRegs.2.1 _ ha; rw [ha1, ha2] at ea; cases ea; rfl
    all_goals rfl
  | opShiftRightLogical _ resId aId bId =>
    exact evalBinU32U64_lowEq resId aId bId _ _
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h) hRegs hCt
  | opShiftLeftLogical _ resId aId bId =>
    exact evalBinU32U64_lowEq resId aId bId _ _
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h) hRegs hCt
  | opBitwiseXor _ resId aId bId =>
    exact evalBinU32U64_lowEq resId aId bId _ _
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h) hRegs hCt
  | opBitwiseOr _ resId aId bId =>
    exact evalBinU32U64_lowEq resId aId bId _ _
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h) hRegs hCt
  | opBitwiseAnd _ resId aId bId =>
    exact evalBinU32U64_lowEq resId aId bId _ _
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h) hRegs hCt

private theorem applyLaneStore_lowEq {env : SpirvModuleEnv} {pol : SimtCtPolicy}
    {m₁ m₂ : GpuMemState} {r₁ r₂ : Nat → SpirvVal} {ptrId valId : UInt32}
    (hMem : MemLowEq pol m₁ m₂)
    (hRegs : LaneRegsLowEq env pol r₁ r₂)
    (hCt : checkInstSimtCtStrict env pol (.opStore ptrId valId) = true) :
    match applyLaneStore m₁ r₁ ptrId valId, applyLaneStore m₂ r₂ ptrId valId with
    | .error e₁, .error e₂ => e₁ = e₂
    | .ok m₁', .ok m₂' => MemLowEq pol m₁' m₂'
    | _, _ => False := by
  dsimp only [checkInstSimtCtStrict] at hCt
  simp only [Bool.and_eq_true, beq_iff_eq] at hCt
  rcases hCt with ⟨hPtrPub, hFlowChk⟩
  have hPtrEq := hRegs.2.1 ptrId.toNat hPtrPub
  have hValSh := hRegs.1 valId.toNat
  dsimp only [applyLaneStore]
  rw [← hPtrEq]
  cases hP : r₁ ptrId.toNat with
  | vPtr sc binding elemIdx width =>
    have hInfo := hRegs.2.2 ptrId.toNat sc binding elemIdx width hP hPtrPub
    cases sc with
    | workgroup =>
      cases width with
      | w32 =>
        cases hv1 : r₁ valId.toNat <;> cases hv2 : r₂ valId.toNat <;>
          (rw [hv1, hv2] at hValSh; try cases hValSh)
        dsimp only
        by_cases hB : elemIdx < ldsCapacityDwords
        · simp only [hB, ↓reduceIte]
          refine ⟨hMem.1, fun hLdsPub => ?_, hMem.2.2⟩
          have hValPub : pol.regSec valId.toNat = .pub := by
            cases hSec : pol.regSec valId.toNat with
            | pub => rfl
            | sec => rw [hSec, hInfo, hLdsPub] at hFlowChk; simp at hFlowChk
          have hvEq := hRegs.2.1 valId.toNat hValPub
          rw [hv1, hv2] at hvEq; cases hvEq
          rw [hMem.2.1 hLdsPub]
        · simp only [hB, ↓reduceIte]
      | w64 =>
        cases hv1 : r₁ valId.toNat <;> cases hv2 : r₂ valId.toNat <;>
          (rw [hv1, hv2] at hValSh; try cases hValSh)
        dsimp only
        by_cases hB : 2 * elemIdx + 1 < ldsCapacityDwords
        · simp only [hB, ↓reduceIte]
          refine ⟨hMem.1, fun hLdsPub => ?_, hMem.2.2⟩
          have hValPub : pol.regSec valId.toNat = .pub := by
            cases hSec : pol.regSec valId.toNat with
            | pub => rfl
            | sec => rw [hSec, hInfo, hLdsPub] at hFlowChk; simp at hFlowChk
          have hvEq := hRegs.2.1 valId.toNat hValPub
          rw [hv1, hv2] at hvEq; cases hvEq
          rw [hMem.2.1 hLdsPub]
        · simp only [hB, ↓reduceIte]
    | storageBuffer =>
      cases width with
      | w32 =>
        cases hv1 : r₁ valId.toNat <;> cases hv2 : r₂ valId.toNat <;>
          (rw [hv1, hv2] at hValSh; try cases hValSh)
        dsimp only
        refine ⟨hMem.1, hMem.2.1, fun b' hb' => ?_⟩
        by_cases hbb : b' = binding
        · subst hbb
          have hValPub : pol.regSec valId.toNat = .pub := by
            cases hSec : pol.regSec valId.toNat with
            | pub => rfl
            | sec => rw [hSec, hInfo] at hFlowChk; dsimp only at hFlowChk; rw [hb'] at hFlowChk; cases hFlowChk
          have hvEq := hRegs.2.1 valId.toNat hValPub
          rw [hv1, hv2] at hvEq; cases hvEq
          funext k
          simp [writeSsboDword, hMem.2.2 b' hb']
        · funext k
          simp [writeSsboDword, hbb, hMem.2.2 b' hb']
      | w64 =>
        cases hv1 : r₁ valId.toNat <;> cases hv2 : r₂ valId.toNat <;>
          (rw [hv1, hv2] at hValSh; try cases hValSh)
        dsimp only
        refine ⟨hMem.1, hMem.2.1, fun b' hb' => ?_⟩
        by_cases hbb : b' = binding
        · subst hbb
          have hValPub : pol.regSec valId.toNat = .pub := by
            cases hSec : pol.regSec valId.toNat with
            | pub => rfl
            | sec => rw [hSec, hInfo] at hFlowChk; dsimp only at hFlowChk; rw [hb'] at hFlowChk; cases hFlowChk
          have hvEq := hRegs.2.1 valId.toNat hValPub
          rw [hv1, hv2] at hvEq; cases hvEq
          funext k
          simp [writeSsboU64, writeSsboDword, hMem.2.2 b' hb']
        · funext k
          simp [writeSsboU64, writeSsboDword, hbb, hMem.2.2 b' hb']
    | input | function | pushConstant =>
      cases width <;> cases r₁ valId.toNat <;> cases r₂ valId.toNat <;> rfl
  | _ =>
    cases r₁ valId.toNat <;> cases r₂ valId.toNat <;> rfl

private theorem execWaveStoreLanes_lowEq {env : SpirvModuleEnv} {pol : SimtCtPolicy}
    {execMask : Nat → Bool} {lr₁ lr₂ : Nat → Nat → SpirvVal} {ptrId valId : UInt32}
    (hRegs : ∀ lane < wave32Lanes, LaneRegsLowEq env pol (lr₁ lane) (lr₂ lane))
    (hCt : checkInstSimtCtStrict env pol (.opStore ptrId valId) = true) :
    ∀ (k : Nat) (_hk : k ≤ wave32Lanes) {m₁ m₂ : GpuMemState} (_hMem : MemLowEq pol m₁ m₂),
      match execWaveStoreLanes execMask lr₁ ptrId valId k m₁,
            execWaveStoreLanes execMask lr₂ ptrId valId k m₂ with
      | .error e₁, .error e₂ => e₁ = e₂
      | .ok m₁', .ok m₂' => MemLowEq pol m₁' m₂'
      | _, _ => False
  | 0, _, _, _, hMem => hMem
  | k + 1, hk, m₁, m₂, hMem => by
    have ih := execWaveStoreLanes_lowEq (execMask := execMask) hRegs hCt k (by omega) hMem
    dsimp only [execWaveStoreLanes]
    cases h1 : execWaveStoreLanes execMask lr₁ ptrId valId k m₁ with
    | error e₁ =>
      cases h2 : execWaveStoreLanes execMask lr₂ ptrId valId k m₂ with
      | error e₂ => rw [h1, h2] at ih; exact ih
      | ok _ => rw [h1, h2] at ih; cases ih
    | ok m₁' =>
      cases h2 : execWaveStoreLanes execMask lr₂ ptrId valId k m₂ with
      | error _ => rw [h1, h2] at ih; cases ih
      | ok m₂' =>
        rw [h1, h2] at ih
        by_cases hAct : execMask k = true
        · simp only [hAct, ↓reduceIte]
          exact applyLaneStore_lowEq ih (hRegs k (by omega)) hCt
        · simp [hAct]; exact ih

private theorem checkWavePureLanesErr_eq {env : SpirvModuleEnv} {pol : SimtCtPolicy}
    {m₁ m₂ : GpuMemState} (execMask : Nat → Bool) {lr₁ lr₂ : Nat → Nat → SpirvVal} {inst : SpirvInst}
    (hMem : MemLowEq pol m₁ m₂)
    (hRegs : ∀ lane < wave32Lanes, LaneRegsLowEq env pol (lr₁ lane) (lr₂ lane))
    (hCt : checkInstSimtCtStrict env pol inst = true)
    (hNotStore : ∀ p v, inst ≠ .opStore p v)
    (hNotBarrier : ∀ es ms sem, inst ≠ .opControlBarrier es ms sem)
    (hNotLabel : ∀ l, inst ≠ .opLabel l) :
    ∀ (k : Nat) (_hk : k ≤ wave32Lanes),
      checkWavePureLanesErr env m₁ execMask lr₁ inst k =
      checkWavePureLanesErr env m₂ execMask lr₂ inst k ∧
      (checkWavePureLanesErr env m₁ execMask lr₁ inst k = none →
        ∀ l < k, execMask l = true →
          ∃ d₁ v₁ d₂ v₂,
            evalLanePureInst env m₁ (lr₁ l) inst = .ok (d₁, v₁) ∧
            evalLanePureInst env m₂ (lr₂ l) inst = .ok (d₂, v₂))
  | 0, _ => ⟨rfl, fun _ _ hl => absurd hl (by omega)⟩
  | k + 1, hk => by
    obtain ⟨ihEq, ihOk⟩ := checkWavePureLanesErr_eq execMask hMem hRegs hCt hNotStore hNotBarrier hNotLabel k (by omega)
    dsimp only [checkWavePureLanesErr]
    rw [ihEq]
    cases hPrev : checkWavePureLanesErr env m₂ execMask lr₂ inst k with
    | some e => exact ⟨rfl, fun h => by cases h⟩
    | none =>
      dsimp only
      by_cases hAct : execMask k = true
      · simp only [hAct, ↓reduceIte]
        have hLane := evalLanePureInst_lowEq hMem (hRegs k (by omega)) hCt hNotStore hNotBarrier hNotLabel
        cases e1 : evalLanePureInst env m₁ (lr₁ k) inst with
        | error err₁ =>
          cases e2 : evalLanePureInst env m₂ (lr₂ k) inst with
          | error err₂ =>
            rw [e1, e2] at hLane
            exact ⟨congrArg some hLane, fun h => by cases h⟩
          | ok _ => rw [e1, e2] at hLane; cases hLane
        | ok dv₁ =>
          cases e2 : evalLanePureInst env m₂ (lr₂ k) inst with
          | error _ => rw [e1, e2] at hLane; cases hLane
          | ok dv₂ =>
            refine ⟨rfl, fun _ l hl hActL => ?_⟩
            by_cases hlk : l = k
            · subst hlk
              rcases dv₁ with ⟨d₁, v₁⟩
              rcases dv₂ with ⟨d₂, v₂⟩
              exact ⟨d₁, v₁, d₂, v₂, e1, e2⟩
            · exact ihOk (ihEq.trans hPrev) l (by omega) hActL
      · simp only [hAct, Bool.false_eq_true, ↓reduceIte]
        refine ⟨trivial, fun _ l hl hActL => ?_⟩
        have hlk : l ≠ k := fun h => hAct (h ▸ hActL)
        exact ihOk (ihEq.trans hPrev) l (by omega) hActL

private theorem evalWavePureLanes_lowEq {env : SpirvModuleEnv} {pol : SimtCtPolicy}
    {m₁ m₂ : GpuMemState} (execMask : Nat → Bool) {lr₁ lr₂ : Nat → Nat → SpirvVal} {inst : SpirvInst}
    (hMem : MemLowEq pol m₁ m₂)
    (hRegs : ∀ lane < wave32Lanes, LaneRegsLowEq env pol (lr₁ lane) (lr₂ lane))
    (hCt : checkInstSimtCtStrict env pol inst = true)
    (hNotStore : ∀ p v, inst ≠ .opStore p v)
    (hNotBarrier : ∀ es ms sem, inst ≠ .opControlBarrier es ms sem)
    (hNotLabel : ∀ l, inst ≠ .opLabel l) :
    match evalWavePureLanes env m₁ execMask lr₁ inst wave32Lanes,
          evalWavePureLanes env m₂ execMask lr₂ inst wave32Lanes with
    | .error e₁, .error e₂ => e₁ = e₂
    | .ok r₁', .ok r₂' => ∀ lane < wave32Lanes, LaneRegsLowEq env pol (r₁' lane) (r₂' lane)
    | _, _ => False := by
  obtain ⟨hErrEq, hAllOk⟩ := checkWavePureLanesErr_eq execMask hMem hRegs hCt
    hNotStore hNotBarrier hNotLabel wave32Lanes (Nat.le_refl _)
  unfold evalWavePureLanes
  cases hErr1 : checkWavePureLanesErr env m₁ execMask lr₁ inst wave32Lanes with
  | some e₁ =>
    rw [hErr1] at hErrEq
    rw [← hErrEq]
  | none =>
    have hErr2 : checkWavePureLanesErr env m₂ execMask lr₂ inst wave32Lanes = none :=
      hErrEq.symm.trans hErr1
    rw [hErr2]
    dsimp only
    intro lane hlt
    unfold stepLanePureRegs
    by_cases hAct : execMask lane = true
    · simp only [hlt, hAct, and_self, ↓reduceIte]
      obtain ⟨d₁, v₁, d₂, v₂, e1, e2⟩ := hAllOk hErr1 lane hlt hAct
      have hLane := evalLanePureInst_lowEq hMem (hRegs lane hlt) hCt hNotStore hNotBarrier hNotLabel
      rw [e1, e2] at hLane ⊢
      rcases hLane with ⟨rfl, hShape, hPubEq, hPtr⟩
      exact writeFn_laneRegsLowEq (hRegs lane hlt) d₁ hShape hPubEq hPtr
    · simp [hAct]; exact hRegs lane hlt

private theorem stepWaveObs_eq_of_lowEq {env : SpirvModuleEnv} {pol : SimtCtPolicy}
    {w₁ w₂ : Wave32State} {inst : SpirvInst}
    (hWave : WaveLowEq env pol w₁ w₂)
    (hCt : checkInstSimtCtStrict env pol inst = true) :
    stepWaveObs w₁ inst = stepWaveObs w₂ inst := by
  unfold stepWaveObs
  rcases hWave with ⟨hpc, _, hMask, hLanes⟩
  rw [hpc, hMask]
  congr 1
  apply List.map_congr_left
  intro lane hMemRange
  have hlt : lane < wave32Lanes := List.mem_range.mp hMemRange
  by_cases hAct : w₂.execMask lane = true
  · simp only [hAct, ↓reduceIte]
    cases inst with
    | opLoad _ _ ptrId =>
      unfold checkInstSimtCtStrict at hCt
      simp only [Bool.and_eq_true, beq_iff_eq] at hCt
      have hEq := (hLanes lane hlt).2.1 ptrId.toNat hCt.1
      simp [observeLaneMem, hEq]
    | opStore ptrId _ =>
      unfold checkInstSimtCtStrict at hCt
      simp only [Bool.and_eq_true, beq_iff_eq] at hCt
      have hEq := (hLanes lane hlt).2.1 ptrId.toNat hCt.1
      simp [observeLaneMem, hEq]
    | _ => rfl
  · simp [hAct]

private theorem stepWave32One_lowEq {env : SpirvModuleEnv} {pol : SimtCtPolicy}
    {prog : List SpirvInst} {w₁ w₂ : Wave32State} {m₁ m₂ : GpuMemState}
    (hProgCt : checkProgSimtCt env pol prog = true)
    (hWave : WaveLowEq env pol w₁ w₂)
    (hMem : MemLowEq pol m₁ m₂) :
    match stepWave32One env prog w₁ m₁, stepWave32One env prog w₂ m₂ with
    | .error e₁, .error e₂ => e₁ = e₂
    | .ok (w₁', m₁'), .ok (w₂', m₂') => WaveLowEq env pol w₁' w₂' ∧ MemLowEq pol m₁' m₂'
    | _, _ => False := by
  unfold stepWave32One
  have ⟨hpc, hBar, hMask, hLanes⟩ := hWave
  rw [hBar]
  by_cases hb : w₂.atBarrier = true
  · simp [hb]; exact ⟨hWave, hMem⟩
  · simp only [hb, Bool.false_eq_true, ↓reduceIte, hpc]
    cases hGet : prog[w₂.pc]? with
    | none => exact ⟨hWave, hMem⟩
    | some inst =>
      have hInstMem : inst ∈ prog := List.mem_of_getElem? hGet
      have hInstCt : checkInstSimtCtStrict env pol inst = true := by
        unfold checkProgSimtCt at hProgCt
        exact List.all_eq_true.mp hProgCt inst hInstMem
      cases inst with
      | opExtInst _ _ _ _ _ | opVariable _ _ _ _
      | opFunctionCall _ _ _ _ | opVectorShuffle _ _ _ _ _ | opCompositeConstruct _ _ _
      | opUDiv _ _ _ _ | opUMod _ _ _ _ | opSGreaterThanEqual _ _ _ _ | opBitReverse _ _ _
      | opMemoryBarrier _ _ | opPhi _ _ _
      | opLoopMerge _ _ _ | opSelectionMerge _ _ | opBranch _ | opBranchConditional _ _ _
      | opSwitch _ _ _ | opReturn | opReturnValue _ =>
        simp [checkInstSimtCtStrict, checkInstSimtCt] at hInstCt
      | opControlBarrier es ms sem =>
        dsimp only
        by_cases hBarOk : isWorkgroupAcqRelBarrier env es ms sem = true
        · simp only [hBarOk, ↓reduceIte]
          exact ⟨⟨rfl, rfl, hMask, hLanes⟩, hMem⟩
        · simp only [hBarOk, Bool.false_eq_true, ↓reduceIte]
      | opStore ptrId valId =>
        dsimp only
        rw [hMask]
        have hSt := execWaveStoreLanes_lowEq (execMask := w₂.execMask) hLanes hInstCt wave32Lanes (Nat.le_refl _) hMem
        cases s1 : execWaveStoreLanes w₂.execMask w₁.laneRegs ptrId valId wave32Lanes m₁ with
        | error e₁ =>
          cases s2 : execWaveStoreLanes w₂.execMask w₂.laneRegs ptrId valId wave32Lanes m₂ with
          | error e₂ => rw [s1, s2] at hSt; exact hSt
          | ok _ => rw [s1, s2] at hSt; cases hSt
        | ok m₁' =>
          cases s2 : execWaveStoreLanes w₂.execMask w₂.laneRegs ptrId valId wave32Lanes m₂ with
          | error _ => rw [s1, s2] at hSt; cases hSt
          | ok m₂' =>
            rw [s1, s2] at hSt
            dsimp only
            exact ⟨⟨rfl, rfl, rfl, hLanes⟩, hSt⟩
      | opLabel lbl =>
        dsimp only
        exact ⟨⟨rfl, rfl, hMask, hLanes⟩, hMem⟩
      | opLoad _ _ _ | opAccessChain _ _ _ _ | opCompositeExtract _ _ _ _ | opUConvert _ _ _
      | opIAdd _ _ _ _ | opISub _ _ _ _ | opIMul _ _ _ _ | opUMulExtended _ _ _ _
      | opLogicalOr _ _ _ _ | opLogicalAnd _ _ _ _ | opLogicalNot _ _ _
      | opSelect _ _ _ _ _ | opIEqual _ _ _ _ | opINotEqual _ _ _ _
      | opUGreaterThan _ _ _ _ | opUGreaterThanEqual _ _ _ _
      | opULessThan _ _ _ _ | opULessThanEqual _ _ _ _
      | opShiftRightLogical _ _ _ _ | opShiftLeftLogical _ _ _ _
      | opBitwiseXor _ _ _ _ | opBitwiseOr _ _ _ _ | opBitwiseAnd _ _ _ _ | opNot _ _ _ =>
        dsimp only
        rw [hMask]
        have hPure := evalWavePureLanes_lowEq w₂.execMask hMem hLanes hInstCt
          (by intro _ _ h; cases h) (by intro _ _ _ h; cases h) (by intro _ h; cases h)
        cases p1 : evalWavePureLanes env m₁ w₂.execMask w₁.laneRegs _ wave32Lanes with
        | error e₁ =>
          cases p2 : evalWavePureLanes env m₂ w₂.execMask w₂.laneRegs _ wave32Lanes with
          | error e₂ => rw [p1, p2] at hPure; exact hPure
          | ok _ => rw [p1, p2] at hPure; cases hPure
        | ok r₁' =>
          cases p2 : evalWavePureLanes env m₂ w₂.execMask w₂.laneRegs _ wave32Lanes with
          | error _ => rw [p1, p2] at hPure; cases hPure
          | ok r₂' =>
            rw [p1, p2] at hPure
            dsimp only
            exact ⟨⟨rfl, rfl, rfl, hPure⟩, hMem⟩

/-- **`SIMT-CT` Hardware Leakage-Trace Noninterference Theorem (`simt_ct_noninterference`)**:
    For every SPIR-V compute epoch `prog` passing `checkProgSimtCt env pol prog = true`,
    any two Wave32 executions starting from public-equivalent registers (`WaveLowEq`) and
    public-equivalent memories (`MemLowEq` — differing arbitrarily on secret `StorageBuffer`
    witnesses and secret `Workgroup` LDS!) emit **identical hardware side-channel observation
    traces** (`PC` trajectory, 32-lane `EXEC` active masks, global coalescing addresses, AND
    physical 32-bank LDS access patterns)! -/
theorem simt_ct_noninterference {env : SpirvModuleEnv} {pol : SimtCtPolicy}
    {prog : List SpirvInst} (hProgCt : checkProgSimtCt env pol prog = true) :
    ∀ (fuel : Nat) {w₁ w₂ : Wave32State} {m₁ m₂ : GpuMemState},
      WaveLowEq env pol w₁ w₂ →
      MemLowEq pol m₁ m₂ →
      runWaveWithObs env prog fuel w₁ m₁ = runWaveWithObs env prog fuel w₂ m₂
  | 0, _, _, _, _, _, _ => rfl
  | fuel + 1, w₁, w₂, m₁, m₂, hWave, hMem => by
    unfold runWaveWithObs
    have ⟨hpc, hBar, _, _⟩ := hWave
    rw [hBar]
    by_cases hb : w₂.atBarrier = true
    · simp [hb]
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      cases hGet₁ : prog[w₁.pc]? with
      | none =>
        have hGet₂ : prog[w₂.pc]? = none := by rwa [← hpc]
        simp [hGet₂]
      | some inst =>
        have hGet₂ : prog[w₂.pc]? = some inst := by rwa [← hpc]
        simp only [hGet₂]
        have hInstCt : checkInstSimtCtStrict env pol inst = true :=
          List.all_eq_true.mp hProgCt inst (List.mem_of_getElem? hGet₁)
        have hObsEq := stepWaveObs_eq_of_lowEq hWave hInstCt
        have hStep := stepWave32One_lowEq hProgCt hWave hMem
        rw [hObsEq]
        cases s1 : stepWave32One env prog w₁ m₁ with
        | error _ =>
          cases s2 : stepWave32One env prog w₂ m₂ with
          | error _ => rfl
          | ok _ => rw [s1, s2] at hStep; cases hStep
        | ok wm₁ =>
          cases s2 : stepWave32One env prog w₂ m₂ with
          | error _ => rw [s1, s2] at hStep; cases hStep
          | ok wm₂ =>
            rw [s1, s2] at hStep
            rcases wm₁ with ⟨w₁', m₁'⟩
            rcases wm₂ with ⟨w₂', m₂'⟩
            dsimp only
            rw [simt_ct_noninterference hProgCt fuel hStep.1 hStep.2]

/-- **Zero `EXEC`-Mask Divergence Theorem (`simt_ct_zero_exec_divergence`)**:
    Starting with all 32 Wave32 lanes active (`wSt.execMask = allActive32`), every observation
    emitted during a `SIMT-CT` epoch has `obs.activeMask = List.replicate 32 true` (`0` divergent
    lanes across the entire kernel execution). -/
theorem simt_ct_zero_exec_divergence (env : SpirvModuleEnv) (prog : List SpirvInst) :
    ∀ (fuel : Nat) (wSt : Wave32State) (mem : GpuMemState),
      wSt.execMask = allActive32 →
      ∀ obs ∈ runWaveWithObs env prog fuel wSt mem,
        obs.activeMask = List.replicate 32 true := by
  have hAllTrue : (List.range wave32Lanes).map allActive32 = List.replicate 32 true := by decide
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ hMem; cases hMem
  | succ fuel ih =>
    intro wSt mem hMask obs hIn
    unfold runWaveWithObs at hIn
    by_cases hb : wSt.atBarrier = true
    · simp [hb] at hIn
    · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hIn
      cases hGet : prog[wSt.pc]? with
      | none => rw [hGet] at hIn; cases hIn
      | some inst =>
        rw [hGet] at hIn
        have hHeadMask : (stepWaveObs wSt inst).activeMask = List.replicate 32 true := by
          unfold stepWaveObs; rw [hMask, hAllTrue]
        cases hStep : stepWave32One env prog wSt mem with
        | error _ =>
          rw [hStep] at hIn
          rcases List.mem_singleton.mp hIn with rfl
          exact hHeadMask
        | ok wm =>
          rw [hStep] at hIn
          rcases wm with ⟨wSt', mem'⟩
          rcases List.mem_cons.mp hIn with rfl | hTail
          · exact hHeadMask
          · have hMaskPres : wSt'.execMask = allActive32 := by
              unfold stepWave32One at hStep
              simp only [hb, Bool.false_eq_true, ↓reduceIte, hGet] at hStep
              cases inst with
              | opControlBarrier es ms sem =>
                dsimp only at hStep
                by_cases hBarOk : isWorkgroupAcqRelBarrier env es ms sem = true
                · simp only [hBarOk, ↓reduceIte] at hStep
                  injection hStep with hPair; injection hPair with hWEq _; rw [← hWEq, hMask]
                · simp only [hBarOk, Bool.false_eq_true, ↓reduceIte] at hStep; cases hStep
              | opStore ptrId valId =>
                dsimp only at hStep
                cases hE : execWaveStoreLanes wSt.execMask wSt.laneRegs ptrId valId wave32Lanes mem with
                | error _ => rw [hE] at hStep; cases hStep
                | ok _ =>
                  rw [hE] at hStep
                  dsimp only at hStep
                  injection hStep with hPair; injection hPair with hWEq _; rw [← hWEq, hMask]
              | opLabel _ =>
                dsimp only at hStep
                injection hStep with hPair; injection hPair with hWEq _; rw [← hWEq, hMask]
              | _ =>
                dsimp only at hStep
                cases hP : evalWavePureLanes env mem wSt.execMask wSt.laneRegs _ wave32Lanes with
                | error _ => rw [hP] at hStep; cases hStep
                | ok _ =>
                  rw [hP] at hStep
                  dsimp only at hStep
                  injection hStep with hPair; injection hPair with hWEq _; rw [← hWEq, hMask]
            exact ih wSt' mem' hMaskPres obs hTail

/-- **`#tooth` Secret-Dependent LDS Indexing Rejected by `SIMT-CT` & Leaks Physical Bank Trace
    (`tooth_secret_index_leaks_lds_bank_trace`)**:
    A buggy lookup-table S-box kernel that loads `lds[%secWitness]` is rejected by `checkProgSimtCt`
    (`= false`) AND exhibits two `MemLowEq` secret witnesses (`sec = 0` vs `sec = 1` on lane `0`)
    whose Wave32 hardware observation traces differ (`ldsBank 0 = 0 ≠ 1 = ldsBank 4`)! -/
theorem tooth_secret_index_leaks_lds_bank_trace :
    let pol : SimtCtPolicy :=
      { ssboSec := fun b => if b == 0 then .sec else .pub
        ldsSec := .pub
        regSec := fun id => if id == 11 || id == 12 || id == 13 then .sec else .pub }
    let buggyLutProg : List SpirvInst :=
      [ .opAccessChain 7 10 3 [1],   -- %10 = &secIn[tid] (pub ptr)
        .opLoad 8 11 10,             -- %11 = secIn[tid]  (SECRET witness!)
        .opAccessChain 6 12 2 [11],  -- %12 = &lds[%11]   (ILLEGAL secret index!)
        .opLoad 8 13 12 ]            -- %13 = lds[%11]    (SECRET-DEPENDENT LDS BANK!)
    let m₀ : GpuMemState :=
      { lds := fun i => UInt32.ofNat i
        ssbo := fun b i => if b == 0 && i == 0 then 0 else 0
        pushConsts := fun _ => 0 }
    let m₁ : GpuMemState :=
      { lds := fun i => UInt32.ofNat i
        ssbo := fun b i => if b == 0 && i == 0 then 1 else 0
        pushConsts := fun _ => 0 }
    let w₀ := (initWorkgroupExecState twoWaveReductionEnv twoWaveCfg m₀).waves 0
    checkProgSimtCt twoWaveReductionEnv pol buggyLutProg = false ∧
    MemLowEq pol m₀ m₁ ∧
    runWaveWithObs twoWaveReductionEnv buggyLutProg 4 w₀ m₀ ≠
      runWaveWithObs twoWaveReductionEnv buggyLutProg 4 w₀ m₁ := by
  refine ⟨by decide, ⟨rfl, fun _ => rfl, fun b hb => ?_⟩, by decide⟩
  by_cases hb0 : b = 0
  · subst hb0; simp at hb
  · funext i; simp [hb0]

/-- The exact scalar-plane swizzle used by goldilocks_ntt.comp and coset_lde_ext2.comp.
The argument and result are dword offsets; a plane occupies 512 dwords. -/
def productionLdsIndex (i : Nat) : Nat := i ^^^ (((i >>> 5) &&& 1) * 31)

/-- Stage is zero-based (shader s = stage+1); side chooses idx0/idx1. -/
def productionButterflyIndex (stage wave side lane : Nat) : Nat :=
  let lid := 32 * wave + lane
  ((lid >>> stage) <<< (stage+1)) + (lid &&& (2^stage-1)) + side * 2^stage

/-- A left inverse for the bank permutation, computed from the actual address formula. -/
def productionBankInverse (stage wave side bank : Nat) : Nat :=
  ((List.range 32).find? fun lane =>
    productionLdsIndex (productionButterflyIndex stage wave side lane) % 32 == bank).getD 32

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem production_bank_inverse_checked :
    ∀ stage : Fin 9, ∀ wave : Fin 8, ∀ side : Fin 2, ∀ lane : Fin 32,
      productionBankInverse stage wave side
        (productionLdsIndex (productionButterflyIndex stage wave side lane) % 32) = lane.val := by
  decide

/-- Each separately issued scalar-plane butterfly access is conflict-free for all
nine fused NTT stages, eight waves, and both butterfly operands. This does not
claim that a fused hardware instruction touching two planes makes only 32 accesses. -/
theorem production_butterfly_lds_bank_conflict_free (stage : Fin 9) (wave : Fin 8)
    (side : Fin 2) :
    LdsBankConflictFree32 (fun lane =>
      4 * productionLdsIndex (productionButterflyIndex stage wave side lane)) := by
  intro a b ha hb h
  have ha' : a < 32 := ha
  have hb' : b < 32 := hb
  have hbank : productionLdsIndex (productionButterflyIndex stage wave side a) % 32 =
      productionLdsIndex (productionButterflyIndex stage wave side b) % 32 := by
    simpa [ldsBank] using h
  have hi := congrArg (productionBankInverse stage wave side) hbank
  rw [production_bank_inverse_checked stage wave side ⟨a, ha'⟩,
      production_bank_inverse_checked stage wave side ⟨b, hb'⟩] at hi
  exact hi

def ProductionButterflyShape (stage wave side : Nat) : Prop :=
  stage < 9 ∧ wave < 8 ∧ side < 2

theorem production_butterfly_address_inhabited :
    ∃ stage wave side : Nat, ProductionButterflyShape stage wave side :=
  ⟨0, 0, 0, by exact ⟨by decide, by decide, by decide⟩⟩

/-- Omitting the XOR duplicates banks already in the first butterfly stage. -/
theorem tooth_omitted_production_swizzle :
    ¬ LdsBankConflictFree32 (fun lane => 4 * productionButterflyIndex 0 0 0 lane) := by
  intro h
  have he := h 0 16 (by decide) (by decide) (by decide)
  omega

#tooth_pair production_butterfly_lds_bank_conflict_free vs tooth_omitted_production_swizzle

theorem production_butterfly_lds_bank_conflict_free_bounded (stage wave side : Nat)
    (h : ProductionButterflyShape stage wave side) :
    LdsBankConflictFree32 (fun lane =>
      4 * productionLdsIndex (productionButterflyIndex stage wave side lane)) :=
  production_butterfly_lds_bank_conflict_free ⟨stage, h.1⟩ ⟨wave, h.2.1⟩ ⟨side, h.2.2⟩

#verify_inhabited production_butterfly_lds_bank_conflict_free_bounded production_butterfly_address_inhabited

/-- Normative Khronos SPIR-V 1.5/1.6 opcode regressions (`OpBitwiseOr = 197`,
    `OpBitwiseXor = 198`, `OpBitwiseAnd = 199`, `OpIEqual = 170`, `OpUGreaterThanEqual = 174`,
    `OpULessThan = 176`), independent of encoder/decoder roundtripping. -/
theorem spirv_normative_bitwise_and_comparison_decode :
    decodeInstRaw ⟨197, [1, 2, 3, 4]⟩ = .ok (.opBitwiseOr 1 2 3 4) ∧
    decodeInstRaw ⟨198, [1, 2, 3, 4]⟩ = .ok (.opBitwiseXor 1 2 3 4) ∧
    decodeInstRaw ⟨199, [1, 2, 3, 4]⟩ = .ok (.opBitwiseAnd 1 2 3 4) ∧
    decodeInstRaw ⟨170, [1, 2, 3, 4]⟩ = .ok (.opIEqual 1 2 3 4) ∧
    decodeInstRaw ⟨174, [1, 2, 3, 4]⟩ = .ok (.opUGreaterThanEqual 1 2 3 4) ∧
    decodeInstRaw ⟨176, [1, 2, 3, 4]⟩ = .ok (.opULessThan 1 2 3 4) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `#tooth` Swapping Khronos SPIR-V `OpBitwiseOr = 197` and `OpBitwiseXor = 198` is rejected
    both at binary instruction decode AND under per-lane VALU evaluation (`1 ||| 3 = 3 ≠ 2 = 1 ^^^ 3`). -/
theorem tooth_swapped_spirv_or_xor_corrupts_word_and_alu :
    let sampleRegs : Nat → SpirvVal := fun r =>
      if r == 3 then .vU32 1 else if r == 4 then .vU32 3 else .vUndef
    let sampleMem : GpuMemState := { lds := fun _ => 0, ssbo := fun _ _ => 0, pushConsts := fun _ => 0 }
    decodeInstRaw ⟨197, [1, 2, 3, 4]⟩ ≠ .ok (.opBitwiseXor 1 2 3 4) ∧
    decodeInstRaw ⟨198, [1, 2, 3, 4]⟩ ≠ .ok (.opBitwiseOr 1 2 3 4) ∧
    evalLanePureInst twoWaveReductionEnv sampleMem sampleRegs (.opBitwiseOr 8 2 3 4) = .ok (2, .vU32 3) ∧
    evalLanePureInst twoWaveReductionEnv sampleMem sampleRegs (.opBitwiseXor 8 2 3 4) = .ok (2, .vU32 2) ∧
    evalLanePureInst twoWaveReductionEnv sampleMem sampleRegs (.opBitwiseOr 8 2 3 4) ≠
      evalLanePureInst twoWaveReductionEnv sampleMem sampleRegs (.opBitwiseXor 8 2 3 4) := by
  refine ⟨nofun, nofun, rfl, rfl, nofun⟩

theorem tooth_spirv_opcode_197_not_xor :
    decodeInstRaw ⟨197, [1, 2, 3, 4]⟩ ≠ .ok (.opBitwiseXor 1 2 3 4) :=
  nofun

#tooth_pair spirv_normative_bitwise_and_comparison_decode vs tooth_spirv_opcode_197_not_xor

end Qsag
end
