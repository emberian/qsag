module
public import Qsag.Machine.SpirvFixtures
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
public import Qsag.Tactic.Prelude
import Qsag.Tactic.Prelude
public import Qsag.Math.Goldilocks
import Qsag.Math.Goldilocks
public import Qsag.Oracle.Poseidon2
import Qsag.Oracle.Poseidon2
public import Qsag.Protocol.Aggregation.Aggregation
import Qsag.Protocol.Aggregation.Aggregation

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

